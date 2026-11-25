#!/usr/bin/env python3
"""Normalize three source-research packet formats to dependency-graph syntax.

This is a loss-minimizing syntax adapter, not a source or topology review.
It rejects missing data and unresolved packet edges; it never invents a node,
source premise, edge, or completion status. Converted records stay PROPOSED.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from proof_depgraph import Edge, Node, parse_graph

KINDS = {
    "thm": "theorem", "theorem": "theorem", "prop": "proposition",
    "proposition": "proposition", "lemma": "lemma", "cor": "corollary",
    "corollary": "corollary", "claim": "claim", "remark": "claim",
    "def": "definition", "definition": "definition", "display": "display",
    "step": "step", "proof_step": "step", "gap": "step",
    "application": "application", "consumer": "application", "route": "route",
    "external": "external", "assumption": "assumption", "assumed": "assumption",
}
HEADER = re.compile(
    r"^(?:RECORD\s+|NODE_ID\s*:\s*|NODE\s*:\s*|###\s+NODE\s+)"
    r"`?([A-Za-z0-9][A-Za-z0-9._:+/()\[\]-]*)`?\s*(?:\([^)]*\))?\s*$"
)
FIELD = re.compile(r"^([A-Z][A-Z_]*(?:\s*\([^)]*\))?)(?:\s*:\s*|\s+)(.*)$")
NODE_FIELDS = (
    "KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE", "CONTRACT_ID",
    "CONTRACT_VERSION", "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS",
    "SOURCE_CONCLUSION", "CONSTANT_SCOPE", "FROZEN_FILE", "FROZEN_DECL",
    "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256", "TOPOLOGY_STATUS", "EXTRACTOR",
    "REVIEWER", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE",
)
ALIASES = {
    "LABEL": "TITLE", "SRC": "STATEMENT_SOURCE", "SOURCE_RANGE": "STATEMENT_SOURCE",
    "CONTRACT_VERSION": "CONTRACT_VERSION", "VERSION": "CONTRACT_VERSION",
    "HYPOTHESES": "SOURCE_HYPOTHESES", "QUANTIFIERS": "SOURCE_QUANTIFIERS",
    "CONCLUSION": "SOURCE_CONCLUSION", "CONSTANT_SCOPE": "CONSTANT_SCOPE",
    "SOURCE_CONSTANTS": "CONSTANT_SCOPE", "SOURCE_CONSTANT_SCOPE": "CONSTANT_SCOPE",
    "FROZEN_PATH": "FROZEN_FILE", "FROZEN_FILE": "FROZEN_FILE",
    "FROZEN_EXPORT": "FROZEN_DECL", "FROZEN_DECL": "FROZEN_DECL",
}
# Packets use these as no-value prose embellishments, not different fields.
FIELD_QUALIFIERS = {"steps", "various", "statement", "proof"}


class PacketError(ValueError):
    pass


@dataclass
class Chunk:
    identifier: str
    fields: dict[str, str]
    notes: list[str]
    edges: list[tuple[str, str, str, str]]
    # provider, packet USE_SITE, kind, direct-use text


@dataclass
class SourceLocator:
    path: str
    anchor: str
    first: int
    last: int

    def render(self) -> str:
        return f"{self.path}#{self.anchor}@L{self.first}-L{self.last}"


class SourceIndex:
    """Resolve a packet anchor to HTML spans, without confusing citation layers."""

    def __init__(self, root: Path):
        self.root = root
        self.source = root / ".scratch/source"
        self.html_lines = (self.source / "paper.html").read_text().splitlines()
        self.tex_lines = (self.source / "paper-tex.txt").read_text().splitlines()
        self.ids: set[str] = set()
        self.spans: dict[str, SourceLocator] = {}
        self.enclosing: dict[str, str] = {}
        self._scan_html()
        self.canonical: dict[int, list[str]] = {}
        with (self.source / "paper-tex.locators.tsv").open(newline="") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                if not row["html_id"]:
                    continue
                line = int(row["line"])
                # A sidecar line may be the blank opening line of a block.
                content_line = line + 1 if not self.tex_lines[line - 1].strip() else line
                self.canonical.setdefault(line, []).append(row["html_id"])
                self.canonical.setdefault(content_line, []).append(row["html_id"])

    def _scan_html(self) -> None:
        # Scope follows block markup only. Inline <math>, <span>, and <a> IDs
        # frequently identify notation rather than a statement/paragraph.
        blocks = {"div", "li", "figure", "section", "p", "table", "tbody"}
        stack: list[tuple[str, str, int]] = []
        for number, line in enumerate(self.html_lines, 1):
            for match in re.finditer(r"</?([A-Za-z][A-Za-z0-9]*)\b([^>]*)>", line):
                closing, tag, tail = bool(match.group(0).startswith("</")), match.group(1).lower(), match.group(2)
                identifier = re.search(r'\bid="([^"]+)"', tail)
                anchor = identifier.group(1) if identifier else ""
                if anchor:
                    self.ids.add(anchor)
                    for _, enclosing_anchor, _ in reversed(stack):
                        if enclosing_anchor:
                            self.enclosing[anchor] = enclosing_anchor
                            break
                if tag not in blocks:
                    continue
                if closing:
                    for pos in range(len(stack) - 1, -1, -1):
                        if stack[pos][0] == tag:
                            _, opened_anchor, start = stack[pos]
                            if opened_anchor:
                                self.spans[opened_anchor] = SourceLocator(
                                    ".scratch/source/paper.html", opened_anchor, start, number
                                )
                            del stack[pos:]
                            break
                elif not match.group(0).endswith("/>"):
                    stack.append((tag, anchor, number))

    def span(self, anchor: str, line: int) -> SourceLocator:
        if anchor not in self.ids:
            raise PacketError(f"unknown HTML id {anchor!r}; refusing to invent a locator")
        if not line:
            raise PacketError(f"missing canonical/HTML line for HTML id {anchor!r}")
        candidates = [key for key in self.spans if key == anchor or key.startswith(anchor + ".")]
        if not candidates and self.enclosing.get(anchor) in self.spans:
            candidates = [self.enclosing[anchor]]
        if not candidates:
            raise PacketError(f"HTML id {anchor!r} has no resolved enclosing block")
        best = min(candidates, key=lambda key: (len(key), key))
        return self.spans[best]

    def resolve(self, value: str) -> SourceLocator | None:
        value = value.strip()
        if (value in {"", "-", "—", "none", "None", "n/a"}
                or value.startswith("- ") or value.lower().startswith("none ")):
            return None
        # A packet locator names both a file and the physical-line layer in that
        # file. Never rename a canonical-text line as an HTML line (or vice versa).
        match = re.search(
            r"(?:(?P<path>(?:\.scratch/(?:critical-lrp-orchestration/)?source/)?"
            r"paper(?:\.html|-tex\.txt))|(?P<alias>P|HTML|SRC))#"
            r"(?P<anchor>[^@\s;\]]+)@(?P<layer>L|h)(?P<first>\d+)"
            r"(?:-(?:L|h)?(?P<last>\d+))?", value)
        if match:
            path, alias = match.group("path"), match.group("alias")
            is_text = alias in {"P", "SRC"} or (path is not None and "paper-tex.txt" in path)
            is_html = alias == "HTML" or (path is not None and "paper.html" in path)
            if not (is_text or is_html):
                raise PacketError(f"unknown source alias in locator {value!r}")
            anchor = match.group("anchor")
            first = int(match.group("first"))
            last = int(match.group("last") or first)
            if first > last:
                raise PacketError(f"descending locator {value!r}")
            lines = self.tex_lines if is_text else self.html_lines
            if first < 1 or last > len(lines):
                raise PacketError(f"locator range is outside its named source layer: {value!r}")
            # Both aliases require an actual DOM statement/proof/display block.
            # The returned line span nevertheless stays in the requested layer.
            resolved = self.span(anchor, first)
            if is_text:
                return SourceLocator(".scratch/source/paper-tex.txt", anchor, first, last)
            if match.group("layer") == "L" and any(
                re.search(r'\bid="' + re.escape(anchor) + r'"', text)
                for text in self.html_lines[first - 1:last]
            ):
                return SourceLocator(".scratch/source/paper.html", anchor, first, last)
            return resolved
        if "canon L" in value:
            match = re.search(r"\bcanon L(\d+)", value)
            assert match
            line = int(match.group(1))
            if line > len(self.tex_lines):
                raise PacketError(f"canonical locator line beyond file: {value!r}")
            candidates = re.findall(r"\s\[([^]]+)\]", value)
            candidates.extend(self.canonical.get(line, []))
            if not candidates:
                raise PacketError(f"no HTML id resolves canonical line L{line}: {value!r}")
            for anchor in dict.fromkeys(candidates):
                if anchor in self.ids:
                    try:
                        return self.span(anchor, line)
                    except PacketError:
                        continue
            raise PacketError(f"none of {candidates} resolves to an HTML block: {value!r}")
        raise PacketError(f"locator does not name canonical text or paper.html: {value!r}")


COMBINED_FIELD_KEYS = set(NODE_FIELDS) | set(ALIASES) | {
    "DEPS", "ROUTES", "ROUTE_FOR", "NOTE", "NOTES", "OBLIGATIONS",
    "PROVENANCE", "CROSS_SLICE", "EXTERNAL", "ASSUMED", "FROZEN_STATE",
    "PROOF_OWNER", "USE_IN_SLICE", "ELIGIBILITY", "PROPOSED", "REVIEWER",
    "VERSION", "ROLE", "DEPTH", "OWNERSHIP",
}
COMBINED_FIELD_RE = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(sorted(COMBINED_FIELD_KEYS, key=len, reverse=True)) +
    r")(?=\s*(?::|\s))")


def _expand_combined_fields(text: str) -> list[str]:
    """Split compressed `FIELD value | FIELD value` records at real field names."""
    if "\t" in text or text.startswith(("EDGE:", "EDGE ")):
        return [text]
    matches = [
        match for match in COMBINED_FIELD_RE.finditer(text)
        if match.start() == 0 or text[:match.start()].rstrip().endswith(("|", ";"))
    ]
    if len(matches) < 2 or matches[0].start() != 0:
        return [text]
    pieces: list[str] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        key = match.group(1)
        value_start = match.end()
        colon = re.match(r"\s*:\s*", text[value_start:])
        if colon:
            value_start += colon.end()
        value = text[value_start:end].strip().strip("|").strip()
        pieces.append(f"{key}: {value}")
    return pieces


def _split_scalar_fields(text: str) -> tuple[str | None, str]:
    if "\t" in text:
        cells = text.split("\t")
        if cells[0].startswith("E") and cells[0][1:].isdigit():
            return None, text
        if re.fullmatch(r"[A-Z][A-Z_]*", cells[0].strip()):
            return cells[0].strip(), cells[-1].strip()
    match = FIELD.match(text.strip())
    if not match:
        return None, None
    key, value = match.groups()
    if "(" in key:
        key = key.split(None, 1)[0]
    return key, value


def _append_fields(fields: dict[str, str], key: str, value: str, context: str) -> None:
    qualifier = re.match(r"^([A-Z_]+)\s*\(([^)]+)\)$", key)
    if qualifier and (qualifier.group(2).lower() in FIELD_QUALIFIERS or qualifier.group(1) in NODE_FIELDS):
        key = qualifier.group(1)
    if key == "CONCLUSION" and value.lower().startswith("steps"):
        value = value.removeprefix("steps").strip()
    key = ALIASES.get(key, key)
    if not key:
        return
    if key in fields:
        if fields[key] == value:
            return
        raise PacketError(f"conflicting duplicate {key} in {context}")
    fields[key] = value.strip()


def chunks(path: Path) -> list[Chunk]:
    """Parse packets record locally; unterminated labels/fields are not accepted."""
    records: list[Chunk] = []
    detached: list[tuple[str, str, str, str, str]] = []
    current: Chunk | None = None
    pending: dict[str, str] | None = None
    active_field: str | None = None
    fenced = False
    # These packets put actual edge tables in fenced blocks; other packets use
    # fences only for examples and must not have those examples parsed as data.
    fenced_data = path.name in {
        "I54DeferredRoots.md", "I54Packet.md", "I41Normalized.md", "I423_NODES.md",
    }

    combined_keys = (
        "NODE_ID", "KIND", "SLICE", "ROUTE_FOR", "EXTERNAL", "ASSUMED",
        "FROZEN_ANCHOR_ID", "FROZEN_PATH", "FROZEN_EXPORT", "FROZEN_ABI_SHA256",
        "FROZEN_STATE", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE",
        "TOPOLOGY_STATUS", "USE_IN_SLICE", "ELIGIBILITY",
    )

    def flush_pending() -> None:
        nonlocal pending
        if pending is None:
            return
        required = ("FROM", "TO", "TYPE", "USE_SITE", "USE_TEXT", "TARGET_STATE")
        missing = [key for key in required if not pending.get(key)]
        if missing:
            raise PacketError(f"structured edge {pending} missing {missing}")
        consumer = pending["FROM"]
        evidence = f"{pending.get('PREREQUISITE', '')} {pending['USE_TEXT']} [TARGET_STATE {pending['TARGET_STATE']}]".strip()
        if current is not None:
            if consumer != current.identifier:
                raise PacketError("structured edge inside a record names a different consumer")
            current.edges.append((pending["TO"], pending["USE_SITE"], pending["TYPE"], evidence))
        else:
            # The I.1 packet has a separate edges section after every record.
            detached.append((consumer, pending["TO"], pending["USE_SITE"], pending["TYPE"], evidence))
        pending = None

    def close_record() -> None:
        nonlocal current
        if pending is not None:
            raise PacketError("record ends with unflushed EDGE")
        current = None

    physical_lines = list(enumerate(path.read_text().splitlines(), 1))
    expanded_lines = [
        (number, expanded)
        for number, raw in physical_lines
        for expanded in _expand_combined_fields(raw.strip())
    ]
    for number, raw in expanded_lines:
        line = raw.strip()
        if line.startswith("```"):
            fenced = not fenced
            if not fenced_data:
                continue
        if fenced and not fenced_data:
            continue
        match = HEADER.match(line)
        if match:
            if (current is not None and current.identifier == match.group(1)
                    and not current.fields and not current.notes and not current.edges
                    and pending is None):
                # `### NODE x` immediately followed by `NODE: x` is one record.
                continue
            close_record()
            current = Chunk(match.group(1), {}, [], [])
            records.append(current)
            active_field = None
            continue
        if line.startswith("#"):
            close_record()
            active_field = None
            continue
        cells = raw.split("\t")
        if cells[0].strip() == "EDGE_ID":
            continue
        if re.fullmatch(r"E\d+", cells[0]) and len(cells) >= 6:
            if pending is not None:
                raise PacketError(f"table edge inside structured edge at {path}:{number}")
            _, consumer, provider, relation, edge_class, site, *evidence = cells
            detached.append((consumer, provider, site, relation,
                             f"{edge_class}: {' '.join(evidence)}".strip()))
            continue
        if current is None and not (line in {"EDGE", "END"} or pending is not None
                                    or re.match(r"^EDGE\s+[A-Za-z0-9_.-]+:", line)):
            continue
        if line in {"---", "### END", "### END NODE"}:
            close_record()
            active_field = None
            continue
        if line == "EDGE":
            if pending is not None:
                raise PacketError(f"nested EDGE at {path}:{number}")
            pending = {}
            active_field = None
            continue
        if line == "END":
            if pending is not None:
                flush_pending()
            else:
                close_record()
            active_field = None
            continue
        if pending is None and re.match(r"^(?:NODE_ID|EXTERNAL|FROZEN_ANCHOR_ID|LEAN_STATUS):", line):
            matches = list(re.finditer(r"(?<!\w)(" + "|".join(combined_keys) + r"):\s*", line))
            if matches and matches[0].start() == 0:
                for index, item in enumerate(matches):
                    key = item.group(1)
                    end = matches[index + 1].start() if index + 1 < len(matches) else len(line)
                    value = line[item.end():end].strip()
                    if key == "NODE_ID" and value != current.identifier:
                        raise PacketError(f"record-line ID {value!r} != {current.identifier}")
                    if key in {"FROZEN_PATH", "FROZEN_EXPORT", "FROZEN_ABI_SHA256"}:
                        _append_fields(current.fields, key, value, current.identifier)
                    elif key in {"KIND", "ROUTE_FOR", "FROZEN_ANCHOR_ID", "EXTERNAL", "ASSUMED", "USE_IN_SLICE", "ELIGIBILITY"}:
                        if key in current.fields:
                            raise PacketError(f"repeated {key} in {current.identifier}")
                        current.fields[key] = value
                continue
        key, value = _split_scalar_fields(line)
        if key in {"CONTRACT_ID", "KIND", "TITLE", "LABEL", "ROUTE_FOR"} and ";" in value:
            key, value = key, value.replace(";", " ")
        if key == "CONTRACT_ID" and re.search(r"\bCONTRACT_VERSION\s*:", value):
            left, right = re.split(r"\bCONTRACT_VERSION\s*:", value, maxsplit=1)
            _append_fields(current.fields, "CONTRACT_ID", left.strip(), current.identifier)
            # I54 writes CONTRACT_VERSION: 1 after this split.
            parsed_version = FIELD.match("CONTRACT_VERSION " + right.strip())
            if parsed_version:
                _append_fields(current.fields, "CONTRACT_VERSION", parsed_version.group(2), current.identifier)
                value = ""
            key = None
        if pending is not None:
            if key in {"FROM", "TO", "TYPE", "USE_SITE", "USE_TEXT", "TARGET_STATE", "PREREQUISITE"}:
                if key in pending:
                    raise PacketError(f"repeated {key} in structured edge at {path}:{number}")
                pending[key] = value
                continue
            raise PacketError(f"unrecognized edge field {line!r} at {path}:{number}")
        one_line_edge = re.match(r"^EDGE(?:\s+[A-Za-z0-9_.-]+)?:\s*(.*)$", line)
        if one_line_edge:
            value = one_line_edge.group(1).strip()
            if " [arrow] " in value:
                if current is None:
                    raise PacketError(f"structured arrow edge has no owning record at {path}:{number}")
                consumer, remainder = value.split(" [arrow] ", 1)
                if consumer.strip() != current.identifier:
                    raise PacketError(f"edge consumer {consumer!r} differs from {current.identifier}")
                provider, separator, rationale = remainder.partition(" | ")
                role, separator2, rationale = rationale.partition(" | ")
                if not separator or not separator2:
                    raise PacketError(f"malformed arrow edge at {path}:{number}")
                site = re.search(r"((?:\.scratch/(?:critical-lrp-orchestration/)?source/)?paper\.html)?(#[\w.]+@L\d+-L\d+)", rationale)
                resolved_site = ((site.group(1) or ".scratch/source/paper.html") + site.group(2)) if site else ""
                if not site:
                    current.notes.append(f"UNLOCATED EDGE: {provider.strip()}; packet only says {rationale.strip()}")
                current.edges.append((provider.strip(), resolved_site, role.strip(), rationale.strip()))
                active_field = None
                continue
            parts = value.split("|", 2)
            if len(parts) != 3:
                raise PacketError(f"native/custom edge needs provider | consumer-use-site | rationale at {path}:{number}")
            provider, site_part, rationale = (part.strip() for part in parts)
            consumer = current.identifier if current is not None else ""
            site = site_part
            embedded = re.fullmatch(r"([A-Za-z0-9][A-Za-z0-9._:+/()\[\]-]*)\s+@\s+(\S+)", site_part)
            if embedded:
                consumer, site = embedded.group(1), embedded.group(2)
            if not consumer:
                raise PacketError(f"detached edge lacks consumer identity at {path}:{number}")
            if current is not None and consumer != current.identifier:
                raise PacketError(f"edge consumer {consumer!r} differs from {current.identifier}")
            if current is not None:
                current.edges.append((provider, site, "requires", rationale))
            else:
                detached.append((consumer, provider, site, "requires", rationale))
            active_field = None
            continue
        if key == "DEPS" and value.count("|") >= 2:
            # I.5.3/I.5.4 repeats DEPS once per fully annotated direct edge.
            provider, site, rationale = (part.strip() for part in value.split("|", 2))
            if not provider or not re.search(r"(?:P|HTML|SRC|paper\.html|paper-tex\.txt)#|paper-tex\.txt#", site):
                raise PacketError(f"malformed annotated DEPS edge in {current.identifier}: {value!r}")
            current.edges.append((provider, site, "requires", rationale))
            active_field = None
            continue
        if key == "ROUTES" and re.search(r"\s\([^()]*\)", value):
            current.notes.append(f"PACKET ANNOTATED ROUTES: {value}")
            value = re.sub(r"\s*\([^()]*\)", "", value).strip()
        if key == "ROUTES" and value.startswith("- "):
            current.notes.append(f"PACKET ROUTES DESCRIPTION: {value}")
            value = "-"
        if key == "DEPS" and value.startswith("(none"):
            current.notes.append(f"PACKET DEPS DESCRIPTION: {value}")
            active_field = None
            continue
        if key in {"DEPS", "ROUTES", "ROUTE_FOR", "TOPOLOGY_STATUS", "EXTERNAL", "ASSUMED",
                   "FROZEN_ANCHOR_ID", "FROZEN_STATE", "NOTE", "NOTES", "OBLIGATIONS",
                   "ERRATA_REFS", "PROOF_OWNER", "USE_IN_SLICE", "ELIGIBILITY"}:
            if key in current.fields:
                if key in {"DEPS", "ROUTES"}:
                    current.fields[key] += "," + value
                elif key in {"NOTE", "NOTES", "OBLIGATIONS"}:
                    current.fields[key] += " " + value
                else:
                    raise PacketError(f"repeated {key} in {current.identifier}")
            else:
                current.fields[key] = value
            active_field = key if key in {"NOTE", "NOTES", "OBLIGATIONS"} else None
            continue
        if key in {"FROZEN_FILE", "FROZEN_DECL", "FROZEN_PATH", "FROZEN_EXPORT", "FROZEN_ABI_SHA256"}:
            _append_fields(current.fields, key, value, current.identifier)
            active_field = None
            continue
        if key in NODE_FIELDS or key in ALIASES or key in {"SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION"}:
            if key == "PROOF_SOURCE" and value == "none (stated, not proved)":
                value = "-"
            _append_fields(current.fields, key, value, current.identifier)
            active_field = key
            continue
        if key and key.startswith("SOURCE") and key not in {"SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "SOURCE_CONSTANT_SCOPE", "SOURCE_CONSTANTS"}:
            raise PacketError(f"unknown source field {key} in {current.identifier}")
        if key:
            current.notes.append(f"UNSCHEMAED INPUT {key}: {value}")
            active_field = None
            continue
        if re.match(r"^[A-Za-z][A-Za-z .]{2,}:", line) and not line.startswith(("e.g.", "i.e.")):
            # Field-value prose may contain a colon; only unambiguous potential fields are rejected.
            if active_field is None and line.split(":", 1)[0].strip() in {"unknown", "unresolved"}:
                raise PacketError(f"unparsed prose/field near {path}:{number}")
        if active_field and line:
            # Preserve non-field lines (matrices, multi-line conclusions) rather than truncating them.
            previous = current.fields.get(active_field, "")
            current.fields[active_field] = (previous + " " + line).strip()
        elif line and line == "TARGET_STATE":
            raise PacketError(f"TARGET_STATE outside edge at {path}:{number}")
    if pending is not None:
        raise PacketError("EOF inside structured EDGE")
    owners = {record.identifier: record for record in records}
    if len(owners) != len(records):
        raise PacketError("duplicate record ID")
    for consumer, provider, site, kind, evidence in detached:
        if consumer not in owners:
            raise PacketError(f"structured edge owner {consumer!r} is not a record")
        owners[consumer].edges.append((provider, site, kind, evidence))
    return records


def _schema_id(identifier: str) -> str:
    # EXT.[93] is a citation label, not a legal graph ID. Keep its citation
    # in TITLE/NOTE while using the schema-safe token EXT.93 uniformly.
    answer = re.sub(r"\[([A-Za-z0-9._:-]+)\]", r"\1", identifier.strip())
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._:#/-]*", answer):
        raise PacketError(f"cannot safely normalize node ID {identifier!r}")
    return answer


def _edge_rationale(text: str) -> str:
    # Vertical bars have delimiters in graph syntax. Use distinct Unicode
    # mathematical bars without dropping or truncating the packet's evidence.
    return text.replace("||", "‖").replace("|", "∣")


def _identifier_list(value: str, field: str, identifier: str) -> list[str]:
    value = value.strip()
    if value in {"", "-", "none", "None", "[]"}:
        return []
    if value.startswith("[") and value.endswith("]"):
        value = value[1:-1]
    if "|" in value and "#" not in value:
        # I.5.3/I.5.4 writes route disjunctions with pipes rather than commas.
        value = ",".join(part.strip() for part in value.split("|"))
        value = re.sub(r"\s*\((?:DISJUNCTION|at least one holds)[^)]*\)\s*$", "", value,
                       flags=re.IGNORECASE)
    if field == "ROUTES" and value.startswith("("):
        # Do not parse prose as IDs: preserve it as an unresolved route reference instead.
        raise PacketError(f"unresolved ROUTES text on {identifier}: {value!r}")
    answer = [item.strip().strip("`") for item in re.split(r"[,;]", value) if item.strip()]
    for item in answer:
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._:+/()\[\]-]*", item):
            raise PacketError(f"invalid {field} ID {item!r} on {identifier}")
    return answer


def _frozen_authors(anchor: dict, contract_id: str, version: str) -> dict[str, str]:
    if anchor["contract"]["id"] != contract_id or anchor["contract"]["version"] != version:
        raise PacketError("frozen contract identity differs from the manifest")
    return {
        "FROZEN_FILE": anchor["path"], "FROZEN_DECL": anchor["export"],
        "FROZEN_ANCHOR_ID": anchor["id"], "FROZEN_ABI_SHA256": anchor["abi_sha256"],
    }


def normalize(packet: Path, root: Path, manifest_path: str) -> tuple[str, dict[str, int | bool]]:
    source = SourceIndex(root)
    manifest = json.loads((root / manifest_path).read_text())
    anchors = {entry["contract"]["id"]: entry for entry in manifest["anchors"]}
    roots = [name for name in ("hutchcroft.i.1.6", "hutchcroft.i.1.15") if name in anchors]
    records = chunks(packet)
    if not records:
        raise PacketError(f"no records recognized in {packet}")
    identifiers = [raw.identifier for raw in records]
    duplicate = [key for key, count in Counter(identifiers).items() if count > 1]
    if duplicate:
        raise PacketError(f"duplicate IDs {duplicate}")
    has_roots = all(name in identifiers for name in roots)
    normalized: list[Node] = []
    warnings: list[str] = []
    alternative_owners: dict[str, set[str]] = {}
    for raw in records:
        for provider, _, relation, _ in raw.edges:
            if relation in {"alternative", "alternative_of"}:
                alternative_owners.setdefault(provider, set()).add(raw.identifier)
    known: set[str] = {_schema_id(identifier) for identifier in identifiers}
    if len(known) != len(identifiers):
        raise PacketError("ID normalization creates a duplicate")
    for raw in records:
        f, identifier = raw.fields, _schema_id(raw.identifier)
        kind_input = f.get("KIND")
        if not kind_input or kind_input.lower() not in KINDS:
            raise PacketError(f"{identifier}: unknown KIND {kind_input!r}")
        kind = KINDS[kind_input.lower()]
        for field in ("TITLE", "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "CONSTANT_SCOPE"):
            value = f.get(field, "").strip()
            if not value or value in {"-", "—", "none", "None"}:
                if field in {"SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "CONSTANT_SCOPE"}:
                    value = "-"
                else:
                    raise PacketError(f"{identifier}: missing substantive {field}")
            if value.rstrip().endswith((" the", " a", " an", " of", " and", " or", " in", " with", " is", " are")):
                raise PacketError(f"{identifier}: apparently truncated {field}: {value!r}")
            f[field] = value
        proof_input = f.get("PROOF_SOURCE", "-")
        if proof_input not in {"", "-", "—", "none", "None", "n/a"}:
            raw.notes.append(f"PACKET PROOF_SOURCE: {proof_input}")
        statement_input = f.get("STATEMENT_SOURCE", "-")
        if statement_input.count("#") > 1:
            raw.notes.append(f"PACKET COMPOUND STATEMENT_SOURCE: {statement_input}")
        statement = source.resolve(statement_input)
        if proof_input.strip().lower() in {"same", "same block"} or proof_input.strip().lower().startswith("same block "):
            proof = statement
        elif proof_input.strip().startswith("#") and statement is not None:
            proof = source.resolve(f"{statement.path}{proof_input.strip()}")
        elif "#" not in proof_input:
            # Descriptive proof prose is not a source locator. A step may fall
            # back to its already-located statement below, with a warning; a
            # theorem cannot silently acquire one.
            if proof_input not in {"", "-", "—", "none", "None", "n/a"}:
                raw.notes.append("UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied")
            proof = None
        else:
            try:
                proof = source.resolve(proof_input)
            except PacketError as error:
                # A compressed record may continue its locator as `#S4...`
                # immediately after prose. Inherit only its already-named file.
                continuation = re.search(r"(?<![A-Za-z0-9_.-])#[A-Za-z0-9_.-]+@L\d+(?:-L\d+)?", proof_input)
                if statement is None or not continuation:
                    raise error
                proof = source.resolve(statement.path + proof_input[continuation.start():])
        if statement is None:
            raise PacketError(f"{identifier}: missing STATEMENT_SOURCE")
        # Missing proofs are fine for statements, but proof steps must locate their actual proof content.
        if kind in {"step", "application"} and proof is None:
            statement_as_proof = statement
            warnings.append(f"{identifier}: proof locator retained as statement; packet has no separate proof source")
        else:
            statement_as_proof = proof
        contract = f.get("CONTRACT_ID", identifier).strip()
        version = f.get("CONTRACT_VERSION", "1").strip()
        inline_version = re.fullmatch(r"(.+?)\s*\(v([^)]+)\)", contract)
        if inline_version:
            if inline_version.group(2) != version:
                raise PacketError(f"{identifier}: inline and explicit CONTRACT_VERSION disagree")
            contract = inline_version.group(1).strip()
        if not contract or not version or version.startswith("("):
            raise PacketError(f"{identifier}: missing/unresolved CONTRACT_VERSION")
        fields = {key: f.get(key, "-") for key in NODE_FIELDS}
        fields.update({
            "KIND": kind, "STATEMENT_SOURCE": statement.render(),
            "PROOF_SOURCE": statement_as_proof.render() if statement_as_proof else "-",
            "CONTRACT_ID": contract, "CONTRACT_VERSION": version,
            "TOPOLOGY_STATUS": "PROPOSED", "EXTRACTOR": packet.parent.name,
            "REVIEWER": "-", "LEAN_STATUS": "ASSUMED" if kind == "assumption" else "EXTERNAL" if kind == "external" else "NOT_STARTED",
            "LEAN_REF": "-", "LEAN_NOTE": "-",
        })
        for key in ("FROZEN_FILE", "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256"):
            fields[key] = "-"
        if identifier in anchors:
            supplied_hash = f.get("FROZEN_ABI_SHA256", "-")
            expected_hash = anchors[identifier]["abi_sha256"]
            if supplied_hash.startswith(expected_hash) or supplied_hash in {"-", ""}:
                fields.update(_frozen_authors(anchors[identifier], contract, version))
            else:
                raise PacketError(f"{identifier}: wrong frozen ABI SHA256")
        elif any(f.get(key, "-") not in {"", "-"} for key in ("FROZEN_FILE", "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256")):
            raise PacketError(f"{identifier}: non-anchor carries frozen metadata")
        notes = raw.notes + [f.get(key, "") for key in ("NOTE", "NOTES", "OBLIGATIONS", "ERRATA_REFS") if f.get(key, "-") not in {"", "-"}]
        if kind_input.lower() == "gap":
            notes.append("SOURCE_GAP: packet explicitly classifies this record as a source gap; review its exact impact.")
        notes.append(f"Imported from {packet}; all source claims and references remain unreviewed.")
        fields["NOTE"] = " ".join(notes)
        deps = [_schema_id(item) for item in _identifier_list(f.get("DEPS", "-"), "DEPS", identifier)]
        routes = [_schema_id(item) for item in _identifier_list(f.get("ROUTES", "-"), "ROUTES", identifier)]
        route_for = f.get("ROUTE_FOR", "-").strip()
        if kind == "route" and route_for in {"", "-"}:
            owners = alternative_owners.get(identifier, set())
            if len(owners) == 1:
                route_for = next(iter(owners))
            elif owners:
                warnings.append(f"route {identifier} has {len(owners)} competing ROUTE_FOR owners; retained unresolved")
        elif route_for not in {"", "-"}:
            raw_route_for = route_for
            try:
                route_for = _schema_id(route_for)
            except PacketError:
                # Keep malformed/multi-owner data visible for native topology diagnostics.
                route_for = raw_route_for
        fields["ROUTE_FOR"] = route_for
        # A route written in both DEPS and ROUTES is the same disjunctive input,
        # not an additional conjunctive hypothesis. Eliminate only exact duplicates.
        deps = [dep for dep in deps if dep not in set(routes)]
        edges: list[Edge] = []
        for provider, site_text, relation, rationale in raw.edges:
            provider = _schema_id(provider)
            edge_unlocated = site_text.strip() in {"", "-", "none"}
            if edge_unlocated:
                warnings.append(f"{identifier}: edge to {provider} lacks a packet use-site")
            edge_locator = statement if edge_unlocated else source.resolve(site_text) or statement
            label = "MISSING_USE_SITE; statement locator is only a placeholder: " if edge_unlocated else ""
            edges.append(Edge(provider, edge_locator.render(),
                              _edge_rationale(f"{label}packet relation {relation.strip() or 'unspecified'}: {rationale}"), 0))
            if relation in {"alternative_of", "alternative"}:
                if provider not in routes:
                    routes.append(provider)
                continue
            if relation == "proved_by":
                # Ownership is preserved as an EDGE annotation, not an ordinary DEPS edge.
                continue
            if provider in {"deferred", "none", "-"}:
                raise PacketError(f"{identifier}: unresolved provider {provider}")
            if f.get("TARGET_STATE") == "IGNORE":
                raise PacketError(f"{identifier}: scanned global TARGET_STATE field invalidated edges")
            if provider not in deps and relation not in {"consistency", "qualifies"} and provider not in routes:
                deps.append(provider)
        for dep in deps:
            if dep not in known:
                warnings.append(f"{identifier}: unresolved cross-slice dependency {dep}")
            if dep == identifier:
                raise PacketError(f"self-dependency {identifier}")
        for route in routes:
            if route not in known:
                warnings.append(f"{identifier}: unresolved route {route}")
            if route not in [edge.target for edge in edges]:
                warnings.append(f"{identifier}: ROUTES entry {route} lacks direct-use EDGE evidence")
        normalized.append(Node(identifier, 0, fields, {}, edges, deps, routes))
    header = f"""GRAPH_VERSION: 4
ROOTS: {','.join(roots) if has_roots else '-'}
CORPUS: .scratch/source/paper.html | arXiv:2508.18807v1
CONVENTIONS: unit-volume unit ball and C=1; imported packet only, not reviewed source topology
STANDING_ASSUMPTIONS: {','.join(raw.identifier for raw in records if raw.fields.get('KIND', '').lower() in {'assumption', 'assumed'}) or '-'}
EXTERNAL_POLICY: named cited inputs only; packet claims remain unverified
FROZEN_ANCHORS: {','.join(roots) if has_roots else '-'}
FROZEN_MANIFEST: {manifest_path} | sha256:{hashlib.sha256((root / manifest_path).read_bytes()).hexdigest()}
WRITER: openmathmodel-orchestrator
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

## Nodes

"""
    blocks = []
    for node in normalized:
        lines = [f"NODE: {node.node_id}"]
        for key in NODE_FIELDS:
            lines.append(f"{key}: {node.fields[key]}")
        lines.extend([f"DEPS: {','.join(node.deps) if node.deps else '-'}",
                      f"ROUTES: {','.join(node.routes) if node.routes else '-'}",
                      f"ROUTE_FOR: {node.fields.get('ROUTE_FOR', '-')}",
                      f"NOTE: {node.fields['NOTE']}"])
        for edge in node.edges:
            lines.append(f"EDGE: {edge.target} | {edge.source} | {edge.rationale}")
        blocks.append("\n".join(lines))
    diagnostics = {
        "records": len(records), "edges": sum(len(node.edges) for node in normalized),
        "dependency_edges": sum(len(node.deps) + len(node.routes) for node in normalized),
        "warnings": len(warnings), "has_roots": has_roots,
    }
    warnings.sort()
    return header + "\n\n".join(blocks) + "\n<!-- IMPORT DIAGNOSTICS\n" + "\n".join(warnings) + "\n-->\n", diagnostics


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--manifest", default="docs/orchestration/FROZEN_ANCHOR_MANIFEST.json")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expect-records", type=int)
    parser.add_argument("--expect-edges", type=int)
    args = parser.parse_args(argv)
    text, stats = normalize(args.packet, args.root, args.manifest)
    if args.expect_records is not None and stats["records"] != args.expect_records:
        raise PacketError(f"record count {stats['records']} != expected {args.expect_records}")
    if args.expect_edges is not None and stats["edges"] != args.expect_edges:
        raise PacketError(f"edge count {stats['edges']} != expected {args.expect_edges}")
    # Parse before writing so a successful run cannot install malformed output.
    graph = parse_graph(text, str(args.output))
    if graph.diagnostics.items:
        raise PacketError("output parser errors: " + "; ".join(d.render() for d in graph.diagnostics.items[:5]))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".new")
    temporary.write_text(text)
    temporary.replace(args.output)
    print(f"normalized {stats['records']} records, {stats['edges']} edges "
          f"({stats['dependency_edges']} dependency IDs; {stats['warnings']} unresolved-route/dependency diagnostics)")
    return 0


if __name__ == "__main__":
    main()
