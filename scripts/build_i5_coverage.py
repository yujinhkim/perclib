#!/usr/bin/env python3
"""Generate a bounded I.5 coverage manifest from actual DOM and node inventories."""
from __future__ import annotations

import json
from html.parser import HTMLParser
from pathlib import Path
import re

from import_source_packets import SourceIndex
from proof_depgraph import parse_manifest, _validate_manifest

ROOT = Path(__file__).resolve().parents[1]
CANDIDATES = [ROOT / "docs/orchestration/candidates" / f"{name}.md" for name in
              ("i1", "i23", "i41", "i423", "i5152", "i5354")]
OUTPUT = ROOT / "docs/orchestration/candidates/I5_COVERAGE.md"

LABEL = re.compile(r"\bI\.5\.(\d+)\b")
CASE = re.compile(r"Cases?\s+(\d)\s+and\s+(\d)")
KIND = {"thm": "theorem", "theorem": "theorem", "prop": "proposition", "lemma": "lemma",
        "corollary": "corollary", "defn": "definition", "remark": "claim"}


class Proofs(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.proof = None
        self.rows = []
        self.depth = 0

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag == "div":
            self.depth += 1
            if "ltx_proof" in values.get("class", "").split():
                self.proof = {"id": values.get("id", ""), "text": [], "depth": self.depth}

    def handle_data(self, data):
        if self.proof:
            self.proof["text"].append(data)

    def handle_endtag(self, tag):
        if tag == "div":
            if self.proof and self.proof["depth"] == self.depth:
                self.rows.append(self.proof)
                self.proof = None
            self.depth -= 1


class Displays(HTMLParser):
    """Actual equation/body owners, without equation-group table duplication."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.tables = []
        self.open = []
        self.rows = []

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        identifier = values.get("id", "")
        classes = set(values.get("class", "").split())
        if tag == "table" and identifier.startswith("S5.") and ("ltx_equation" in classes or "ltx_equationgroup" in classes):
            self.tables.append((identifier, []))
            self.open.append(identifier)
        elif tag == "tbody" and identifier.startswith("S5.") and self.open:
            self.tables[-1][1].append(identifier)

    def handle_endtag(self, tag):
        if tag == "table" and self.open:
            identifier = self.open.pop()
            table_id, bodies = self.tables[-1]
            assert table_id == identifier, (table_id, identifier)
            self.rows.extend(bodies if bodies else [identifier])


def disposition_map(node_ids: set[str], label: str) -> tuple[str, str]:
    stem = f"hutchcroft.i.5.{label}"
    if stem not in node_ids and f"I.5.{label}" in node_ids:
        return f"NODE I.5.{label}", "Primary statement record with function-level proof obligations still PROPOSED."
    if stem in node_ids:
        candidates = [stem, f"{stem}.s1", f"{stem}.s2"]
        present = [identifier for identifier in candidates if identifier in node_ids]
        return "NODE " + ",".join(present), "Primary statement record with function-level proof obligations still PROPOSED."
    return "EXCLUDED", "No primary statement record in the bounded candidate. Any use remains a cross-slice obligation, not silently claimed coverage."


def main():
    inventory = json.loads((ROOT / "docs/orchestration/SOURCE_INVENTORY.json").read_text())["rows"]
    source = SourceIndex(ROOT)
    node_ids = {line.split(":", 1)[1].strip() for path in CANDIDATES for line in path.read_text().splitlines() if line.startswith("NODE:")}
    for stem in ("hutchcroft.i.1.6", "hutchcroft.i.1.15"):
        assert stem in node_ids
    parser = Proofs()
    parser.feed((ROOT / ".scratch/source/paper.html").read_text())
    regions = []
    for region in parser.rows:
        text = re.sub(r"\s+", " ", " ".join(region["text"])).strip()
        if re.search(r"Proof of Theorems\s+I\.1\.9\s+and\s+I\.1\.17", text):
            regions.append({"statement": None, "case": "main", "source": source.span(region["id"], 1).render(), "role": "Theorems I.1.9 and I.1.17"})
            continue
        match = LABEL.search(text)
        if not match:
            continue
        case = CASE.search(text)
        regions.append({
            "statement": int(match.group(1)),
            "case": f"{case.group(1)}-{case.group(2)}" if case else "main",
            "source": source.span(region["id"], 1).render(),
            "role": f"{match.group(0)}" + (f" cases {case.group(1)} and {case.group(2)}" if case else ""),
        })
    regions.sort(key=lambda row: (row["statement"] or 0, row["case"], row["source"]))
    lines = [
        "# Proof-source coverage manifest — bounded Section I.5 review inputs",
        "",
        "CORPUS: .scratch/source/paper.html | arXiv:2508.18807v1",
        "",
        "Status: all PROPOSED. This is a bounded source inventory, not a completed",
        "coverage review or root-closure proof. NODE dispositions point only at actual",
        "candidate IDs concatenated from the six current candidate graphs. EXCLUDED",
        "means unassigned in this bounded packet, not mathematically irrelevant or",
        "proved elsewhere. Deferred superprocess roots I.1.9/I.1.17 remain open.",
        "Statement ownership and source spans are computed from actual HTML DOM blocks;",
        "the stride-2 TSV locator enumeration is not used as a physical-line map.",
        "",
        "## Inventory",
        "",
    ]
    count = 0
    for row in inventory:
        match = LABEL.fullmatch(row["source_id"].split()[-1])
        if not match:
            continue
        label = int(match.group(1))
        disposition, reason = disposition_map(node_ids, str(label))
        lines += [f"ITEM: {row['source_id'].lower().replace(' ', '-')}",
                  f"KIND: {KIND[row['kind']]}",
                  f"SOURCE: {source.span(row['html_id'], 1).render()}",
                  f"DISPOSITION: {disposition}", f"REASON: {reason}",
                  "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py",
                  "REVIEWER: -", ""]
        count += 1
    proof_owners = {
        "S5.SS3.10": "PS.I5421", "S5.SS3.3": "PS.I5422", "S5.SS3.2": "PS.I5424",
        "S5.SS3.4": "PS.I5426", "S5.SS3.5": "PS.I5427", "S5.SS3.6": "PS.I5428",
        "S5.SS3.7": "PS.I5429C1,PS.I5429C4", "S5.SS3.8": "PS.I5429C2,PS.I5429C3",
        "S5.SS3.9": "PS.I5430",
        "S5.SS4.8": "PS.I5433", "S5.SS4.7": "PS.I5437", "S5.SS4.6": "PS.I5436",
        "S5.SS4.3": "PS.I5432", "S5.SS4.2": "PS.I5419",
        "S5.SS4.4": "PS.I5434", "S5.SS4.5": "PS.I5435",
    }
    for idx, region in enumerate(regions, 1):
        if region["statement"] is None:
            deferred_disposition = "NODE PS.I5419" if "PS.I5419" in node_ids else "EXCLUDED"
            lines += ["ITEM: deferred-proof-i.1.9-i.1.17", "KIND: proof-region",
                      f"SOURCE: {region['source']}", f"DISPOSITION: {deferred_disposition}",
                      "REASON: PS.I5419 provisionally records this proof region; the target roots I.1.9/I.1.17, canonical carrier, weak/vague topology and global root closure remain deferred. This is not a Lean provider assignment.",
                      "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py", "REVIEWER: -", ""]
            count += 1
            continue
        label = region["statement"]
        disposition, reason = disposition_map(node_ids, str(label))
        owner = proof_owners.get(region["source"].split("#", 1)[1].split("@", 1)[0])
        owners = owner.split(",") if owner else []
        if owners and all(item in node_ids for item in owners) and disposition.startswith("NODE "):
            disposition += "," + ",".join(owners)
        lines += [f"ITEM: proof-i.5.{label}.{region['case']}",
                  "KIND: proof-region", f"SOURCE: {region['source']}",
                  f"DISPOSITION: {disposition}",
                  f"REASON: Proof region ({region['role']}); reconstructing every substantive proof step remains an open obligation even where the statement has a primary node.",
                  "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py",
                  "REVIEWER: -", ""]
        count += 1
    for theorem in (9, 17):
        lines += [f"ITEM: deferred-theorem-i.1.{theorem}", "KIND: theorem",
                  f"SOURCE: {source.span(f'S1.Thmthm{theorem}', 1).render()}",
                  "DISPOSITION: EXCLUDED",
                  "REASON: Deferred canonical-superprocess target, not an implied I.5 coverage result. Integrated excursion carrier, Green function, mass law and measure topology remain unresolved.",
                  "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py", "REVIEWER: -", ""]
        count += 1
    for number in (33, 42, 43, 53):
        owner = f"D.I.5.{number}"
        assert owner in node_ids, f"coverage owner {owner} has not actually been extracted"
        lines += [f"ITEM: display-i.5.{number}", "KIND: display", f"SOURCE: {source.span(f'S5.E{number}', 1).render()}",
                  f"DISPOSITION: NODE {owner}",
                  "REASON: Extracted display record. This is source ownership only, not mathematical coverage or independent review.",
                  "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py", "REVIEWER: -", ""]
        count += 1

    # Independent census of actual equation/body owners, not an inference from
    # the drifted sidecar's enumerated line column or a reused reviewer total.
    # Equation groups use their labelled tbody rows instead of duplicating the
    # enclosing table; the final list is de-duplicated before classification.
    display_parser = Displays()
    display_parser.feed((ROOT / ".scratch/source/paper.html").read_text())
    assert not display_parser.open, "unclosed ltx_equation/group table"
    equation_roots = list(dict.fromkeys(
        identifier for identifier in display_parser.rows
        if 5163 <= source.span(identifier, 1).first and source.span(identifier, 1).last <= 6453
    ))
    assert len(equation_roots) == len(set(equation_roots))
    unnumbered = [identifier for identifier in equation_roots if not re.fullmatch(r"S5\.E\d+", identifier)]
    assert len(equation_roots) == 24 + len(unnumbered)
    for identifier in unnumbered:
        lines += [f"ITEM: unnumbered-display-{identifier.lower()}", "KIND: display",
                  f"SOURCE: {source.span(identifier, 1).render()}", "DISPOSITION: EXCLUDED",
                  "REASON: Unnumbered display with no separate display-level extraction. Its surrounding proof region may have a PS owner, but that is not display-level coverage.",
                  "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: scripts/build_i5_coverage.py", "REVIEWER: -", ""]
    text = "\n".join(lines).rstrip() + "\n"
    temporary = OUTPUT.with_suffix(".md.new")
    temporary.write_text(text)
    manifest = parse_manifest(text, str(OUTPUT))
    graph_nodes = {identifier: None for identifier in node_ids}
    nodes = _validate_manifest(manifest, graph_nodes, ROOT, require_complete=False)
    if manifest.diagnostics.items:
        for diagnostic in manifest.diagnostics.items:
            print(diagnostic.render())
        raise SystemExit(1)
    entry_count = sum(line.startswith("ITEM: ") for line in lines)
    temporary.replace(OUTPUT)
    print(f"coverage manifest: 37 statements, {len(regions)} proof regions, 2 deferred superprocess roots, {len(equation_roots)} display blocks ({len(unnumbered)} unnumbered/EXCLUDED and {entry_count} total indexed entries); all PROPOSED")


if __name__ == "__main__":
    main()
