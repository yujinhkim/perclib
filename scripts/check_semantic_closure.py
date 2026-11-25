#!/usr/bin/env python3
"""Pin and check selected semantic source files, then run the frozen guard.

The boundary is mechanical: every non-proof repository import of an anchor is
covered in addition to the documented semantic_import_roots. This establishes
source-byte identity at the time of checking, not mathematical fidelity,
approval, elaboration, or an ABI theorem.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOTS_KEY = "semantic_import_roots"
FILES_KEY = "semantic_file_closure"
HASH = re.compile(r"^[0-9a-f]{64}$")
IMPORT = re.compile(
    r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*(?:--.*)?$")
IGNORED = {".lake", ".git", ".scratch", ".ultramath"}


def _load_guard():
    path = Path(__file__).with_name("check_frozen_anchors.py")
    spec = importlib.util.spec_from_file_location("critical_lrp_frozen_anchor_guard", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Guard


def _index(root: Path):
    root = root.resolve()
    candidates: dict[str, list[Path]] = {}
    for path in root.rglob("*.lean"):
        if IGNORED.intersection(path.relative_to(root).parts):
            continue
        name = ".".join(path.relative_to(root).with_suffix("").parts)
        candidates.setdefault(name, []).append(path)
    modules: dict[str, Path] = {}
    graph: dict[str, set[str]] = {}
    errors: dict[str, list[str]] = {}
    guard = _load_guard()
    for name, paths in candidates.items():
        if len(paths) != 1:
            errors[name] = [f"module name is claimed by multiple files: {', '.join(str(p.relative_to(root)) for p in paths)}"]
            continue
        path = paths[0]
        relative = str(path.relative_to(root))
        try:
            path.resolve().relative_to(root)
        except ValueError:
            errors[name] = [f"{relative}: repository source path escapes --root"]
            continue
        modules[name] = path
        try:
            text = guard.code_mask(path.read_bytes().decode("utf-8"))
        except (OSError, UnicodeError) as exc:
            errors[name] = [f"{relative}: cannot read module: {exc}"]
            graph[name] = set()
            continue
        imports: set[str] = set()
        errors[name] = []
        for line in text.splitlines():
            if not re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\b", line):
                continue
            match = IMPORT.fullmatch(line)
            if match is None:
                errors[name].append(f"{relative}: unsupported import line: {line.strip()}")
            else:
                imports.add(match.group(1))
        graph[name] = imports
    return modules, graph, errors


def module_graph(root: Path) -> tuple[dict[str, Path], dict[str, set[str]], list[str]]:
    """Compatibility query: the full unscoped diagnostics, by module name."""
    modules, graph, per_module = _index(root)
    return modules, graph, [error for group in per_module.values() for error in group]


def _is_proof_module(name: str, path: Path, root: Path) -> bool:
    parts = set(path.relative_to(root).parts) | set(name.split("."))
    return bool(parts.intersection({"Frozen", "Providers", "Audit"}))


def _import_closure(root, modules, graph, per_module, import_roots):
    seen: set[str] = set()
    todo = list(dict.fromkeys(import_roots))
    local_prefixes = {name.split(".")[0] for name in modules}
    errors: list[str] = []
    for name in import_roots:
        if name not in modules:
            errors.append(f"semantic import root does not resolve to a repository module: {name}")
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        for error in per_module.get(current, []):
            message = f"{current}: {error}"
            if message not in errors:
                errors.append(message)
        for imported in graph.get(current, ()):
            if imported not in modules:
                # Only local unresolved imports are meaningful here. Third-party
                # dependencies are outside this repository-import data model.
                if imported.startswith("PercLib.") or imported.split(".")[0] in local_prefixes:
                    source_name = str(modules[current].relative_to(root)) if current in modules else current
                    errors.append(f"{source_name}: missing repository import {imported}")
                continue
            todo.append(imported)
    return seen, errors


def semantic_closure(root: Path, import_roots: list[str]) -> tuple[list[str], list[str]]:
    root = root.resolve()
    modules, graph, per_module = _index(root)
    seen, errors = _import_closure(root, modules, graph, per_module, import_roots)
    paths = sorted(str(modules[name].relative_to(root)) for name in seen if name in modules)
    for name in seen:
        if name in modules and _is_proof_module(name, modules[name], root):
            errors.append(f"proof-bearing provider/frozen module is not a semantic input: {modules[name].relative_to(root)}")
    return paths, errors


def _anchor_required_roots(root: Path, anchor: dict[str, Any], label: str):
    """Imports of the declaration file that no hand-selected subset can omit."""
    path = anchor.get("path")
    if not isinstance(path, str):
        return [], [f"{label}.path: declaration source is not a string"]
    modules, graph, _ = _index(root)
    by_path = {candidate.resolve(): name for name, candidate in modules.items()}
    module = by_path.get((root / path).resolve())
    if module is None:
        return [], [f"{label}: declaration path is not a unique repository module: {path}"]
    required = sorted(name for name in graph.get(module, ())
                      if name in modules and not _is_proof_module(name, modules[name], root))
    return required, []


def _contained(root: Path, value: str):
    if not isinstance(value, str) or Path(value).is_absolute() or not value.endswith(".lean"):
        return None
    if any(part in {"", ".", ".."} for part in Path(value).parts):
        return None
    candidate = (root / value).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError:
        return None
    return candidate if candidate.is_file() else None


def check(data: Any, root: Path, *, core: bool = True) -> tuple[list[str], dict[str, int]]:
    root = root.resolve()
    errors: list[str] = []
    counts: dict[str, int] = {}
    if not isinstance(data, dict) or not isinstance(data.get("anchors"), list):
        return ["manifest: expected object with anchors array"], counts
    if not data["anchors"]:
        errors.append("manifest: empty anchors array")
    for number, anchor in enumerate(data["anchors"]):
        label = anchor.get("id", f"anchor[{number}]") if isinstance(anchor, dict) else f"anchor[{number}]"
        if not isinstance(anchor, dict):
            errors.append(f"{label}: expected object")
            continue
        imports = anchor.get(ROOTS_KEY)
        if (not isinstance(imports, list) or not imports or len(imports) != len(set(imports))
                or any(not isinstance(name, str) or not name or name in {"Frozen", "Providers"} for name in imports)):
            errors.append(f"{label}.{ROOTS_KEY}: expected unique nonempty module-name array")
            continue
        entries = anchor.get(FILES_KEY)
        if not isinstance(entries, list):
            errors.append(f"{label}.{FILES_KEY}: expected path/sha256 array")
            continue
        required, required_errors = _anchor_required_roots(root, anchor, label)
        errors.extend(required_errors)
        expected, closure_errors = semantic_closure(root, sorted(set(imports) | set(required)))
        errors.extend(f"{label}: {message}" for message in closure_errors)
        counts[label] = len(expected)
        actual: dict[str, str] = {}
        for index, entry in enumerate(entries):
            item_label = f"{label}.{FILES_KEY}[{index}]"
            if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
                errors.append(f"{item_label}: expected exactly path and sha256")
                continue
            path, digest = entry["path"], entry["sha256"]
            if not isinstance(path, str) or path in actual or _contained(root, path) is None:
                errors.append(f"{item_label}: expected a new relative path inside --root")
                continue
            if not isinstance(digest, str) or not HASH.fullmatch(digest):
                errors.append(f"{item_label}: expected lowercase SHA256")
                continue
            actual[path] = digest
        for path in sorted(set(expected) - set(actual)):
            errors.append(f"{label}: unpinned semantic dependency: {path}")
        for path in sorted(set(actual) - set(expected)):
            errors.append(f"{label}: non-selected or stale semantic dependency entry: {path}")
        for path, recorded in actual.items():
            candidate = _contained(root, path)
            if candidate is None:
                continue
            import hashlib
            if hashlib.sha256(candidate.read_bytes()).hexdigest() != recorded:
                errors.append(f"{label}: semantic dependency hash drift: {path}")
    if core:
        reduced = copy.deepcopy(data)
        for anchor in reduced.get("anchors", []):
            if isinstance(anchor, dict):
                anchor.pop(ROOTS_KEY, None)
                anchor.pop(FILES_KEY, None)
        guard = _load_guard()(root)
        guard.check(reduced)
        errors.extend(guard.errors)
    return errors, counts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--skip-core", action="store_true",
                        help="closure-only mutation diagnostics; returns 3 even when no errors are found")
    args = parser.parse_args(argv)
    try:
        data = json.loads(args.manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"SEMANTIC-CLOSURE GUARD FAILED: cannot read manifest: {exc}", file=sys.stderr)
        return 2
    errors, counts = check(data, args.root, core=not args.skip_core)
    if errors:
        print("SEMANTIC-CLOSURE GUARD FAILED:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    for anchor, count in sorted(counts.items()):
        print(f"{anchor}: {count} semantic source files pinned")
    if args.skip_core:
        print("SEMANTIC CLOSURE ONLY: CORE FROZEN-ANCHOR GUARD NOT RUN")
        return 3
    print("SEMANTIC-CLOSURE + FROZEN-ANCHOR GUARD OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
