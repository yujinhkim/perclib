#!/usr/bin/env python3
"""Normalize research packets and run the real source-graph validators.

This is not a source-fidelity or independent-topology review. Every imported
record remains PROPOSED. Only explicitly named missing claim-proof locators may
be declared open on the command line; all other diagnostics fail the run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from import_source_packets import normalize, PacketError
from proof_depgraph import _apply_amendments, _validate_node_shape, _validate_topology, parse_graph

MANIFEST = "docs/orchestration/FROZEN_ANCHOR_MANIFEST.json"


def identifiers(value: str, field: str) -> list[str]:
    return [item for item in value.split(",") if item and item != "-"]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--candidate", action="append", required=True,
                        metavar="NAME=PATH", help="research packet to normalize and validate")
    parser.add_argument("--allow-open-proof", action="append", default=[],
                        metavar="NODE_ID", help="allow only this claim's missing source proof locator")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    allowed_open = set(args.allow_open_proof)
    observed_open = set()
    report = {"schema": "source-packet-native-validation-v1", "candidates": []}
    failures = []
    for specification in args.candidate:
        name, separator, filename = specification.partition("=")
        if not separator or not name:
            parser.error(f"invalid --candidate {specification!r}")
        path = Path(filename).resolve()
        entry = {"name": name, "input": str(path),
                 "input_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        report["candidates"].append(entry)
        try:
            text, stats = normalize(path, root, MANIFEST)
            output = args.output_dir / f"{name}.md"
            output.write_text(text)
            entry["stats"] = stats
            entry["output_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
            entry["topology_status"] = "PROPOSED (all nodes)"
            graph = parse_graph(text, str(output))
            metadata = graph.metadata
            roots = identifiers(metadata.get("ROOTS", "-"), "ROOTS")
            assumptions = identifiers(metadata.get("STANDING_ASSUMPTIONS", "-"), "STANDING_ASSUMPTIONS")
            frozen = identifiers(metadata.get("FROZEN_ANCHORS", "-"), "FROZEN_ANCHORS")
            # Deliberately call the repository validators, not a packet checker.
            _validate_node_shape(graph, root, set(frozen))
            nodes = _apply_amendments(graph, root, set(frozen))
            _validate_topology(graph, nodes, roots, assumptions, frozen)
            diagnostics = [item.render() for item in graph.diagnostics.items]
            entry["native_diagnostics"] = diagnostics
            remaining = []
            for diagnostic in diagnostics:
                open_node = next((node for node in allowed_open
                                  if f"node {node!r} KIND 'claim' needs a source-level PROOF_SOURCE" in diagnostic), None)
                if open_node:
                    observed_open.add(open_node)
                else:
                    remaining.append(diagnostic)
            if remaining:
                failures.extend(remaining)
            entry["status"] = ("FAILED" if remaining else
                               "OPEN_DECLARED_PROOF_INPUT" if len(diagnostics) != len(remaining)
                               else "NATIVE_CLEAN")
        except (OSError, PacketError) as error:
            entry["status"] = "FAILED"
            entry["error"] = f"{type(error).__name__}: {error}"
            failures.append(f"{name}: {entry['error']}")
    unused_open = sorted(allowed_open - observed_open)
    if unused_open:
        failures.append(f"declared open proof inputs not observed: {unused_open}")
    report["declared_open_proof_inputs"] = sorted(observed_open)
    report["status"] = "FAILED" if failures else "VALIDATED_WITH_DECLARED_OPEN_INPUTS" if observed_open else "NATIVE_CLEAN"
    report["failures"] = failures
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for entry in report["candidates"]:
        details = entry.get("stats", entry.get("error", {}))
        print(f"{entry['name']}: {entry['status']} {details}")
    print(f"overall: {report['status']}; report: {args.report}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
