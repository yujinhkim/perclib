#!/usr/bin/env python3
"""Small, auditable edits to normalized candidate graphs (never proof promotion)."""
from __future__ import annotations

import copy
from pathlib import Path

from proof_depgraph import (
    Edge, analyze, parse_graph, _validate_node_shape,
)
from import_source_packets import NODE_FIELDS, _edge_rationale


class Candidate:
    def __init__(self, path: Path, root: Path):
        self.path = path
        self.root = root
        self.text = path.read_text()
        self.graph = parse_graph(self.text, str(path))
        self.records = self.graph.node_records
        self.nodes = self.graph.nodes
        frozen = {item for item in self.graph.metadata.get("FROZEN_ANCHORS", "-").split(",") if item != "-"}
        _validate_node_shape(self.graph, root, frozen)
        self.sync_index()
        self.header = self.text.split("## Nodes", 1)[0] + "## Nodes\n\n"

    def sync_index(self):
        self.nodes = {node.node_id: node for node in self.records}

    def set_metadata(self, key: str, value: str):
        import re
        self.graph.metadata[key] = value
        self.header = re.sub(rf"(?m)^{re.escape(key)}:.*$", f"{key}: {value}", self.header, count=1)

    def clone(self, template: str, identifier: str, contract: str):
        base = copy.deepcopy(self.nodes[template])
        base.node_id = identifier
        base.fields["CONTRACT_ID"] = contract
        base.fields["EXTRACTOR"] = "openmathmodel-orchestrator-review"
        base.fields["REVIEWER"] = "-"
        base.fields["DEPS"] = "-"
        base.fields["ROUTES"] = "-"
        base.fields["ROUTE_FOR"] = "-"
        base.deps = []
        base.routes = []
        base.edges = []
        self.records.append(base)
        self.sync_index()
        return base

    def replace_references(self, old: str, new: str):
        for node in self.records:
            if node.node_id == old:
                node.node_id = new
            node.fields = {key: value.replace(old, new) for key, value in node.fields.items()}
            for edge in node.edges:
                if edge.target == old:
                    edge.target = new
                edge.rationale = edge.rationale.replace(old, new)
            node.deps = [new if item == old else item for item in node.deps]
            node.routes = [new if item == old else item for item in node.routes]
        self.sync_index()

    @staticmethod
    def add(node, target: str, site: str, rationale: str, *, route: bool = False):
        expected = node.routes if route else node.deps
        if target not in expected:
            expected.append(target)
        if not any(edge.target == target for edge in node.edges):
            node.edges.append(Edge(target, site, rationale, 0))
        assert sum(edge.target == target for edge in node.edges) == 1, (node.node_id, target)

    @staticmethod
    def drop(node, target: str):
        node.deps = [item for item in node.deps if item != target]
        node.routes = [item for item in node.routes if item != target]
        node.edges = [edge for edge in node.edges if edge.target != target]

    def remove(self, identifier: str):
        for node in self.records:
            self.drop(node, identifier)
        self.records = [node for node in self.records if node.node_id != identifier]
        self.sync_index()

    def render(self, output: Path, footer: str = ""):
        for node in self.records:
            node.fields["DEPS"] = ",".join(node.deps) if node.deps else "-"
            node.fields["ROUTES"] = ",".join(node.routes) if node.routes else "-"
            node.fields["TOPOLOGY_STATUS"] = "PROPOSED"
            node.fields["REVIEWER"] = "-"
            expected = node.deps + node.routes
            targets = [edge.target for edge in node.edges]
            for target in expected:
                if targets.count(target) != 1:
                    raise AssertionError((node.node_id, target, targets.count(target)))
            if set(targets) - set(expected):
                raise AssertionError((node.node_id, set(targets) - set(expected)))
        if len({node.node_id for node in self.records}) != len(self.records):
            raise AssertionError("duplicate node ID")
        if len({(node.value("CONTRACT_ID"), node.value("CONTRACT_VERSION")) for node in self.records}) != len(self.records):
            raise AssertionError("duplicate source contract")
        blocks = []
        for node in self.records:
            lines = [f"NODE: {node.node_id}"]
            lines.extend(f"{key}: {node.fields[key]}" for key in NODE_FIELDS)
            lines.extend([f"DEPS: {node.fields['DEPS']}", f"ROUTES: {node.fields['ROUTES']}",
                          f"ROUTE_FOR: {node.fields.get('ROUTE_FOR', '-')}", f"NOTE: {node.fields['NOTE']}"])
            lines.extend(f"EDGE: {edge.target} | {edge.source} | {_edge_rationale(edge.rationale)}" for edge in node.edges)
            blocks.append("\n".join(lines))
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(self.header + "\n\n".join(blocks) + footer)
        return output

    def analysis(self, output: Path, *, allow_dangling: bool = False, allow_open_proof: set[str] | None = None):
        allowed_open = allow_open_proof or set()
        graph = parse_graph(output.read_text(), str(output))
        if graph.metadata.get("ROOTS", "-") != "-" or graph.metadata.get("FROZEN_ANCHORS", "-") != "-":
            analysis = analyze(graph, source_root=self.root)
            diagnostics = analysis.diagnostics
        else:
            # Bounded slices intentionally have no roots. Use the same native
            # primitive checks as the packet validator, not the global root gate.
            from proof_depgraph import _apply_amendments, _validate_topology, _closure
            _validate_node_shape(graph, self.root, set())
            effective = _apply_amendments(graph, self.root, set())
            assumptions = [item for item in graph.metadata.get("STANDING_ASSUMPTIONS", "-").split(",") if item != "-"]
            _validate_topology(graph, effective, [], assumptions, [])
            graph.nodes = effective
            analysis = graph
            diagnostics = graph.diagnostics.items
        remaining = [diagnostic for diagnostic in diagnostics
                     if not (allow_dangling and "dangling" in diagnostic.message)]
        remaining = [diagnostic for diagnostic in remaining
                     if not any(f"node {node_id!r} KIND 'claim' needs a source-level PROOF_SOURCE" in diagnostic.message
                                for node_id in allowed_open)]
        if remaining:
            for diagnostic in remaining:
                print(diagnostic.render())
            raise AssertionError(f"{len(remaining)} native diagnostics remain")
        return analysis
