#!/usr/bin/env python3
"""An invalid partial graph must diagnose dangling references, not crash."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_depgraph import analyze, parse_graph


class DanglingDiagnosticsTest(unittest.TestCase):
    def test_closure_skips_dangling_dependency_after_recording_diagnostic(self):
        graph = parse_graph("""GRAPH_VERSION: 4
ROOTS: root
CORPUS: paper
CONVENTIONS: test
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: test
FROZEN_ANCHORS: -
WRITER: test
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

NODE: root
KIND: theorem
TITLE: Test
STATEMENT_SOURCE: paper.html#proof@L1-L2
PROOF_SOURCE: paper.html#proof@L1-L2
CONTRACT_ID: root
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: source premise
SOURCE_QUANTIFIERS: all source indices
SOURCE_CONCLUSION: source conclusion
CONSTANT_SCOPE: source constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: external.missing
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: test
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
EDGE: external.missing | paper.html#proof@L1-L2 | intended consumer use
NOTE: unresolved research packet
FROZEN_MANIFEST: -
""", "<dangling>")
        analysis = analyze(graph)
        self.assertEqual(analysis.root_closure, {"root"})
        self.assertEqual(analysis.outside_root_closure, [])
        messages = [item.message for item in graph.diagnostics.items]
        self.assertTrue(any("dangling dependency 'external.missing'" in item for item in messages))


if __name__ == "__main__":
    unittest.main()
