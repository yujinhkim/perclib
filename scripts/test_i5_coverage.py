#!/usr/bin/env python3
from pathlib import Path
import re
import unittest

import build_i5_coverage as coverage
from proof_depgraph import parse_manifest, _validate_manifest

ROOT = Path(__file__).resolve().parents[1]


class I5CoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        coverage.main()
        cls.path = ROOT / "docs/orchestration/candidates/I5_COVERAGE.md"
        cls.text = cls.path.read_text()
        cls.node_ids = {line.split(":", 1)[1].strip() for path in coverage.CANDIDATES
                        for line in path.read_text().splitlines() if line.startswith("NODE:")}

    def test_item_count_dispositions_and_namespace(self):
        self.assertEqual(self.text.count("ITEM: "), 152)
        self.assertEqual(self.text.count("ITEM: unnumbered-display-"), 77)
        self.assertIn("DISPOSITION: NODE I.5.29,PS.I5429C1,PS.I5429C4", self.text)
        self.assertIn("DISPOSITION: NODE I.5.29,PS.I5429C2,PS.I5429C3", self.text)
        self.assertIn("ITEM: deferred-proof-i.1.9-i.1.17", self.text)
        self.assertIn("DISPOSITION: NODE PS.I5419", self.text)
        for number in (24, 26, 28, 34, 35):
            self.assertIn(f"DISPOSITION: NODE I.5.{number},PS.I54{number}", self.text)
        for number in (33, 42, 43, 53):
            self.assertIn(f"DISPOSITION: NODE D.I.5.{number}", self.text)
        self.assertNotIn("COVERAGE_STATUS: REVIEWED", self.text)
        self.assertEqual(coverage.disposition_map({"I.5.29"}, "29")[0], "NODE I.5.29")

    def test_actual_manifest_validation(self):
        manifest = parse_manifest(self.text, str(self.path))
        graph_nodes = {identifier: None for identifier in self.node_ids}
        _validate_manifest(manifest, graph_nodes, ROOT, require_complete=False)
        self.assertFalse(manifest.diagnostics.items)
        self.assertEqual(len(manifest.records), 152)


if __name__ == "__main__":
    unittest.main()
