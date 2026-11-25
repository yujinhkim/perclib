#!/usr/bin/env python3
"""CLI tests for the repository-native packet validator."""
import json
from pathlib import Path
import unittest

from validate_source_packets import main

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[1]


class ValidatorCliTests(unittest.TestCase):
    def test_clean_i23_candidate_and_json_report(self):
        packet = PROJECT / ".ultramath/smwobyis9/m2/I23Packet.m2.md"
        if not packet.is_file():
            self.skipTest(f"research packet is unavailable: {packet}")
        out = ROOT / ".scratch/validator-cli-test"
        status = main(["--root", str(ROOT), "--output-dir", str(out / "graph"),
                       "--report", str(out / "report.json"), "--candidate", f"i23={packet}"])
        self.assertEqual(status, 0)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["status"], "NATIVE_CLEAN")
        self.assertEqual(report["candidates"][0]["stats"]["records"], 68)
        self.assertEqual(report["candidates"][0]["stats"]["edges"], 93)

    def test_declared_open_input_is_required_not_silent(self):
        packet = ROOT / ".scratch/packet-native-validation/repaired/I41Normalized.md"
        if not packet.is_file():
            self.skipTest(f"repaired candidate is unavailable: {packet}")
        out = ROOT / ".scratch/validator-open-test"
        common = ["--root", str(ROOT), "--output-dir", str(out / "graph"),
                  "--report", str(out / "report.json"), "--candidate", f"i41={packet}"]
        self.assertEqual(main(common), 1)
        rejected = json.loads((out / "report.json").read_text())
        self.assertEqual(rejected["candidates"][0]["status"], "FAILED")
        accepted = main(common + ["--allow-open-proof", "hutchcroft.i.4.4"])
        self.assertEqual(accepted, 0)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["declared_open_proof_inputs"], ["hutchcroft.i.4.4"])
        self.assertEqual(report["candidates"][0]["status"], "OPEN_DECLARED_PROOF_INPUT")


if __name__ == "__main__":
    unittest.main()
