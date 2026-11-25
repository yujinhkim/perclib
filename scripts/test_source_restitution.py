#!/usr/bin/env python3
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from check_source_restitution import math_errors, restitution_errors, TEXT_SHA256
from html_restitution import convert

PROJECT = Path(__file__).resolve().parents[1]
SCRIPT = PROJECT / "scripts/html_restitution.py"
FIXTURE = """<!doctype html><html><head><script>initializeReadingPreferences()</script></head>
<body><nav>I.1.1 Critical phenomena in long-range percolation</nav>
<section id="S1.Thmthm15.2"><h6>Theorem</h6><p>Suppose <math alttext="d=3\\alpha&lt;6"><mi>bad duplicate</mi></math>
and <math alttext="r&lt;\\infty"><mi>bad duplicate too</mi></math>.</p></section></body></html>
"""


class RestitutionTests(unittest.TestCase):
    def test_fixture_preserves_inequalities_and_drops_chrome(self):
        text, ids, maths = self.convert_fixture()
        text, ids, maths = self.convert_fixture()
        self.assertIn("d=3\\alpha<6", text)
        self.assertIn("r<\\infty", text)
        self.assertNotIn("bad duplicate", text)
        self.assertNotIn("initializeReadingPreferences", text)
        self.assertEqual(len(maths), 2)
        self.assertIn("S1.Thmthm15.2", ids)

    def convert_fixture(self):
        with tempfile.TemporaryDirectory(dir=PROJECT / ".scratch") as temp:
            path = Path(temp) / "fixture.html"
            path.write_text(FIXTURE)
            return convert(str(path))

    def test_annotation_loss_fails_closed(self):
        text, _ids, maths = self.convert_fixture()
        corrupted = text.replace("d=3\\alpha<6", "d=3\\alpha")
        self.assertTrue(math_errors(corrupted, maths))

    def test_pinned_html_and_text_pass(self):
        failures = restitution_errors(
            PROJECT,
            PROJECT / ".scratch/source/paper.html",
            PROJECT / ".scratch/source/paper-tex.txt",
            PROJECT / ".scratch/source/paper-tex.locators.tsv",
        )
        self.assertEqual(failures, [])

    def test_real_regeneration_is_identical_and_guard_passes(self):
        with tempfile.TemporaryDirectory(dir=PROJECT / ".scratch") as temp:
            output = Path(temp) / "regenerated.txt"
            locators = Path(temp) / "locators.tsv"
            result = subprocess.run(
                [sys.executable, str(SCRIPT), str(PROJECT / ".scratch/source/paper.html"),
                 str(output), "--locators", str(locators)],
                cwd=PROJECT, text=True, capture_output=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), (PROJECT / ".scratch/source/paper-tex.txt").read_bytes())
            self.assertEqual(TEXT_SHA256, __import__('hashlib').sha256(output.read_bytes()).hexdigest())
            guard = subprocess.run(
                [sys.executable, str(PROJECT / "scripts/check_source_restitution.py")],
                cwd=PROJECT, text=True, capture_output=True, check=False,
            )
            self.assertEqual(guard.returncode, 0, guard.stderr)
            self.assertIn("SOURCE-RESTITUTION GUARD OK", guard.stdout)


if __name__ == "__main__":
    unittest.main()
