#!/usr/bin/env python3
import tempfile
import unittest
from pathlib import Path

from check_frozen_anchors import Guard


class ProductionScopeTests(unittest.TestCase):
    def test_scratch_probes_are_not_production_but_module_holes_fail(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parents[1] / ".scratch") as temp:
            root = Path(temp)
            (root / ".scratch/Probe").mkdir(parents=True)
            (root / ".ultramath/member").mkdir(parents=True)
            (root / "PercLib/Wrong").mkdir(parents=True)
            for path in [root / ".scratch/Probe/Draft.lean", root / ".ultramath/member/Draft.lean"]:
                path.write_text("module\ntheorem provisional : True := by sorry\n")
            (root / "PercLib/Wrong/Draft.lean").write_text("module\ntheorem provisional : True := by sorry\n")
            guard = Guard(root)
            self.assertEqual(guard.project_files(), [root / "PercLib/Wrong/Draft.lean"])
            guard.check_all_sorries()
            self.assertTrue(any("unauthorized `sorry`" in error for error in guard.errors))


if __name__ == "__main__":
    unittest.main()
