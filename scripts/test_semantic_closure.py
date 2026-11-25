#!/usr/bin/env python3
import copy
import hashlib
import io
import json
import tempfile
import unittest
from unittest import mock
from pathlib import Path

from check_semantic_closure import FILES_KEY, ROOTS_KEY, check, semantic_closure


class SemanticClosureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parents[1] / ".scratch")
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        return path, hashlib.sha256(target.read_bytes()).hexdigest()

    def fixture(self):
        self.write("P/Base.lean", "module\n")
        self.write("P/Derived.lean", "module\npublic import P.Base\n")
        self.write("P/Unrelated.lean", "module\n")
        self.write("Frozen/Root.lean", "module\n")
        self.write("P/Probe.lean", "module\npublic import Frozen.Root\n")
        self.write(".scratch/P/Ignored.lean", "module\n")
        entry = lambda path: {"path": path, "sha256": hashlib.sha256((self.root / path).read_bytes()).hexdigest()}
        return {"anchors": [{
            "id": "root", "path": "Frozen/Root.lean", ROOTS_KEY: ["P.Derived"],
            FILES_KEY: [entry("P/Base.lean"), entry("P/Derived.lean")],
        }]}

    def test_transitive_closure(self):
        data = self.fixture()
        self.assertEqual(semantic_closure(self.root, ["P.Derived"]),
                         (["P/Base.lean", "P/Derived.lean"], []))
        errors, counts = check(data, self.root, core=False)
        self.assertEqual(errors, [])
        self.assertEqual(counts, {"root": 2})

    def test_hash_mutation_and_missing_entry_fail(self):
        data = self.fixture()
        data["anchors"][0][FILES_KEY][0]["sha256"] = "0" * 64
        errors, _ = check(data, self.root, core=False)
        self.assertTrue(any("hash drift" in error for error in errors))
        data = self.fixture()
        del data["anchors"][0][FILES_KEY][0]
        errors, _ = check(data, self.root, core=False)
        self.assertTrue(any("unpinned semantic dependency" in error for error in errors))

    def test_extra_and_provider_bounce_fail(self):
        data = self.fixture()
        data["anchors"][0][FILES_KEY].append(copy.deepcopy(data["anchors"][0][FILES_KEY][0]))
        errors, _ = check(data, self.root, core=False)
        self.assertTrue(any("new relative path" in error for error in errors))
        data = self.fixture()
        data["anchors"][0][ROOTS_KEY] = ["P.Unrelated"]
        errors, _ = check(data, self.root, core=False)
        self.assertIn("root: non-selected or stale semantic dependency entry: P/Base.lean", errors)
        data["anchors"][0][ROOTS_KEY] = ["P.Probe"]
        errors, _ = check(data, self.root, core=False)
        self.assertTrue(any("proof-bearing provider/frozen module" in error for error in errors))

    def test_dangling_import_and_missing_root_fail(self):
        self.write("P/Broken.lean", "module\nimport PercLib.DoesNotExist\n")
        _paths, errors = semantic_closure(self.root, ["P.Broken"])
        self.assertIn("P/Broken.lean: missing repository import PercLib.DoesNotExist", errors)
        _paths, errors = semantic_closure(self.root, ["P.NoRoot"])
        self.assertIn("semantic import root does not resolve to a repository module: P.NoRoot", errors)


class SemanticClosureHardeningTests(SemanticClosureTests):
    def test_trailing_comments_unicode_and_block_comments(self):
        self.write("PercLib/Base'.lean", "module\n")
        self.write("PercLib/Ünit.lean", "module\n")
        self.write("PercLib/Commented.lean", "module\n")
        self.write("PercLib/Derived.lean", "module\n/- import PercLib.CommentMissing -/\npublic import PercLib.Base' -- comment\npublic import PercLib.Ünit\n/-- import PercLib.DocMissing -/\n")
        paths, errors = semantic_closure(self.root, ["PercLib.Derived"])
        self.assertFalse(errors)
        self.assertIn("PercLib/Base'.lean", paths)
        self.assertIn("PercLib/Ünit.lean", paths)
        self.assertNotIn("PercLib/CommentMissing.lean", paths)
        self.assertNotIn("PercLib/DocMissing.lean", paths)

    def test_duplicate_module_name_fails_closed(self):
        self.write("PercLib/Base.lean", "module\n")
        self.write("PercLib.Base.lean", "module\n")
        _paths, errors = semantic_closure(self.root, ["PercLib.Base"])
        self.assertTrue(any("multiple files" in error for error in errors))

    def test_frozen_file_module_and_audit_are_not_semantic_roots(self):
        self.write("PercLib/Frozen.lean", "module\n")
        _paths, errors = semantic_closure(self.root, ["PercLib.Frozen"])
        self.assertTrue(any("proof-bearing" in error for error in errors))
        self.write("Audit/Diag.lean", "module\n")
        _paths, errors = semantic_closure(self.root, ["Audit.Diag"])
        self.assertTrue(any("proof-bearing" in error for error in errors))
        # Test the path-component policy separately from ordinary semantic source.
        self.write("PercLib/Providers.lean", "module\n")
        _paths, errors = semantic_closure(self.root, ["PercLib.Providers"])
        self.assertTrue(any("proof-bearing" in error for error in errors))

    def test_symlink_escape_rejected_even_when_unrelated(self):
        outside = self.root.parent / "outside-semantic-test.lean"
        outside.write_text("module\n")
        (self.root / "P").mkdir(exist_ok=True)
        (self.root / "P/Outside.lean").symlink_to(outside)
        _paths, errors = semantic_closure(self.root, ["P.Outside"])
        self.assertTrue(any("escapes --root" in error for error in errors))
        outside.unlink()

    def test_scope_scans_errors_only_in_selection(self):
        self.write("PercLib/Unrelated.lean", "module\n/- import PercLib.CommentedOut -/\n")
        self.write("PercLib/Good.lean", "module\n")
        paths, errors = semantic_closure(self.root, ["PercLib.Good"])
        self.assertEqual((paths, errors), (["PercLib/Good.lean"], []))

class SemanticScopeAndCliTests(SemanticClosureTests):
    def test_anchor_path_imports_are_required_even_if_roots_are_hollow(self):
        data = self.fixture()
        self.write("P/Meaning.lean", "module\npublic import P.Derived\n")
        self.write("Frozen/Root.lean", "module\npublic import P.Meaning\n")
        data["anchors"][0].update({"path": "Frozen/Root.lean", ROOTS_KEY: ["P.Unrelated"]})
        expected, errors = semantic_closure(self.root, ["P.Unrelated", "P.Meaning"])
        self.assertEqual(errors, [])
        data["anchors"][0][FILES_KEY] = [
            {"path": path, "sha256": hashlib.sha256((self.root / path).read_bytes()).hexdigest()}
            for path in expected
        ]
        errors, counts = check(data, self.root, core=False)
        self.assertEqual(errors, [])
        self.assertIn("P/Meaning.lean", {entry["path"] for entry in data["anchors"][0][FILES_KEY]})
        # Dropping a declaration's direct import is never a valid narrower list.
        data["anchors"][0][FILES_KEY] = [
            entry for entry in data["anchors"][0][FILES_KEY]
            if entry["path"] != "P/Meaning.lean"
        ]
        errors, _ = check(data, self.root, core=False)
        self.assertTrue(any("unpinned semantic dependency" in error for error in errors))

    def test_closure_only_cli_is_partial_not_combined_success(self):
        data = self.fixture()
        manifest = self.root / "manifest.json"
        manifest.write_text(json.dumps(data))
        with mock.patch("sys.stdout", new_callable=io.StringIO) as out:
            # Import only for the CLI test so other tests keep the small public API.
            import check_semantic_closure
            status = check_semantic_closure.main([
                "--root", str(self.root), "--manifest", str(manifest), "--skip-core"
            ])
        self.assertEqual(status, 3)
        self.assertIn("CORE FROZEN-ANCHOR GUARD NOT RUN", out.getvalue())
        self.assertNotIn("+ FROZEN-ANCHOR GUARD OK", out.getvalue())

    def test_empty_anchor_array_fails_even_without_core(self):
        errors, _ = check({"anchors": []}, self.root, core=False)
        self.assertIn("manifest: empty anchors array", errors)


if __name__ == "__main__":
    unittest.main()
