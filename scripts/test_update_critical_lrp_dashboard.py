"""Tests for snapshot validation in the Critical LRP dashboard generator."""

import unittest

import update_critical_lrp_dashboard as dashboard


class DashboardValidationTests(unittest.TestCase):
    def setUp(self):
        self.arguments = [
            {"status": "passed", "source_digest": "digest"},
            "digest",
            "Build completed successfully (42 jobs).",
            "Nonstandard axioms: 0\nsorryAx: 0\n",
            "Ran 3 tests in 0.01s\n\nOK\n",
            "SEMANTIC-CLOSURE + FROZEN-ANCHOR GUARD OK\n"
            "SOURCE-RESTITUTION GUARD OK\n",
        ]

    def test_matching_completed_snapshot_is_valid(self):
        self.assertTrue(dashboard.snapshot_validated(*self.arguments))

    def test_passing_logs_cannot_validate_a_changed_source(self):
        self.arguments[0]["source_digest"] = "older-digest"
        self.assertFalse(dashboard.snapshot_validated(*self.arguments))

    def test_pending_marker_cannot_export_old_passing_logs(self):
        self.arguments[0]["status"] = "running"
        self.assertFalse(dashboard.snapshot_validated(*self.arguments))

    def test_missing_tests_and_extra_axioms_are_rejected(self):
        self.arguments[4] = ""
        self.assertFalse(dashboard.snapshot_validated(*self.arguments))
        self.arguments[4] = "Ran 64 tests\n\nOK\n"
        self.arguments[3] = "Nonstandard axioms: 2\nsorryAx: 1\n"
        self.assertFalse(dashboard.snapshot_validated(*self.arguments))


if __name__ == "__main__":
    unittest.main()
