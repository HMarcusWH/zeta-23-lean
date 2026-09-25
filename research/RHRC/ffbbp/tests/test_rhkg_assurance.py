import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ffbbp.rhkg_assurance import build_report
from ffbbp.v16_commutation import assess_categorical_snapshot_sufficiency


class FFBBPRHKGAssuranceTests(unittest.TestCase):
    def test_mixed_fiber_fails_snapshot_decision_sufficiency(self):
        rows = [
            {"id": "a", "module": "M", "visibility": "SOURCE_ONLY_PUBLIC_THEOREM"},
            {"id": "b", "module": "M", "visibility": "ALREADY_IN_REGISTERED_DEPENDENCY_CLOSURE"},
        ]
        result = assess_categorical_snapshot_sufficiency(
            rows,
            reduction_key=lambda row: (row["module"],),
            value_map=lambda row: row["visibility"] == "SOURCE_ONLY_PUBLIC_THEOREM",
            item_id=lambda row: row["id"],
        )
        self.assertFalse(result.passed)
        self.assertEqual(result.mixed_value_fiber_count, 1)

    def test_retaining_decision_field_passes(self):
        rows = [
            {"id": "a", "module": "M", "visibility": "SOURCE_ONLY_PUBLIC_THEOREM"},
            {"id": "b", "module": "M", "visibility": "ALREADY_IN_REGISTERED_DEPENDENCY_CLOSURE"},
        ]
        result = assess_categorical_snapshot_sufficiency(
            rows,
            reduction_key=lambda row: (row["module"], row["visibility"]),
            value_map=lambda row: row["visibility"] == "SOURCE_ONLY_PUBLIC_THEOREM",
            item_id=lambda row: row["id"],
        )
        self.assertTrue(result.passed)
        self.assertEqual(result.mixed_value_fiber_count, 0)

    def test_live_snapshot_preserves_fail_closed_navigation_semantics(self):
        report = build_report()
        summary = report["input_snapshot"]
        self.assertGreater(summary["candidate_count"], 0)
        self.assertGreater(summary["source_only_public_theorem_count"], 0)
        self.assertLess(summary["source_only_public_theorem_count"], summary["candidate_count"])

        module_only = report["reductions"]["MODULE_ONLY_SNAPSHOT"]
        self.assertFalse(module_only["assurance_gate"]["passed"])
        self.assertGreater(module_only["decision_factorization"]["mixed_value_fiber_count"], 0)

        selected = report["reductions"]["MODULE_VISIBILITY_SNAPSHOT"]
        self.assertTrue(selected["assurance_gate"]["passed"])
        self.assertEqual(selected["assurance_gate"]["status"], "PASS")
        self.assertGreater(report["source_only_module_cohort_count"], 0)

        self.assertEqual(report["theory_version"], "1.7")
        self.assertEqual(report["terminal_claim"], "RH_OPEN")
        self.assertFalse(report["theorem_promotion"])
        self.assertFalse(report["inherits_runtime_qualification"])
        self.assertEqual(report["runtime_authority"]["version"], "1.5.1+RUN42C_inductive_firewall_closure_overlay")


if __name__ == "__main__":
    unittest.main()
