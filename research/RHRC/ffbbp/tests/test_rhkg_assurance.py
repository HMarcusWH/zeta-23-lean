import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
REPO = RHRC.parents[1]
WORKFLOW_DIR = REPO / ".github" / "workflows"
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

    def test_live_snapshot_produces_expected_ffbbp_separation(self):
        if any(WORKFLOW_DIR.glob("rhrc_*_materializer.yml")):
            self.skipTest("one-shot theorem materializer has not rebound the live snapshot yet")

        report = build_report()
        self.assertEqual(report["input_snapshot"]["candidate_count"], 2362)
        self.assertEqual(report["input_snapshot"]["source_only_public_theorem_count"], 680)

        module_only = report["reductions"]["MODULE_ONLY_SNAPSHOT"]
        self.assertFalse(module_only["assurance_gate"]["passed"])
        self.assertEqual(module_only["decision_factorization"]["fiber_count"], 298)
        self.assertEqual(module_only["decision_factorization"]["mixed_value_fiber_count"], 128)
        self.assertEqual(module_only["diagnostic_factorization"]["mixed_value_fiber_count"], 167)

        type_digest = report["reductions"]["TYPE_DIGEST_SNAPSHOT"]
        self.assertTrue(type_digest["decision_factorization"]["passed"])
        self.assertFalse(type_digest["diagnostic_factorization"]["passed"])
        self.assertGreaterEqual(type_digest["decision_factorization"]["fiber_count"], 2324)
        self.assertLessEqual(type_digest["decision_factorization"]["fiber_count"], 2362)
        self.assertEqual(type_digest["diagnostic_factorization"]["mixed_value_fiber_count"], 7)

        selected = report["reductions"]["MODULE_VISIBILITY_SNAPSHOT"]
        self.assertTrue(selected["assurance_gate"]["passed"])
        self.assertEqual(selected["decision_factorization"]["fiber_count"], 515)
        self.assertEqual(report["source_only_module_cohort_count"], 195)

        self.assertEqual(report["terminal_claim"], "RH_OPEN")
        self.assertFalse(report["theorem_promotion"])
        self.assertFalse(report["inherits_run42c_qualification"])



if __name__ == "__main__":
    unittest.main()
