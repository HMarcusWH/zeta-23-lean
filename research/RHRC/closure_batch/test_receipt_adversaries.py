from __future__ import annotations

import copy
import unittest

from interval_codec import DyadicInterval
from verify_receipt import ReceiptError, plan_digest, verify_receipt


class ReceiptAdversaryTests(unittest.TestCase):
    def setUp(self):
        self.plan = {
            "receipt_scope": {
                "required_case_ids": [
                    "A_UNIFORM_BASE", "A_SEAM_TRANSFER", "B_SCHUR",
                    "C_SPECTRAL_LIMIT", "D_DETECTOR"
                ]
            }
        }
        intervals = [
            DyadicInterval.from_decimal_bounds("1", "2"),
            DyadicInterval.from_decimal_bounds("-2", "-1"),
            DyadicInterval.from_decimal_bounds("0", "0"),
            DyadicInterval.from_decimal_bounds("-1", "1"),
            DyadicInterval.from_decimal_bounds("3", "4")
        ]
        ids = self.plan["receipt_scope"]["required_case_ids"]
        cases = [
            {"id": i, "interval": d.to_json(), "claimed_sign": d.sign()}
            for i, d in zip(ids, intervals)
        ]
        signs = {"POSITIVE": 0, "NEGATIVE": 0, "ZERO_ONLY": 0, "CONTAINS_ZERO": 0}
        for c in cases:
            signs[c["claimed_sign"]] += 1
        self.receipt = {
            "schema_version": "RHRC-CLOSURE-RECEIPT-1.0",
            "execution_status": "SUCCESS",
            "integrity_status": "PASS",
            "research_disposition": "MIXED_OPEN",
            "terminal_claim": "RH_OPEN",
            "source": {"commit": "a" * 40, "tree": "b" * 40},
            "plan_sha256": plan_digest(self.plan),
            "cases": cases,
            "summary": {"case_count": len(cases), "sign_counts": signs}
        }

    def test_valid(self):
        self.assertEqual(verify_receipt(self.receipt, self.plan)["status"], "PASS")

    def test_reject_empty_cases(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"] = []
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_fabricated_summary(self):
        bad = copy.deepcopy(self.receipt)
        bad["summary"]["case_count"] = 999
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_control_failure_as_pass(self):
        bad = copy.deepcopy(self.receipt)
        bad["research_disposition"] = "CONTROL_FAILURE"
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_forged_sign(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][0]["claimed_sign"] = "NEGATIVE"
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_empty_scope(self):
        bad_plan = {"receipt_scope": {"required_case_ids": []}}
        bad = copy.deepcopy(self.receipt)
        bad["plan_sha256"] = plan_digest(bad_plan)
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, bad_plan)


if __name__ == "__main__":
    unittest.main()
