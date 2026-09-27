from __future__ import annotations

import copy
import unittest

from interval_codec import DyadicInterval
from verify_receipt import ReceiptError, digest, verify_receipt


def interval(lo: str, hi: str, bits: int) -> dict:
    return DyadicInterval.from_decimal_bounds(lo, hi, bits=bits).to_json()


class ReceiptAdversaryTests(unittest.TestCase):
    def setUp(self):
        self.plan = {
            "research_scope": {
                "A": {"L": "1/512", "K": [0], "precision_bits": 16},
                "B": {
                    "physical_Q": [13],
                    "successor_K": [3],
                    "parities": ["even"],
                    "segments_per_cell": 1,
                    "precision_bits": 16,
                },
                "C": {
                    "L": [2, 3],
                    "K": [3, 4],
                    "z": [{"re": "0", "im": "1/4"}],
                    "precision_bits": 16,
                },
            },
            "numerical_receipt_scope": {
                "tracks": {
                    "A": {"precision_bits": 16},
                    "B": {"precision_bits": 16},
                    "C": {"precision_bits": 16},
                }
            },
        }
        cases = [
            {
                "id": "A",
                "track": "A",
                "observable": "lambda_min",
                "params": {"L": "1/512", "K": 0},
                "precision_bits": 16,
                "source_bounds": {"lower": "1", "upper": "2"},
                "interval": interval("1", "2", 16),
                "claimed_sign": "POSITIVE",
            },
            {
                "id": "B",
                "track": "B",
                "observable": "shell_energy",
                "params": {
                    "Q": 13, "K": 3, "N": 2, "parity": "even",
                    "segment": {"lo": 0, "hi": 1, "den": 1},
                },
                "precision_bits": 16,
                "source_bounds": {"lower": "-1", "upper": "1"},
                "interval": interval("-1", "1", 16),
                "claimed_sign": "CONTAINS_ZERO",
            },
            {
                "id": "CK",
                "track": "C",
                "observable": "successive_K_delta_abs",
                "params": {"L": 2, "K_from": 3, "K_to": 4, "z_index": 0},
                "precision_bits": 16,
                "source_bounds": {"lower": "0", "upper": "1"},
                "interval": interval("0", "1", 16),
                "claimed_sign": "CONTAINS_ZERO",
            },
            {
                "id": "CK2",
                "track": "C",
                "observable": "successive_K_delta_abs",
                "params": {"L": 3, "K_from": 3, "K_to": 4, "z_index": 0},
                "precision_bits": 16,
                "source_bounds": {"lower": "0", "upper": "1"},
                "interval": interval("0", "1", 16),
                "claimed_sign": "CONTAINS_ZERO",
            },
            {
                "id": "CL",
                "track": "C",
                "observable": "successive_L_delta_abs",
                "params": {"L_from": 2, "L_to": 3, "K": 3, "z_index": 0},
                "precision_bits": 16,
                "source_bounds": {"lower": "0", "upper": "1"},
                "interval": interval("0", "1", 16),
                "claimed_sign": "CONTAINS_ZERO",
            },
            {
                "id": "CL2",
                "track": "C",
                "observable": "successive_L_delta_abs",
                "params": {"L_from": 2, "L_to": 3, "K": 4, "z_index": 0},
                "precision_bits": 16,
                "source_bounds": {"lower": "0", "upper": "1"},
                "interval": interval("0", "1", 16),
                "claimed_sign": "CONTAINS_ZERO",
            },
        ]
        signs = {"POSITIVE": 1, "NEGATIVE": 0, "ZERO_ONLY": 0, "CONTAINS_ZERO": 5}
        self.receipt = {
            "schema_version": "RHRC-CLOSURE-NUMERICAL-RECEIPT-1.0",
            "execution_status": "SUCCESS",
            "integrity_status": "PASS",
            "research_disposition": "BOUNDED_NUMERICAL_INTERVALS_ONLY",
            "terminal_claim": "RH_OPEN",
            "source": {"commit": "a" * 40, "tree": "b" * 40},
            "plan_sha256": digest(self.plan),
            "scope_sha256": digest(self.plan["numerical_receipt_scope"]),
            "fixture_sha256": digest(self.plan["research_scope"]),
            "program_sha256": "c" * 64,
            "precision_bits": {"A": 16, "B": 16, "C": 16},
            "cases": cases,
            "summary": {"case_count": len(cases), "sign_counts": signs},
        }

    def test_valid(self):
        self.assertEqual(verify_receipt(self.receipt, self.plan)["status"], "PASS")

    def test_reject_duplicate_case(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"].append(copy.deepcopy(bad["cases"][0]))
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_missing_scope_case(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"] = bad["cases"][1:]
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_fixture_digest_mutation(self):
        bad = copy.deepcopy(self.receipt)
        bad["fixture_sha256"] = "d" * 64
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_bad_program_digest(self):
        bad = copy.deepcopy(self.receipt)
        bad["program_sha256"] = "not-a-digest"
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_parameter_swap(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][1]["params"]["Q"] = 16
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_forged_sign(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][0]["claimed_sign"] = "NEGATIVE"
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_invalid_interval(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][0]["interval"] = {"lo_num": 2, "hi_num": 1, "exp2": 0}
        with self.assertRaises(Exception):
            verify_receipt(bad, self.plan)

    def test_reject_interval_widening(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][0]["interval"] = interval("1", "3", 16)
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_interval_narrowing(self):
        bad = copy.deepcopy(self.receipt)
        bad["cases"][1]["interval"] = interval("-1/2", "1/2", 16)
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_precision_schedule_mutation(self):
        bad = copy.deepcopy(self.receipt)
        bad["precision_bits"]["A"] = 32
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)

    def test_reject_terminal_promotion(self):
        bad = copy.deepcopy(self.receipt)
        bad["terminal_claim"] = "RH_PROVED"
        with self.assertRaises(ReceiptError):
            verify_receipt(bad, self.plan)


if __name__ == "__main__":
    unittest.main()
