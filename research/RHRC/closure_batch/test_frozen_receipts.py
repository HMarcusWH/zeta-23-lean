from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

import check_frozen_receipts as checker
import freeze_receipts as freezer


class FrozenReceiptContractTests(unittest.TestCase):
    def test_expected_sets_match(self):
        self.assertEqual(set(checker.EXPECTED), set(freezer.EXPECTED))
        self.assertIn("HARVEST.json", checker.EXPECTED)
        self.assertIn("diagnostic_b_schur_arb.json", checker.EXPECTED)

    def test_disposition_ignores_raw_float_payload(self):
        a = {
            "schema_version": "X",
            "classification": "C",
            "terminal_claim": "RH_OPEN",
            "theorem_promotion": False,
            "rh_claim": False,
            "x": 1.0,
        }
        b = dict(a, x=1.0000000000001)
        self.assertEqual(checker.disposition(a), checker.disposition(b))

    def test_disposition_detects_claim_drift(self):
        a = {"schema_version": "X", "terminal_claim": "RH_OPEN"}
        b = {"schema_version": "X", "terminal_claim": "RH_PROVED"}
        self.assertNotEqual(checker.disposition(a), checker.disposition(b))


if __name__ == "__main__":
    unittest.main()
