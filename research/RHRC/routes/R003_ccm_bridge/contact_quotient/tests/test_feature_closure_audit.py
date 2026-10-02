from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from feature_closure_audit import audit_feature_closure


class FeatureClosureAuditTests(unittest.TestCase):
    def test_registered_operation_closure(self):
        receipt = audit_feature_closure()
        self.assertEqual(receipt["status"], "PASS")
        self.assertFalse(receipt["global_basis_completeness"])
        self.assertEqual(receipt["claim_cap"], "CURRENT_REGISTERED_OPERATION_CLOSURE_ONLY")
        self.assertGreaterEqual(receipt["operation_count"], 4)
        self.assertEqual(receipt["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
