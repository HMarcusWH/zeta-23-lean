from __future__ import annotations

import unittest

from dual_scout import scout


class DualFirewallTests(unittest.TestCase):
    def test_dual_is_diagnostic_only(self):
        result = scout()
        self.assertEqual(result["claim_cap"], "DIAGNOSTIC_ONLY")
        self.assertFalse(result["source_derived"])
        self.assertFalse(result["theorem_authority"])
        self.assertEqual(result["terminal_claim"], "RH_OPEN")

    def test_left_inverse_reproduces_identity_on_surviving_quotient(self):
        result = scout()
        n = result["nullity"]
        product = result["dual_times_nullspace"]
        self.assertEqual(len(product), n)
        for i, row in enumerate(product):
            self.assertEqual(len(row), n)
            for j, value in enumerate(row):
                self.assertEqual(value, "1" if i == j else "0")


if __name__ == "__main__":
    unittest.main()
