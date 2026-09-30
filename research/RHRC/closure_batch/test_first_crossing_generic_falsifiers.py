from __future__ import annotations

import unittest

from first_crossing_generic_falsifiers import harvest


class FirstCrossingGenericFalsifierTests(unittest.TestCase):
    def test_naive_contact_laws_are_rejected(self):
        result = harvest()
        self.assertEqual(result["terminal_claim"], "RH_OPEN")
        self.assertEqual(
            result["cubic_contact"]["disposition"],
            "GENERIC_ZERO_DERIVATIVE_CROSSING_COUNTERMODEL",
        )
        self.assertEqual(
            result["singular_coupling_contact"]["disposition"],
            "GENERIC_CONTACT_DECOUPLING_NOT_A_BARRIER",
        )
        self.assertEqual(
            result["claim_cap"],
            "SYNTHETIC_GENERIC_COUNTERMODEL_ONLY",
        )


if __name__ == "__main__":
    unittest.main()
