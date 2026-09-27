from __future__ import annotations

import unittest

from flint import arb, arb_mat

from canonical_schur_arb import _classify


def pos(x: arb) -> bool:
    return bool(x > 0)


def neg(x: arb) -> bool:
    return bool(x < 0)


class CanonicalSchurAdversaryTests(unittest.TestCase):
    def test_negative_shell_is_failure(self):
        cls, reason = _classify(arb(-1), [arb(0)], arb_mat([[0]]), pos, neg)
        self.assertEqual(cls, "CERTIFIED_CANONICAL_DOMINATION_FAILURE")
        self.assertEqual(reason, "NEGATIVE_SHELL_ENERGY")

    def test_pair_d_singular_bad_coupling_is_detected(self):
        cls, reason = _classify(arb(0), [arb(1)], arb_mat([[0]]), pos, neg)
        self.assertEqual(cls, "SINGULAR_BAD_COUPLING")
        self.assertEqual(reason, "EXACT_ZERO_SHELL_NONZERO_COUPLING")

    def test_negative_coordinate_determinant_is_failure(self):
        cls, reason = _classify(arb(1), [arb(0)], arb_mat([[-1]]), pos, neg)
        self.assertEqual(cls, "CERTIFIED_CANONICAL_DOMINATION_FAILURE")
        self.assertEqual(reason, "NEGATIVE_COORDINATE_DETERMINANT_0")

    def test_strict_positive_schur_form_is_certificate(self):
        cls, reason = _classify(arb(1), [arb(0)], arb_mat([[2]]), pos, neg)
        self.assertEqual(cls, "CERTIFIED_CANONICAL_DOMINATION")
        self.assertEqual(reason, "STRICT_SCHUR_FORM_POSITIVE")


if __name__ == "__main__":
    unittest.main()
