#!/usr/bin/env python3
"""Zero-third-party-dependency exact checks for the post-300 K5 frame."""
import unittest

from post300_k5_mixed_source import (
    K, CENTER, ODD, F, center, shift, moment, gram_poly, exact_geometry
)


class K5ParityQuotientTests(unittest.TestCase):
    def test_even_quartic_moments(self):
        for r in (0, 2, 4, 6):
            self.assertEqual(moment(center, r), 0)

    def test_odd_quartic_moments(self):
        def odd(n):
            return F(0) if n == 0 else (ODD[abs(n)] if n > 0 else -ODD[abs(n)])
        for r in (1, 3, 5, 7):
            self.assertEqual(moment(odd, r), 0)

    def test_moment_shift_identity(self):
        def odd(n):
            return F(0) if n == 0 else (ODD[abs(n)] if n > 0 else -ODD[abs(n)])
        for r in range(9):
            self.assertEqual(moment(shift, r), moment(odd, r+1))

    def test_center_quotient_and_parity(self):
        self.assertEqual(center(0), 1)
        self.assertEqual(shift(0), 0)
        for n in range(-K, K+1):
            self.assertEqual(center(n), center(-n))
            self.assertEqual(shift(n), shift(-n))

    def test_exact_gram(self):
        e = exact_geometry()
        p = e["gram_polynomials_ascending_beta"]
        self.assertEqual(p["12"], ["-21208/7", "-38896/35", "-1144/7"])
        self.assertEqual(p["11"], ["1916860", "458744", "37180"])
        self.assertTrue(e["gram_determinant_coefficientwise_positive"])

    def test_lift_invariance_exact(self):
        # H acts in frame [T_5 v, e]. Shift e by t*T_5 v.
        for a, b, c, t in [(F(2), F(3), F(5), F(7,13)),
                            (F(1,17), F(-23), F(2), F(-8,9))]:
            original = c - b*b/a
            new_b = b+t*a
            new_c = c+2*t*b+t*t*a
            self.assertEqual(original, new_c-new_b*new_b/a)

    def test_generic_hermitian_countermodel(self):
        # Arbitrary symmetric 2x2 source cannot force a positive quotient.
        a, b, c = F(1), F(2), F(1)
        self.assertLess(c-b*b/a, 0)


if __name__ == "__main__":
    unittest.main()
