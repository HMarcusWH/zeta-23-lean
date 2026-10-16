"""Exact rational four-history and boundary-partition adversarial controls.

SYNTHETIC_CONTROL_ONLY: no certified zeta-zero, D2, or X growth claim.
"""
from __future__ import annotations

import re
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
CCM = ROOT / "Zeta23/CCM"


def causal(t: int) -> Fraction:
    if t < 0:
        return Fraction(0)
    return {0: Fraction(2), 1: Fraction(3), 2: Fraction(5),
            3: Fraction(7), 4: Fraction(11), 5: Fraction(13),
            6: Fraction(17)}.get(t, Fraction(0))


def four(x: int, L: int, c: int, sigma: int, k: Fraction) -> Fraction:
    return k * (causal(x-c) + causal(c-x) +
                sigma*(causal(L-x-c) + causal(x+c-L)))


class OriginalHistoryControls(unittest.TestCase):
    def test_source_contracts_retained(self):
        signed = (CCM / "OriginalDetectorFourHistorySignedTransfer.lean").read_text()
        boundary = (CCM / "OriginalDetectorBoundaryHistorySplit.lean").read_text()
        exterior = (CCM / "NativeOriginalExteriorHistory.lean").read_text()
        self.assertIn("theorem NativeCompactPoleH2.originalSmoothFourPrimeHistories_to_actualX", signed)
        self.assertIn("def originalSmoothFourPrimeXHistories", signed)
        self.assertIn("theorem originalSmoothRightBoundary_convolution_split", boundary)
        self.assertIn("originalSmoothWeilInteriorHistory", boundary)
        self.assertIn("theorem originalNativeFourHistories_common_finite_cutoff", exterior)
        for source in (signed, boundary, exterior):
            self.assertIsNone(re.search(r"^\s*(?:sorry|admit|axiom)\b",source,re.MULTILINE))

    def test_four_signed_arguments_include_reflections_and_phase(self):
        L, c, k = 10, 2, Fraction(2, 7)
        for sigma in (-1, 1):
            for x in range(L+1):
                parts = (causal(x-c), causal(c-x),
                         causal(L-x-c), causal(x+c-L))
                self.assertEqual(four(x,L,c,sigma,k),
                                 k*(parts[0]+parts[1]+sigma*(parts[2]+parts[3])))
        self.assertNotEqual(four(1,L,c,1,k), four(1,L,c,1,k)-k*causal(c-1))
        self.assertNotEqual(four(9,L,c,1,k), four(9,L,c,1,k)-k*causal(9+c-L))
        self.assertNotEqual(four(8,L,c,-1,k), four(8,L,c,1,k))

    def test_right_boundary_preserves_nonzero_interior(self):
        L,b,s = 10,2,1
        K = lambda y: Fraction(1,1+abs(y))
        R = lambda z: Fraction(z)+Fraction(1,2)
        ys = range(-b,b+1)
        x = lambda y: L-b+s-y
        interior = lambda z: R(z) if 0 <= z <= L else Fraction(0)
        right = lambda z: R(z) if z > L else Fraction(0)
        whole = sum(K(y)*R(x(y)) for y in ys)
        partitioned = sum(K(y)*(right(x(y))+interior(x(y))) for y in ys)
        middle = sum(K(y)*interior(x(y)) for y in ys)
        self.assertEqual(whole, partitioned)
        self.assertNotEqual(middle, 0)
        self.assertNotEqual(whole, whole-middle)
        self.assertEqual(interior(L), R(L))
        self.assertEqual(right(L), 0)
        self.assertEqual(interior(0), R(0))


if __name__ == "__main__":
    unittest.main()
