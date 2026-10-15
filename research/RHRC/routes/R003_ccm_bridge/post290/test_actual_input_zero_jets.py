"""Finite symbolic falsifiers for the actual physical-Y multiplicity jet.

SYNTHETIC_CONTROL_ONLY. The toy polynomial is not a zeta zero and does not
turn the Lean conditional nonrange theorem into an unconditional RH result.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[5]
PROOF = ROOT / "Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean"


class PhysicalYJetControls(unittest.TestCase):
    def test_proof_exports_and_real_source_are_still_present(self):
        lean = PROOF.read_text(encoding="utf-8")
        for required in (
            "theorem nativeActualInputLaplace_eventuallyEq_multiplier",
            "theorem nativeActualInputLaplace_order_of_zero",
            "theorem nativeCompletedInput_zeroJet_value",
            "theorem nativeCompletedInput_zeroJet_ne_zero",
            "theorem nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero",
            "theorem nativeCompletedInput_zeroJet_residual_lower",
            "nativeZeroJetInputMultiplier_jet",
            "iteratedDeriv_comp_add_const",
            "nativeZeroJetSourceFactor_ne_zero",
        ):
            with self.subTest(required=required):
                self.assertIn(required, lean)
        self.assertIsNone(re.search(r"^\s*(?:sorry|admit|axiom)\b", lean, re.MULTILINE))

    def test_multiplicity_and_laplace_phase(self):
        z, t = sp.symbols("z t")
        center = sp.Rational(3, 4) + sp.I * sp.Rational(2, 3)
        eps = sp.Rational(1, 8)
        w = center - eps
        R, J = sp.Rational(2, 7), sp.Rational(5, 3)
        self.assertGreater(sp.re(w), 0)
        for m in (1, 2, 3, 5):
            with self.subTest(order=m):
                # Multiplicity m of the toy zero -> order m-1 in Y.
                zeta = (t - center)**m
                Y = (-R * J * sp.diff(zeta, t)).subs(t, z + eps)
                jet = sp.diff(Y, z, m - 1).subs(z, w)
                actual_pairing = (-1)**(m-1) * jet
                expected_pairing = (-1)**m * R * J * sp.factorial(m)
                self.assertEqual(sp.simplify(actual_pairing - expected_pairing), 0)
                self.assertNotEqual(sp.simplify(actual_pairing), 0)
                self.assertEqual(sp.simplify(sp.diff(Y, z, m).subs(z, w)), 0)

    def test_wrong_shift_and_conjugation_are_detected(self):
        z, t = sp.symbols("z t")
        center = sp.Rational(3, 4) + sp.I * sp.Rational(2, 3)
        eps = sp.Rational(1, 8)
        w = center - eps
        m = 3
        F = sp.diff((t-center)**m, t)
        good = F.subs(t, z+eps)
        reversed_damping = F.subs(t, z-eps)
        conjugated = sp.diff((t-sp.conjugate(center))**m, t).subs(t,z+eps)
        self.assertEqual(sp.simplify(good.subs(z, w)), 0)
        self.assertNotEqual(sp.simplify(reversed_damping.subs(z, w)), 0)
        self.assertNotEqual(sp.simplify(conjugated.subs(z, w)), 0)


if __name__ == "__main__":
    unittest.main()
