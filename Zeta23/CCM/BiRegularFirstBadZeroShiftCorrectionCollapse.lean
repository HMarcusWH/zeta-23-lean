import Zeta23.CCM.BiRegularFirstBadZeroShiftNormalForm
import Zeta23.CCM.ZeroShiftCrossParityCorrectionCollapse

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: bi-regular one-coefficient zero-shift normal form

This module preserves the complete selected-even bi-regular zero-shift state
from the post-#222 normal form while replacing the two-coefficient
alpha/Gamma transfer by the denominator-free one-coefficient consequence of
PR #226.

The selected parity is still assumed even. No WLOG-even theorem, branch
exclusion, negative-root exclusion, or RH theorem is introduced.
-/

/-- Selected-even bi-regular retained state in denominator-free
one-coefficient form. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftOneCoefficientNormalForm_of_even
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.energy.firstBad.p = ReversalParity.even) :
    ∃ xPlus : intrinsicParityPredecessorSubspace .even c.energy.firstBad.Nstar,
      ∃ xMinus : intrinsicParityPredecessorSubspace .odd c.energy.firstBad.Nstar,
        intrinsicPredecessorBlock .even
            c.energy.firstBad.L c.energy.firstBad.Nstar xPlus =
          intrinsicShellToPredecessor .even
            c.energy.firstBad.L c.energy.firstBad.Nstar
            (intrinsicCubicShellPart .even c.energy.firstBad.Nstar) ∧
        intrinsicPredecessorBlock .odd
            c.energy.firstBad.L c.energy.firstBad.Nstar xMinus =
          intrinsicShellToPredecessor .odd
            c.energy.firstBad.L c.energy.firstBad.Nstar
            (intrinsicCubicShellPart .odd c.energy.firstBad.Nstar) ∧
        Complex.re
          (cubicZeroShiftShellResponseScalar .even
            c.energy.firstBad.L c.energy.firstBad.Nstar xPlus) < 0 ∧
        (6 : ℂ) *
            cubicZeroShiftShellResponseScalar .odd
              c.energy.firstBad.L c.energy.firstBad.Nstar xMinus =
          crossParityZeroShiftAlpha c.energy.firstBad.Nstar xMinus *
              ((6 : ℂ) *
                  cubicZeroShiftShellResponseScalar .even
                    c.energy.firstBad.L c.energy.firstBad.Nstar xPlus -
                (2 * (c.energy.firstBad.Nstar : ℂ) - 1) *
                  explicitCanonicalSourceMoment
                    c.energy.firstBad.L (c.energy.firstBad.Nstar + 1)
                    (cubicZeroShiftTrialVector .even
                      c.energy.firstBad.L c.energy.firstBad.Nstar xPlus)) +
            (2 * (c.energy.firstBad.Nstar : ℂ) + 5) *
              explicitCanonicalSourceMoment
                c.energy.firstBad.L (c.energy.firstBad.Nstar + 1)
                (cubicZeroShiftTrialVector .even
                  c.energy.firstBad.L c.energy.firstBad.Nstar xPlus) ∧
        (ParityBad .odd
            c.energy.firstBad.L (c.energy.firstBad.Nstar + 1) ↔
          Complex.re
            (cubicZeroShiftShellResponseScalar .odd
              c.energy.firstBad.L c.energy.firstBad.Nstar xMinus) < 0) := by
  obtain ⟨xPlus, xMinus, hxPlus, hxMinus, hneg, _htransfer, hbad⟩ :=
    c.exists_evenOddZeroShiftScalarNormalForm_of_even hp
  refine ⟨xPlus, xMinus, hxPlus, hxMinus, hneg, ?_, hbad⟩
  exact
    six_mul_cubicZeroShiftShellResponseScalar_crossParity_oneCoefficient
      c.energy.firstBad.L_pos c.energy.firstBad.Nstar
      c.energy.firstBad.one_le_Nstar
      xPlus hxPlus xMinus hxMinus

end Zeta23.CCM

#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftOneCoefficientNormalForm_of_even
