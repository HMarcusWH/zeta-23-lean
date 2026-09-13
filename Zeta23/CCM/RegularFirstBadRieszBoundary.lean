import Zeta23.CCM.RegularFirstBadRieszEnergy
import Zeta23.CCM.CanonicalRieszBoundary

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04A: retained first-bad Riesz boundary

This module attaches the exact generic Riesz boundary recurrence to the same
`RegularCellMinimalNegativeEnergyCertificate` retained by #153/#157.  No new
certificate type is introduced and no arithmetic sign is assumed for the
endpoint scalar.
-/

/-- Exact Riesz-6/Riesz-7 boundary decomposition on the retained first-bad
trial. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszSix_eq_rieszSeven_sub_momentThree
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 6 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) =
      canonicalRieszSourceChannelEnergy
        c.firstBad.L 7 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
        2 * (2 * Real.pi) ^ 6 *
          canonicalPolePrimeRieszEndpointScalar c.firstBad.L 6 *
          Complex.normSq
            (centeredMoment (c.firstBad.Nstar + 1) 3
              ((EuclideanSpace.equiv
                (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
                (cubicZeroShiftTrialVector
                  c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1))))) := by
  exact canonicalRieszSourceChannelEnergy_six_eq_seven_sub_moment_three
    c.firstBad.L_pos (c.firstBad.Nstar + 1)
    (cubicZeroShiftTrialVector
      c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
      EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))
    c.trial_boundaryFlat

/-- Since the retained Riesz-6 complete channel is strictly negative, its
Riesz-7 continuation lies strictly below the exact `M_3` boundary quantity.
No sign of that boundary quantity is assumed. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszSeven_lt_momentThreeBoundary
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 7 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) <
      2 * (2 * Real.pi) ^ 6 *
        canonicalPolePrimeRieszEndpointScalar c.firstBad.L 6 *
        Complex.normSq
          (centeredMoment (c.firstBad.Nstar + 1) 3
            ((EuclideanSpace.equiv
              (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
              (cubicZeroShiftTrialVector
                c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
                EuclideanSpace ℂ
                  (Fin (2 * (c.firstBad.Nstar + 1) + 1))))) := by
  have hEq := c.rieszSix_eq_rieszSeven_sub_momentThree
  have hNeg := c.rieszSixNeg
  linarith

/-- Exact Riesz-8/Riesz-9 boundary decomposition on an even retained first-bad
trial. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszEight_eq_rieszNine_add_momentFour_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 8 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) =
      canonicalRieszSourceChannelEnergy
        c.firstBad.L 9 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) +
        2 * (2 * Real.pi) ^ 8 *
          canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
          Complex.normSq
            (centeredMoment (c.firstBad.Nstar + 1) 4
              ((EuclideanSpace.equiv
                (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
                (cubicZeroShiftTrialVector
                  c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1))))) := by
  exact canonicalRieszSourceChannelEnergy_eight_eq_nine_add_moment_four
    c.firstBad.L_pos (c.firstBad.Nstar + 1)
    (cubicZeroShiftTrialVector
      c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
      EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))
    c.trial_boundaryFlat (c.trial_evenCoefficient hp)

/-- On an even retained first-bad state, strict Riesz-8 negativity pushes the
Riesz-9 complete channel below the negative of the exact `M_4` boundary
quantity.  Again no sign of the endpoint scalar is assumed. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszNine_lt_neg_momentFourBoundary_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 9 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) <
      -(2 * (2 * Real.pi) ^ 8 *
        canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
        Complex.normSq
          (centeredMoment (c.firstBad.Nstar + 1) 4
            ((EuclideanSpace.equiv
              (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
              (cubicZeroShiftTrialVector
                c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
                EuclideanSpace ℂ
                  (Fin (2 * (c.firstBad.Nstar + 1) + 1)))))) := by
  have hEq := c.rieszEight_eq_rieszNine_add_momentFour_of_even hp
  have hNeg := c.rieszEightNeg_of_even hp
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszSix_eq_rieszSeven_sub_momentThree
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszSeven_lt_momentThreeBoundary
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszEight_eq_rieszNine_add_momentFour_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszNine_lt_neg_momentFourBoundary_of_even
