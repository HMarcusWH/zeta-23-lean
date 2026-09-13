import Zeta23.CCM.RegularFirstBadCrossParityRiesz
import Zeta23.CCM.QuadraticNormalSourceJets

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04C: retained mixed-source/Riesz bridge

This module specializes the generic quadratic-normal mixed source jet to the
exact even shifted trial introduced in PR #161.  The same canonical trial can
therefore be read through its local seventh source jet and through the existing
complete Riesz-8/Riesz-9 boundary recurrence.

The selected first-bad parity is required only when strict shifted Riesz
negativity or the opposite-parity secular obstruction is used.  No
source-moment-to-`M4` implication, endpoint-scalar sign, simultaneous-parity
exclusion, negative-root exclusion, or RH theorem is asserted.
-/

/-- Quadratic-normal elementary source observable on the exact #161 even
shifted trial. -/
def RegularCellMinimalNegativeEnergyCertificate.evenShiftedQuadraticNormalSourceAtom
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (ω : ℝ) : ℂ :=
  quadraticNormalSourceAtom
    (c.firstBad.Nstar + 1) c.evenShiftedTrial ω

/-- The local seventh jet of the exact shifted trial is the fourth centered
moment with the canonical coefficient. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0 =
      ((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ) *
        centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial) := by
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedQuadraticNormalSourceAtom] using
    iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
      (c.firstBad.Nstar + 1) (by omega) c.evenShiftedTrial

/-- Exact complete-channel Riesz-8/Riesz-9 boundary identity on the same #161
shifted trial, rewritten through the squared seventh mixed source jet. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    2 * (2 * Real.pi) ^ 4 *
        (canonicalRieszSourceChannelEnergy
            c.firstBad.L 8 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
          canonicalRieszSourceChannelEnergy
            c.firstBad.L 9 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) =
      canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
        Complex.normSq
          (iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) := by
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedQuadraticNormalSourceAtom] using
    two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
      c.firstBad.L_pos (c.firstBad.Nstar + 1) (by omega) c.evenShiftedTrial

/-- In the retained even-selected branch, strict Riesz-8 negativity converts
the exact boundary identity into a strict order-nine upper bound by the squared
mixed seventh jet.  No sign of the endpoint scalar is used. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    2 * (2 * Real.pi) ^ 4 *
        canonicalRieszSourceChannelEnergy
          c.firstBad.L 9 (c.firstBad.Nstar + 1)
          (c.evenShiftedTrial :
            EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) <
      -(canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
        Complex.normSq
          (iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0)) := by
  have h8 := c.evenShiftedRieszEightNeg hp
  have hid := c.evenShiftedRieszEightNine_eq_mixedJetBoundary
  have hscale : 0 < 2 * (2 * Real.pi) ^ 4 := by positivity
  have hscaled :
      2 * (2 * Real.pi) ^ 4 *
          canonicalRieszSourceChannelEnergy
            c.firstBad.L 8 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 :=
    mul_neg_of_pos_of_neg hscale h8
  nlinarith

/-- Under opposite-parity goodness, the cross-parity Gamma factor itself is
nonzero.  This is a no-division consequence of the #161 nonzero odd secular
scalar and exact product identity. -/
theorem RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    crossParitySecularGamma
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg ≠ 0 := by
  have hFodd :
      cubicSecularScalar
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg ≠ 0 :=
    cubicSecularScalar_ne_zero_of_not_parityBad
      .odd c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hodd
  have htransfer := c.oddSecularScalar_eq_gamma_mul_explicitSource_of_even hp
  intro hgamma
  apply hFodd
  calc
    cubicSecularScalar
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      crossParitySecularGamma
          c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg *
        explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := htransfer
    _ = 0 := by rw [hgamma, zero_mul]

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
