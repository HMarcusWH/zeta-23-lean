import Zeta23.CCM.ParitySourceMomentFourRigidity
import Zeta23.CCM.RegularFirstBadMixedSourceRigidity

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained Pair-D source/M4 rigidity

This module specializes the generic parity/source/M4 energy identity to the
exact even shifted trial already retained by the first-bad certificate.  On the
opposite-parity-good branch the same canonical state now carries:

* a strictly positive `re (star(sourceMoment) * M4)` pairing;
* a nonzero exact production source moment;
* a nonzero fourth centered moment;
* a nonzero seventh quadratic-normal mixed source jet.

The simultaneous odd-bad branch is not excluded.  No endpoint-scalar sign,
negative-root exclusion, finite-to-infinite closure, or RH theorem is asserted.
-/

/-- The retained even shifted trial is a genuine nonzero eigenmode at the
retained negative secular root whenever the selected first-bad parity is even. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial_eigenmode_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    c.evenShiftedTrial ≠ 0 ∧
      evenCompressedCanonical c.firstBad.L (c.firstBad.Nstar + 1)
          c.evenShiftedTrial =
        (c.lam : ℂ) • c.evenShiftedTrial := by
  have hroot := c.evenSecularRoot_of_even hp
  have hne :
      cubicSecularTrialVector
          .even c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .even)
          c.lam c.lam_neg ≠ 0 :=
    cubicSecularTrialVector_ne_zero
      .even c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg
  have heig :
      parityCompressedCanonical .even c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicSecularTrialVector
            .even c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .even)
            c.lam c.lam_neg) =
        (c.lam : ℂ) •
          cubicSecularTrialVector
            .even c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .even)
            c.lam c.lam_neg :=
    (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      .even c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg).mp hroot
  change
    cubicSecularTrialVector
        .even c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .even)
        c.lam c.lam_neg ≠ 0 ∧
      parityCompressedCanonical .even c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicSecularTrialVector
            .even c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .even)
            c.lam c.lam_neg) =
        (c.lam : ℂ) •
          cubicSecularTrialVector
            .even c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .even)
            c.lam c.lam_neg
  exact ⟨hne, heig⟩

/-- Headline retained rigidity: on the odd-good branch, the exact production
source moment and fourth centered moment have strictly positive Hermitian
pairing on the same retained negative-root trial. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < Complex.re
      (star
          (explicitCanonicalSourceMoment
            c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) *
        centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial)) := by
  obtain ⟨hvne, hveig⟩ := c.evenShiftedTrial_eigenmode_of_even hp
  exact
    re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
      c.firstBad.L_pos (c.firstBad.Nstar + 1) (by omega)
      c.lam_neg hvne hveig hodd

/-- The retained fourth centered moment cannot vanish on the odd-good branch.
This uses the signed Pair-D energy identity rather than a generic implication
from source-moment nonvanishing. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial) ≠ 0 := by
  have hpos := c.evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad hp hodd
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

/-- Hence the exact #163 mixed seventh source jet is also nonzero on the
opposite-parity-good branch. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0 ≠ 0 := by
  have hM4 := c.evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad hp hodd
  have hcoeffReal : (-2 * (2 * Real.pi) ^ 6 : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 6 (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hcoeff : (((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hcoeffReal
  rw [c.evenShiftedMixedSourceSeventhJet_eq_momentFour]
  exact mul_ne_zero hcoeff hM4

/-- Pair-D fork strengthened from source-moment nonvanishing to a strict
source-moment/M4 orientation law on the odd-good branch. -/
theorem RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMomentMomentFour_re_pos_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      0 < Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) *
          centeredMoment (c.firstBad.Nstar + 1) 4
            (evenBoundaryFlatRawCoefficients
              (c.firstBad.Nstar + 1) c.evenShiftedTrial)) := by
  by_cases hodd : ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · exact Or.inr
      (c.evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad hp hodd)

/-- Fully expanded nonvanishing fork on the same retained state.  If the odd
successor is not bad, then the exact production source moment, `M4`, and the
mixed seventh jet are all simultaneously nonzero. -/
theorem RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMoment_momentFour_mixedJet_ne_zero_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      (explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0 ∧
        centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial) ≠ 0 ∧
        iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0 ≠ 0) := by
  by_cases hodd : ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · right
    exact ⟨
      c.explicitSourceMoment_ne_zero_of_even_of_not_oddBad hp hodd,
      c.evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad hp hodd,
      c.evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad hp hodd⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial_eigenmode_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMomentMomentFour_re_pos_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMoment_momentFour_mixedJet_ne_zero_of_even