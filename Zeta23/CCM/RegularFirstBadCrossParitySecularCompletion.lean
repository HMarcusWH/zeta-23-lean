import Zeta23.CCM.CrossParitySecularCompletion
import Zeta23.CCM.RegularFirstBadPairDCoercivity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained cross-parity secular completion

Specialization of the generic completed cross-parity secular identity to the
exact even shifted first-bad trial.  On the odd-good branch the same retained
state now satisfies both the Pair-D transported-energy budget and the completed
odd-secular budget.

The simultaneous odd-bad branch and odd-selected branch remain open. No
negative-root exclusion, finite-to-infinite closure, or RH theorem is asserted.
-/

/-- Odd-sector shell-scaled secular orientation is strictly positive on the
retained even-selected, odd-good branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddSecularShellPairing_pos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 <
      Complex.re
        (star
            (cubicSecularScalar
              .odd c.firstBad.L_pos c.firstBad.Nstar
              (c.firstBad.predecessorNonnegative_anyParity .odd)
              c.lam c.lam_neg) *
          inner ℂ
            (intrinsicCubicShellPart .odd c.firstBad.Nstar :
              euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1))
            (intrinsicCubicShellPart .odd c.firstBad.Nstar :
              euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1))) := by
  exact
    cubicSecularScalar_shellPairing_pos_of_not_parityBad
      .odd c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hodd

/-- The cross-parity Gamma factor cannot vanish on the retained even-root,
odd-good branch. No division by Gamma is used. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.crossParitySecularGamma_ne_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    crossParitySecularGamma
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg ≠ 0 := by
  have hFpos := c.oddSecularShellPairing_pos_of_even_of_not_oddBad hp hodd
  have hFne :
      cubicSecularScalar
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg ≠ 0 := by
    intro hF
    rw [hF] at hFpos
    simp at hFpos
  have htransfer := c.oddSecularScalar_eq_gamma_mul_explicitSource_of_even hp
  intro hgamma
  apply hFne
  rw [htransfer, hgamma, zero_mul]

/-- Exact denominator-free completed secular identity on the retained even
negative-root trial, rewritten with the explicit canonical source moment. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularCompletion
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let M4 :=
      centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial)
    star
        (cubicSecularScalar
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg) *
      inner ℂ
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1)) =
      star S *
        (M4 - S *
          oddCubicGeneratorResolventQuadratic
            c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .odd)
            c.lam c.lam_neg) := by
  dsimp
  have hroot := c.evenSecularRoot_of_even hp
  have hcompletion :=
    star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hroot
  have hsource :=
    evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
      c.firstBad.L_pos (c.firstBad.Nstar + 1) c.evenShiftedTrial
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial, hsource]
    using hcompletion

/-- Retained completed odd-secular budget on the odd-good branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let M4 :=
      centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial)
    (-c.lam) *
        ‖cubicSecularTrialVector
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg‖ ^ 2 ≤
      Complex.re
        (star S *
          (M4 - S *
            oddCubicGeneratorResolventQuadratic
              c.firstBad.L_pos c.firstBad.Nstar
              (c.firstBad.predecessorNonnegative_anyParity .odd)
              c.lam c.lam_neg)) := by
  dsimp
  have hroot := c.evenSecularRoot_of_even hp
  have hbudget :=
    neg_lam_mul_oddTrial_norm_sq_le_completedSource_of_even_root_of_not_oddBad
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hroot hodd
  have hsource :=
    evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
      c.firstBad.L_pos (c.firstBad.Nstar + 1) c.evenShiftedTrial
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial, hsource]
    using hbudget

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddSecularShellPairing_pos_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.crossParitySecularGamma_ne_zero_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularCompletion
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad
