import Zeta23.CCM.CrossParitySecularKernelDichotomy
import Zeta23.CCM.RegularFirstBadCrossParitySecularCompletion

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained secular budget and regular-resonant dichotomy

PR #218 proves the exact completed odd-sector secular budget at the retained
negative even root.  This module expands that budget into real nonnegative
costs, composes it with the already-proved Pair-D coercivity, and then connects
the exact #218 predecessor correction to the zero-shift kernel/range split.

On the even-selected / odd-good branch, writing

  S  = exact production source moment,
  M4 = fourth centered moment,
  C  = odd cubic-generator resolvent quadratic,
  k  = canonical kernel coordinate of the odd cubic-generator predecessor part,

we prove the denominator-free constraints

  (-lam) * ||u_-||^2 + normSq(S) * re(C) <= re(star(S) * M4),

  normSq(S) * re(C) < re(star(S) * M4),

  normSq(S) * ||k||^2 < (-lam) * re(star(S) * M4),

together with the human-readable ratio consequences

  0 <= re(C) < re(M4 / S),

  ||k||^2 < (-lam) * re(M4 / S).

Finally the exact #218 correction is packaged into the exhaustive regular or
resonant branch: either a zero-shift preimage exists, or the kernel coordinate
is nonzero and carries the exact 1/(-lam) pole.

Firewalls:
* the simultaneous odd-bad branch remains open;
* the odd-selected first-bad branch remains open;
* no sign theorem for arbitrary source vectors is asserted;
* no regular-branch signed zero-shift response for the #218 vector is asserted;
* no negative-root exclusion, finite-to-infinite closure, or RH theorem is
  claimed.
-/

private theorem re_star_mul_sub_mul_eq
    (S M C : ℂ) (hC : star C = C) :
    Complex.re (star S * (M - S * C)) =
      Complex.re (star S * M) -
        Complex.normSq S * Complex.re C := by
  have hCim : C.im = 0 := by
    have h := congrArg Complex.im hC
    simp at h
    linarith
  simp [Complex.mul_re, Complex.sub_re, Complex.normSq, hCim]
  ring

private theorem re_div_eq_re_star_mul_div_normSq
    (M S : ℂ) :
    Complex.re (M / S) =
      Complex.re (star S * M) / Complex.normSq S := by
  rw [Complex.div_re]
  simp [Complex.mul_re]
  ring

/-- Expanded retained #218 budget.  The resolvent correction appears as an
explicit nonnegative real cost rather than remaining inside one complex real
part. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularBudget_expanded_of_even_of_not_oddBad
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
    let C :=
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let uMinus :=
      cubicSecularTrialVector
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    (-c.lam) * ‖uMinus‖ ^ 2 +
        Complex.normSq S * Complex.re C ≤
      Complex.re (star S * M4) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hbudget :=
    c.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad hp hodd
  dsimp only at hbudget
  change
    (-c.lam) * ‖uMinus‖ ^ 2 ≤
      Complex.re (star S * (M4 - S * C)) at hbudget
  have hCstar :
      star C = C := by
    simpa [C] using
      (star_oddCubicGeneratorResolventQuadratic_eq
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg)
  rw [re_star_mul_sub_mul_eq S M4 C hCstar] at hbudget
  linarith

/-- Strict denominator-free form of the #218 cost: the source/M4 pairing must
strictly exceed the resolvent correction because the odd canonical trial is
nonzero and the retained shift is negative. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedResolventCost_lt_sourceMomentMomentFour_of_even_of_not_oddBad
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
    let C :=
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    Complex.normSq S * Complex.re C <
      Complex.re (star S * M4) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hexpanded :=
    c.evenShiftedCrossParitySecularBudget_expanded_of_even_of_not_oddBad
      hp hodd
  dsimp only at hexpanded
  change
    (-c.lam) * ‖uMinus‖ ^ 2 +
        Complex.normSq S * Complex.re C ≤
      Complex.re (star S * M4) at hexpanded
  have hune : uMinus ≠ 0 := by
    simpa [uMinus] using
      (cubicSecularTrialVector_ne_zero
        .odd c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg)
  have hnormpos : 0 < ‖uMinus‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hune)
  have hshiftpos : 0 < -c.lam := neg_pos.mpr c.lam_neg
  have henergypos : 0 < (-c.lam) * ‖uMinus‖ ^ 2 :=
    mul_pos hshiftpos hnormpos
  linarith

/-- Composition of #209 Pair-D coercivity with the expanded #218 secular
budget.  The same arithmetic source/M4 pairing must finance both costs. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCombinedPairDSecularBudget_of_even_of_not_oddBad
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
    let C :=
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let uMinus :=
      cubicSecularTrialVector
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    max
      (-c.lam *
        ‖euclideanEvenToOddIndexLinearMap
          (c.firstBad.Nstar + 1) c.evenShiftedTrial‖ ^ 2)
      ((-c.lam) * ‖uMinus‖ ^ 2 +
        Complex.normSq S * Complex.re C) ≤
      Complex.re (star S * M4) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  apply max_le
  · simpa [S, M4] using
      c.evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
        hp hodd
  · simpa [S, M4, C, uMinus] using
      c.evenShiftedCrossParitySecularBudget_expanded_of_even_of_not_oddBad
        hp hodd

/-- Human-readable strict source-ratio locus forced by #218. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceRatio_re_gt_resolventQuadratic_of_even_of_not_oddBad
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
    let C :=
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    0 ≤ Complex.re C ∧
      Complex.re C < Complex.re (M4 / S) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hCnonneg : 0 ≤ Complex.re C := by
    simpa [C] using
      (oddCubicGeneratorResolventQuadratic_re_nonnegative
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg)
  have hstrict :=
    c.evenShiftedResolventCost_lt_sourceMomentMomentFour_of_even_of_not_oddBad
      hp hodd
  dsimp only at hstrict
  change
    Complex.normSq S * Complex.re C <
      Complex.re (star S * M4) at hstrict
  have hSne : S ≠ 0 := by
    simpa [S] using c.explicitSourceMoment_ne_zero_of_even_of_not_oddBad hp hodd
  have hSnorm : 0 < Complex.normSq S :=
    Complex.normSq_pos.mpr hSne
  have hratio :
      Complex.re (M4 / S) =
        Complex.re (star S * M4) / Complex.normSq S :=
    re_div_eq_re_star_mul_div_normSq M4 S
  refine ⟨hCnonneg, ?_⟩
  rw [hratio]
  apply (lt_div_iff₀ hSnorm).2
  simpa [mul_comm] using hstrict

/-- Denominator-free composition of the generic kernel lower bound with the
strict retained #218 source/M4 budget. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedKernelBudget_lt_sourceMomentMomentFour_of_even_of_not_oddBad
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
    let k :=
      oddCubicGeneratorKernelPart
        c.firstBad.L c.firstBad.Nstar
    Complex.normSq S * ‖k‖ ^ 2 <
      (-c.lam) * Complex.re (star S * M4) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let k :=
    oddCubicGeneratorKernelPart c.firstBad.L c.firstBad.Nstar
  have hkbound :=
    oddCubicGeneratorKernelPart_norm_sq_le_neg_lam_mul_resolventQuadratic_re
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam_neg
  change ‖k‖ ^ 2 ≤ (-c.lam) * Complex.re C at hkbound
  have hstrict :=
    c.evenShiftedResolventCost_lt_sourceMomentMomentFour_of_even_of_not_oddBad
      hp hodd
  dsimp only at hstrict
  change
    Complex.normSq S * Complex.re C <
      Complex.re (star S * M4) at hstrict
  have hSne : S ≠ 0 := by
    simpa [S] using c.explicitSourceMoment_ne_zero_of_even_of_not_oddBad hp hodd
  have hSnorm : 0 < Complex.normSq S :=
    Complex.normSq_pos.mpr hSne
  have hshiftpos : 0 < -c.lam := neg_pos.mpr c.lam_neg
  have hleft :
      Complex.normSq S * ‖k‖ ^ 2 ≤
        Complex.normSq S * ((-c.lam) * Complex.re C) :=
    mul_le_mul_of_nonneg_left hkbound (le_of_lt hSnorm)
  have hright :
      Complex.normSq S * ((-c.lam) * Complex.re C) <
        (-c.lam) * Complex.re (star S * M4) := by
    have hm :=
      mul_lt_mul_of_pos_left hstrict hshiftpos
    nlinarith
  exact lt_of_le_of_lt hleft hright

/-- Ratio form of the retained arithmetic-versus-resonance constraint. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedKernel_norm_sq_lt_neg_lam_mul_sourceRatio_re_of_even_of_not_oddBad
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
    let k :=
      oddCubicGeneratorKernelPart
        c.firstBad.L c.firstBad.Nstar
    ‖k‖ ^ 2 <
      (-c.lam) * Complex.re (M4 / S) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let k :=
    oddCubicGeneratorKernelPart c.firstBad.L c.firstBad.Nstar
  have hkbound :=
    oddCubicGeneratorKernelPart_norm_sq_le_neg_lam_mul_resolventQuadratic_re
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam_neg
  change ‖k‖ ^ 2 ≤ (-c.lam) * Complex.re C at hkbound
  have hratio :=
    c.evenShiftedSourceRatio_re_gt_resolventQuadratic_of_even_of_not_oddBad
      hp hodd
  dsimp only at hratio
  change
    0 ≤ Complex.re C ∧
      Complex.re C < Complex.re (M4 / S) at hratio
  have hshiftpos : 0 < -c.lam := neg_pos.mpr c.lam_neg
  have hstrict :
      (-c.lam) * Complex.re C <
        (-c.lam) * Complex.re (M4 / S) :=
    mul_lt_mul_of_pos_left hratio.2 hshiftpos
  exact lt_of_le_of_lt hkbound hstrict

/-- Final retained Step-1/Step-2 endpoint: the exact #218 odd predecessor
correction is either regular at zero, with a well-defined zero-shift quadratic
response, or resonant with an exact kernel pole and the strict arithmetic
source-ratio budget. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedRegularOrResonantSourceRatioDichotomy_of_even_of_not_oddBad
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
    let k :=
      oddCubicGeneratorKernelPart
        c.firstBad.L c.firstBad.Nstar
    (∃ x₀ : intrinsicParityPredecessorSubspace .odd c.firstBad.Nstar,
      intrinsicPredecessorBlock .odd c.firstBad.L c.firstBad.Nstar x₀ =
        oddCubicGeneratorPredecessorPart c.firstBad.Nstar ∧
      ∀ x : intrinsicParityPredecessorSubspace .odd c.firstBad.Nstar,
        intrinsicPredecessorBlock .odd c.firstBad.L c.firstBad.Nstar x =
            oddCubicGeneratorPredecessorPart c.firstBad.Nstar →
          inner ℂ
              (x : euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1))
              (oddCubicGeneratorPredecessorPart c.firstBad.Nstar :
                euclideanParityBoundaryFlatSubspace .odd
                  (c.firstBad.Nstar + 1)) =
            inner ℂ
              (x₀ : euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1))
              (oddCubicGeneratorPredecessorPart c.firstBad.Nstar :
                euclideanParityBoundaryFlatSubspace .odd
                  (c.firstBad.Nstar + 1))) ∨
    (k ≠ 0 ∧
      intrinsicPredecessorKernelPart .odd
          c.firstBad.L c.firstBad.Nstar
          (shiftedIntrinsicPredecessorResolvent
            .odd c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .odd)
            c.lam c.lam_neg
            (oddCubicGeneratorPredecessorPart c.firstBad.Nstar)) =
        ((-c.lam : ℂ)⁻¹) • k ∧
      ‖k‖ ^ 2 <
        (-c.lam) * Complex.re (M4 / S)) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let k :=
    oddCubicGeneratorKernelPart c.firstBad.L c.firstBad.Nstar
  have hdich :=
    oddCubicGenerator_regular_or_resonant
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam_neg
  rcases hdich with hregular | hresonant
  · left
    have hk : k = 0 := by
      apply
        (oddCubicGeneratorKernelPart_eq_zero_iff_mem_range
          c.firstBad.L c.firstBad.Nstar).2
      rcases hregular with ⟨x₀, hx₀⟩
      exact ⟨x₀, hx₀⟩
    simpa [k] using
      oddCubicGeneratorKernelPart_zeroShiftPreimage_inner_unique
        c.firstBad.L c.firstBad.Nstar hk
  · right
    refine ⟨?_, ?_, ?_⟩
    · simpa [k] using hresonant.1
    · simpa [k] using hresonant.2
    · simpa [S, M4, k] using
        c.evenShiftedKernel_norm_sq_lt_neg_lam_mul_sourceRatio_re_of_even_of_not_oddBad
          hp hodd

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySecularBudget_expanded_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedResolventCost_lt_sourceMomentMomentFour_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCombinedPairDSecularBudget_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceRatio_re_gt_resolventQuadratic_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedKernelBudget_lt_sourceMomentMomentFour_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedKernel_norm_sq_lt_neg_lam_mul_sourceRatio_re_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRegularOrResonantSourceRatioDichotomy_of_even_of_not_oddBad
