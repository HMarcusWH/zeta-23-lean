import Zeta23.CCM.CubicSecularGoodSectorMargin
import Zeta23.CCM.CrossParitySecularTransfer
import Zeta23.CCM.ParitySourceMomentFourRigidity

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: exact cross-parity secular completion

This module completes the retained negative-root cross-parity transfer at the
same shift.  The correction is the odd negative-shift resolvent quadratic value
of the predecessor part of the full odd cubic generator.

At an even secular root the odd trial is reconstructed as

  u_- = D u_+ - S R_- a,

and the denominator-free completed scalar identity is

  star(F_-) * <c_-,c_->
    =
  star(S) * (M4 - S*C),

where C = <R_- a,a>.  No division by S, Gamma, or C is used.  No negative-root
exclusion or RH theorem is claimed.
-/

/-- Odd cubic-generator resolvent quadratic value at a safe negative shift. -/
def oddCubicGeneratorResolventQuadratic
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) : ℂ :=
  inner ℂ
    ((shiftedIntrinsicPredecessorResolvent
        .odd hL N hprevOdd lam hlam
        (oddCubicGeneratorPredecessorPart N) :
      intrinsicParityPredecessorSubspace .odd N) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1))
    (oddCubicGeneratorPredecessorPart N :
      euclideanParityBoundaryFlatSubspace .odd (N + 1))

/-- The odd cubic-generator resolvent quadratic value is real. -/
theorem star_oddCubicGeneratorResolventQuadratic_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star (oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam) =
      oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam := by
  exact star_inner_resolvent_eq
    .odd hL N hprevOdd hlam (oddCubicGeneratorPredecessorPart N)

/-- The odd cubic-generator resolvent correction is nonnegative. -/
theorem oddCubicGeneratorResolventQuadratic_re_nonnegative
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    0 ≤ Complex.re
      (oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam) := by
  exact re_inner_resolvent_nonnegative
    .odd hL N hprevOdd hlam (oddCubicGeneratorPredecessorPart N)

/-- Quantitative lower bound on the odd cubic-generator correction. -/
theorem neg_lam_mul_oddCubicGeneratorResolvent_norm_sq_le
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (-lam) *
        ‖shiftedIntrinsicPredecessorResolvent
          .odd hL N hprevOdd lam hlam
          (oddCubicGeneratorPredecessorPart N)‖ ^ 2 ≤
      Complex.re
        (oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam) := by
  exact neg_mul_norm_sq_resolvent_le_re_inner
    .odd hL N hprevOdd hlam (oddCubicGeneratorPredecessorPart N)

/-- The correction vanishes exactly in the genuinely degenerate case where the
odd cubic generator has no predecessor component. -/
theorem oddCubicGeneratorResolventQuadratic_eq_zero_iff
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam = 0 ↔
      oddCubicGeneratorPredecessorPart N = 0 := by
  let a := oddCubicGeneratorPredecessorPart N
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  constructor
  · intro hC
    have hco :=
      neg_mul_norm_sq_resolvent_le_re_inner
        .odd hL N hprevOdd hlam a
    change (-lam) * ‖R a‖ ^ 2 ≤
      Complex.re
        (oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam) at hco
    rw [hC] at hco
    simp only [map_zero, Complex.zero_re] at hco
    have hRa : R a = 0 := by
      have hnormnonneg : 0 ≤ ‖R a‖ := norm_nonneg _
      have hlampos : 0 < -lam := neg_pos.mpr hlam
      have hnormzero : ‖R a‖ = 0 := by
        by_contra hne
        have hnormpos : 0 < ‖R a‖ :=
          lt_of_le_of_ne hnormnonneg (Ne.symm hne)
        have hsqpos : 0 < ‖R a‖ ^ 2 := pow_pos hnormpos 2
        have hprodpos : 0 < (-lam) * ‖R a‖ ^ 2 :=
          mul_pos hlampos hsqpos
        exact (not_lt_of_ge hco) hprodpos
      exact norm_eq_zero.mp hnormzero
    have hright :=
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        .odd hL N hprevOdd lam hlam a
    rw [show R a = 0 by exact hRa, map_zero] at hright
    exact hright.symm
  · intro ha
    rw [ha]
    have hR0 :
        shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam
            (0 : intrinsicParityPredecessorSubspace .odd N) = 0 :=
      map_zero _
    change
      inner ℂ
          ((shiftedIntrinsicPredecessorResolvent
              .odd hL N hprevOdd lam hlam
              (0 : intrinsicParityPredecessorSubspace .odd N) :
            intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (0 : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0
    rw [hR0]
    simp

/-- At an even secular root the transported predecessor forcing collapses to
the source defect times the odd cubic-generator predecessor part. -/
theorem crossParityPredecessorForcing_eq_source_smul_generator_of_even_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0) :
    crossParityPredecessorForcing hL N hprevEven lam hlam =
      evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam) •
        oddCubicGeneratorPredecessorPart N := by
  rw [crossParityPredecessorForcing]
  rw [hroot, zero_smul, zero_add]
  rw [evenParityCubicDefectFunctional_eq_evenQuadraticSourceMoment
    hL (N + 1) (by omega)
    (cubicSecularTrialVector .even hL N hprevEven lam hlam)]

/-- Root-specialized reconstruction of the odd canonical trial. -/
theorem cubicSecularTrialVector_odd_eq_evenIndex_sub_source_resolvent_of_even_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let S := evenQuadraticSourceMoment L (N + 1) uPlus
    cubicSecularTrialVector .odd hL N hprevOdd lam hlam =
      evenIndexParityLinearMap (N + 1) uPlus -
        S •
          ((shiftedIntrinsicPredecessorResolvent
              .odd hL N hprevOdd lam hlam
              (oddCubicGeneratorPredecessorPart N) :
            intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let S := evenQuadraticSourceMoment L (N + 1) uPlus
  change
    cubicSecularTrialVector .odd hL N hprevOdd lam hlam =
      evenIndexParityLinearMap (N + 1) uPlus -
        S •
          ((shiftedIntrinsicPredecessorResolvent
              .odd hL N hprevOdd lam hlam
              (oddCubicGeneratorPredecessorPart N) :
            intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
  rw [cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
    hL N hN hprevEven hprevOdd lam hlam]
  rw [crossParityPredecessorForcing_eq_source_smul_generator_of_even_root
    hL N hN hprevEven lam hlam hroot]
  rw [map_smul]
  simp only [Submodule.coe_smul]

/-- Completed metric overlap of the odd trial with the odd cubic generator. -/
theorem inner_oddCubicGenerator_oddTrial_eq_source_completion_of_even_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let S := evenQuadraticSourceMoment L (N + 1) uPlus
    let M4 :=
      centeredMoment (N + 1) 4
        (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
    inner ℂ
        (successorParityCubicVector .odd N)
        (cubicSecularTrialVector .odd hL N hprevOdd lam hlam) =
      M4 - S *
        oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let S := evenQuadraticSourceMoment L (N + 1) uPlus
  let M4 :=
    centeredMoment (N + 1) 4
      (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
  change
    inner ℂ
        (successorParityCubicVector .odd N)
        (cubicSecularTrialVector .odd hL N hprevOdd lam hlam) =
      M4 - S *
        oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    successorParityCubicVector .odd N
  let a := oddCubicGeneratorPredecessorPart N
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  have hrecon :=
    cubicSecularTrialVector_odd_eq_evenIndex_sub_source_resolvent_of_even_root
      hL N hN hprevEven hprevOdd lam hlam hroot
  change
    cubicSecularTrialVector .odd hL N hprevOdd lam hlam =
      evenIndexParityLinearMap (N + 1) uPlus -
        S •
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) at hrecon
  have hM4 :
      inner ℂ g (evenIndexParityLinearMap (N + 1) uPlus) =
        centeredMoment (N + 1) 4
          (evenBoundaryFlatRawCoefficients (N + 1) uPlus) := by
    simpa [g, successorParityCubicVector, evenIndexParityLinearMap] using
      inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour
        (N + 1) uPlus
  have hgdecomp :=
    oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hshell :
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((R a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 :=
    inner_intrinsicShell_predecessor_eq_zero .odd N
      (intrinsicCubicShellPart .odd N) (R a)
  have hgR :
      inner ℂ g
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam := by
    rw [show g =
      (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) by
      simpa [g, a] using hgdecomp]
    rw [inner_add_left, hshell, add_zero]
    have hsym :=
      shiftedIntrinsicPredecessorResolvent_isSymmetric
        .odd hL N hprevOdd hlam a a
    simpa [oddCubicGeneratorResolventQuadratic, R] using hsym.symm
  have hsmul :
      inner ℂ g
          (S •
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        S *
          inner ℂ g
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    change
      inner ℂ
          (g : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (S •
            (((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        S *
          inner ℂ
            (g : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
            (((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
    rw [inner_smul_right]
  rw [hrecon, inner_sub_right, hM4, hsmul, hgR]

/-- Denominator-free exact completed odd secular identity at an even root. -/
theorem star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let S := evenQuadraticSourceMoment L (N + 1) uPlus
    let M4 :=
      centeredMoment (N + 1) 4
        (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
    star (cubicSecularScalar .odd hL N hprevOdd lam hlam) *
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      star S *
        (M4 - S *
          oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let S := evenQuadraticSourceMoment L (N + 1) uPlus
  let M4 :=
    centeredMoment (N + 1) 4
      (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
  change
    star (cubicSecularScalar .odd hL N hprevOdd lam hlam) *
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      star S *
        (M4 - S *
          oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam)
  let den :=
    inner ℂ
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hden : den ≠ 0 := by
    exact inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have htransfer :=
    cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
      hL N hN hprevEven hprevOdd lam hlam hroot
  change
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      (inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (successorParityCubicVector .odd N) / den) * S at htransfer
  have hoverlap :=
    inner_oddCubicGenerator_oddTrial_eq_source_completion_of_even_root
      hL N hN hprevEven hprevOdd lam hlam hroot
  change
    inner ℂ
        (successorParityCubicVector .odd N)
        (cubicSecularTrialVector .odd hL N hprevOdd lam hlam) =
      M4 - S *
        oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam at hoverlap
  have hdenStar : star den = den := by
    simp [den]
  have hstarTransfer := congrArg (starRingEnd ℂ) htransfer
  simp only [map_mul, map_div, hdenStar] at hstarTransfer
  have hinnerStar :
      star
        (inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (successorParityCubicVector .odd N)) =
        M4 - S *
          oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam := by
    calc
      star
          (inner ℂ
            (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
            (successorParityCubicVector .odd N)) =
        inner ℂ
          (successorParityCubicVector .odd N)
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam) := by simp
      _ = _ := hoverlap
  rw [hstarTransfer, hinnerStar]
  field_simp [hden]
  ring

/-- Good odd successor sector: the exact completed source side must pay the
whole negative shift of the odd canonical trial. -/
theorem neg_lam_mul_oddTrial_norm_sq_le_completedSource_of_even_root_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0)
    (hodd : ¬ ParityBad .odd L (N + 1)) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let S := evenQuadraticSourceMoment L (N + 1) uPlus
    let M4 :=
      centeredMoment (N + 1) 4
        (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
    (-lam) *
        ‖cubicSecularTrialVector .odd hL N hprevOdd lam hlam‖ ^ 2 ≤
      Complex.re
        (star S *
          (M4 - S *
            oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam)) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let S := evenQuadraticSourceMoment L (N + 1) uPlus
  let M4 :=
    centeredMoment (N + 1) 4
      (evenBoundaryFlatRawCoefficients (N + 1) uPlus)
  change
    (-lam) *
        ‖cubicSecularTrialVector .odd hL N hprevOdd lam hlam‖ ^ 2 ≤
      Complex.re
        (star S *
          (M4 - S *
            oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam))
  have hmargin :=
    neg_lam_mul_cubicSecularTrialVector_norm_sq_le_shellPairing
      .odd hL N hN hprevOdd lam hlam hodd
  have hcompletion :=
    star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root
      hL N hN hprevEven hprevOdd lam hlam hroot
  change
    star (cubicSecularScalar .odd hL N hprevOdd lam hlam) *
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      star S *
        (M4 - S *
          oddCubicGeneratorResolventQuadratic hL N hprevOdd lam hlam)
      at hcompletion
  rw [hcompletion] at hmargin
  exact hmargin

end Zeta23.CCM

#print axioms Zeta23.CCM.oddCubicGeneratorResolventQuadratic_re_nonnegative
#print axioms Zeta23.CCM.oddCubicGeneratorResolventQuadratic_eq_zero_iff
#print axioms Zeta23.CCM.inner_oddCubicGenerator_oddTrial_eq_source_completion_of_even_root
#print axioms Zeta23.CCM.star_cubicSecularScalar_odd_mul_shellInner_eq_source_completion_of_even_root
#print axioms Zeta23.CCM.neg_lam_mul_oddTrial_norm_sq_le_completedSource_of_even_root_of_not_oddBad
