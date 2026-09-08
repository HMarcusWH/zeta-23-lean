import Zeta23.CCM.CrossParityTrialReconstruction

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-- Quotient coordinate of the transported even residual before canonical odd
predecessor correction. -/
theorem evenTrial_oddResidual_quotient_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let Du := evenIndexParityLinearMap (N + 1) uPlus
    intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) =
      cubicSecularScalar .even hL N hprevEven lam hlam +
        evenParityCubicDefectFunctional L (N + 1) uPlus := by
  dsimp
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Du := evenIndexParityLinearMap (N + 1) uPlus
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let c := intrinsicCubicShellPart .odd N
  let Q := intrinsicCubicQuotientCoordinate .odd N
  have hfull :=
    evenTrial_oddResidual_eq_forcing_add_shell
      hL N hN hprevEven lam hlam
  have hq := congrArg Q hfull
  have hf0 : Q (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 :=
    intrinsicCubicQuotientCoordinate_predecessor_eq_zero .odd N hN f
  have hc1 : Q (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 1 :=
    intrinsicCubicQuotientCoordinate_cubicShellPart .odd N hN
  have hQadd :
      Q ((f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        Q (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          Q ((Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) :=
    Q.map_add _ _
  have hQsmul :
      Q ((Fplus + phi) •
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        (Fplus + phi) • Q
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :=
    Q.map_smul (Fplus + phi) _
  calc
    Q (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) =
      Q ((f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := hq
    _ = Q (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          Q ((Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := hQadd
    _ = 0 + (Fplus + phi) • (1 : ℂ) := by rw [hf0, hQsmul, hc1]
    _ = Fplus + phi := by simp

/-- Main exact cross-parity secular transfer. -/
theorem cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
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
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      crossParitySecularAlpha hL N hprevOdd lam hlam *
          cubicSecularScalar .even hL N hprevEven lam hlam +
        crossParitySecularGamma hL N hprevOdd lam hlam *
          evenParityCubicDefectFunctional L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let uMinus := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let D := evenIndexParityLinearMap (N + 1)
  let Du : euclideanParityBoundaryFlatSubspace .odd (N + 1) := D uPlus
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let Fminus := cubicSecularScalar .odd hL N hprevOdd lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let Q := intrinsicCubicQuotientCoordinate .odd N
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let dW := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  have htrial :=
    cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
      hL N hN hprevEven hprevOdd lam hlam
  have hqDuResidual :=
    evenTrial_oddResidual_quotient_eq hL N hN hprevEven lam hlam
  have hRf0 :
      Q ((R f : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 := by
    exact intrinsicCubicQuotientCoordinate_predecessor_eq_zero .odd N hN (R f)
  have htrial' :
      uMinus =
        Du -
          ((R f : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    simpa [uMinus, Du, D, uPlus, R, f] using htrial
  have hresMinus :
      cubicSecularResidual .odd hL N hprevOdd lam hlam =
        (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) -
          (parityCompressedCanonical .odd L (N + 1)
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
            (lam : ℂ) •
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
    change
      parityCompressedCanonical .odd L (N + 1) uMinus -
          (lam : ℂ) • uMinus = _
    rw [htrial', map_sub, smul_sub]
    abel
  have hchi :
      Q (parityCompressedCanonical .odd L (N + 1)
            ((R f : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) = chi f := by
    rfl
  let Ares : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du
  let Bres : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    parityCompressedCanonical .odd L (N + 1)
        ((R f : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
      (lam : ℂ) •
        ((R f : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
  let Tpred : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    parityCompressedCanonical .odd L (N + 1)
      ((R f : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
  let Lpred : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    (lam : ℂ) •
      ((R f : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hQouter : Q (Ares - Bres) = Q Ares - Q Bres := Q.map_sub Ares Bres
  have hQinner : Q (Tpred - Lpred) = Q Tpred - Q Lpred := Q.map_sub Tpred Lpred
  have hQlam :
      Q Lpred = (lam : ℂ) •
        Q ((R f : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact Q.map_smul (lam : ℂ) _
  have hFminus : Fminus = Fplus + phi - chi f := by
    change Q (cubicSecularResidual .odd hL N hprevOdd lam hlam) = _
    calc
      Q (cubicSecularResidual .odd hL N hprevOdd lam hlam) =
        Q (Ares - Bres) := by
          exact congrArg Q hresMinus
      _ = Q Ares - Q Bres := hQouter
      _ = Q Ares - (Q Tpred - Q Lpred) := by
        change Q Ares - Q (Tpred - Lpred) = _
        rw [hQinner]
      _ = (Fplus + phi) - (chi f - 0) := by
        rw [hqDuResidual, hchi, hQlam, hRf0, smul_zero]
      _ = Fplus + phi - chi f := by ring
  have hf : f = Fplus • dW + phi • a := by rfl
  have hchif : chi f = Fplus * chi dW + phi * chi a := by
    calc
      chi f = chi (Fplus • dW + phi • a) := congrArg chi hf
      _ = chi (Fplus • dW) + chi (phi • a) := chi.map_add _ _
      _ = Fplus • chi dW + phi • chi a := by
        rw [chi.map_smul, chi.map_smul]
      _ = Fplus * chi dW + phi * chi a := by
        simp only [smul_eq_mul]
  change Fminus =
    (1 - chi dW) * Fplus + (1 - chi a) * phi
  rw [hFminus, hchif]
  ring

/-- The Gamma coefficient has a metric overlap interpretation involving only
the canonical odd trial vector and full odd cubic generator. -/
theorem crossParitySecularGamma_eq_trial_cubic_overlap_div
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    crossParitySecularGamma hL N hprevOdd lam hlam =
      inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (successorParityCubicVector .odd N) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let c := intrinsicCubicShellPart .odd N
  let a := oddCubicGeneratorPredecessorPart N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let u := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    successorParityCubicVector .odd N
  let cV : euclideanParityBoundaryFlatSubspace .odd (N + 1) := c
  let den := inner ℂ cV cV
  have hden : den ≠ 0 := by
    change
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) ≠ 0
    exact inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hchiInner :
      chi a =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R a : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R a : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) /
          inner ℂ cV cV
    exact
      intrinsicCubicQuotientCoordinate_eq_inner_div
        .odd N hN
        (parityCompressedCanonical .odd L (N + 1)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)))
  have hsymT :
      inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact
      (parityCompressedCanonical_isSymmetric .odd L (N + 1)
        cV
        ((R a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))).symm
  have hTcRa :
      inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    let y := parityCompressedCanonical .odd L (N + 1) cV
    have hrec := intrinsicPredecessorPart_add_shellPart .odd N y
    have hpredY : intrinsicPredecessorPart .odd N y = b := by rfl
    have hort := inner_intrinsicShell_predecessor_eq_zero
      .odd N (intrinsicShellPart .odd N y) (R a)
    calc
      inner ℂ y
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          ((intrinsicPredecessorPart .odd N y :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        inner ℂ
          ((intrinsicShellPart .odd N y : intrinsicParitySuccShell .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
          rw [← inner_add_left]
          exact congrArg
            (fun z : euclideanParityBoundaryFlatSubspace .odd (N + 1) =>
              inner ℂ z
                ((R a : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1))) hrec.symm
      _ = inner ℂ
          ((intrinsicPredecessorPart .odd N y :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hort, add_zero]
      _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hpredY]
  have hRba :
      inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    simpa [R] using
      shiftedIntrinsicPredecessorResolvent_isSymmetric
        .odd hL N hprevOdd hlam b a
  have hchi :
      chi a =
        inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
    calc
      chi a = inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := hchiInner
      _ = inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [hsymT]
      _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [hTcRa]
      _ = inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [← hRba]
  have hRaC := inner_intrinsicPredecessor_shell_eq_zero .odd N (R b) c
  have hCa := inner_intrinsicShell_predecessor_eq_zero .odd N c a
  have hg :
      g =
        (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hcoeNeg :
      (((- R b : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        - ((R b : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rfl
  have huInner :
      inner ℂ u g =
        den -
          inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    change
      inner ℂ
        (((- R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) g = _
    rw [hg, hcoeNeg]
    simp only [inner_add_left, inner_add_right, inner_neg_left]
    rw [hRaC, hCa]
    simp only [neg_zero, zero_add, sub_eq_add_neg]
    change
      - inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + den =
        den +
          - inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    ac_rfl
  change 1 - chi a = inner ℂ u g / den
  rw [hchi, huInner]
  field_simp [hden] <;> ring

/-- Source-explicit version of the exact cross-parity transfer. -/
theorem cubicSecularScalar_crossParity_source_transfer
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
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      crossParitySecularAlpha hL N hprevOdd lam hlam *
          cubicSecularScalar .even hL N hprevEven lam hlam +
        crossParitySecularGamma hL N hprevOdd lam hlam *
          evenQuadraticSourceMoment L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  rw [cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
    hL N hN hprevEven hprevOdd lam hlam]
  rw [evenParityCubicDefectFunctional_eq_evenQuadraticSourceMoment
    hL (N + 1) (by omega)
    (cubicSecularTrialVector .even hL N hprevEven lam hlam)]

/-- At an even secular root, the odd scalar is exactly overlap times the actual
canonical-source quadratic normal moment. -/
theorem cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
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
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      (inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (successorParityCubicVector .odd N) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))) *
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  rw [cubicSecularScalar_crossParity_source_transfer
    hL N hN hprevEven hprevOdd lam hlam, hroot]
  simp only [mul_zero, zero_add]
  rw [crossParitySecularGamma_eq_trial_cubic_overlap_div
    hL N hN hprevOdd lam hlam]

end Zeta23.CCM
