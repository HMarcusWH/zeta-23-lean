import Zeta23.OPICARound4.AdaptiveBudget

noncomputable section
namespace Zeta23.OPICARound4
open CCM MeasureTheory
open scoped BigOperators ComplexConjugate Interval

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- The inverse of a real shift of a symmetric finite operator is symmetric
on its actual inverse domain. -/
theorem native_real_shift_inverse_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : E →ₗ[ℂ] E) (hB : B.IsSymmetric)
    (lam : ℝ) (T : E ≃ₗ[ℂ] E)
    (hT : ∀ x, T x = B x - (lam : ℂ) • x) : T.symm.toLinearMap.IsSymmetric := by
  have ht : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℂ (T x) y = inner ℂ x (T y)
    rw [hT, hT, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    change inner ℂ (B x) y - conj (lam : ℂ) * inner ℂ x y =
      inner ℂ x (B y) - (lam : ℂ) * inner ℂ x y
    rw [hB x y, Complex.conj_ofReal]
  intro x y
  have h := ht (T.symm x) (T.symm y)
  simp only [LinearEquiv.coe_toLinearMap, T.apply_symm_apply] at h
  exact h.symm

/-- The reciprocal even input representing the actual odd response. This is
distinct from the even resolvent applied to the corrected Riesz vector. -/
def nativeOddReciprocalInput {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralEvenSubspace L K :=
  (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
    ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm
      (poleNeutralCubicCompressionVector L K))

/-- Exact reciprocity, with the material minus sign and conjugation. The
original odd ray still uses the actual corrected-source Riesz input. -/
theorem native_odd_response_eq_reciprocal_source {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =
      -conj (poleNeutralCorrectedCubicSource L K (nativeOddReciprocalInput hL K hK lam hlam)) := by
  let T := poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam
  let f := poleNeutralCorrectedCubicRieszVector L K
  let g := poleNeutralCubicCompressionVector L K
  let d := (poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm g
  let z := nativeIndexAdjointInverseAdjoint hL K hK g
  have hresp : inner ℂ z (T.symm (-f)) =
      poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) := by
    dsimp only [z, nativeIndexAdjointInverseAdjoint]
    rw [LinearMap.adjoint_inner_left]
    rfl
  have hInv := @native_real_shift_inverse_symmetric (poleNeutralEvenSubspace L K)
    inferInstance (poleNeutralEven_innerProductSpace L K)
    (poleNeutralEvenCompressedCanonical L K) (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    lam T (fun _ => rfl)
  calc
    _ = inner ℂ z (T.symm (-f)) := hresp.symm
    _ = -inner ℂ d (T.symm f) := by
      dsimp only [z, d]
      rw [native_odd_inverse_adjoint_eq_inverse, map_neg]
      change inner ℂ
        ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm g).val.val
        (-(T.symm f).val.val) = -inner ℂ
          ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm g).val.val
          (T.symm f).val.val
      exact inner_neg_right _ _
    _ = -inner ℂ (T.symm d) f := congrArg Neg.neg (hInv d f).symm
    _ = -conj (poleNeutralCorrectedCubicSource L K (nativeOddReciprocalInput hL K hK lam hlam)) := by
      rw [← inner_poleNeutralCorrectedCubicRieszVector]
      change -inner ℂ (T.symm d) f = -conj (inner ℂ f (T.symm d))
      change -inner ℂ (T.symm d).val.val f.val.val =
        -conj (inner ℂ f.val.val (T.symm d).val.val)
      exact congrArg Neg.neg
        (inner_conj_symm (𝕜 := ℂ) (T.symm d).val.val f.val.val).symm

/-- The reciprocal source test represents every prime power and the full
uncompressed arch action, with the sign/conjugation required by the odd ray. -/
theorem native_odd_response_complete_arithmetic {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let v := nativeOddReciprocalInput hL K hK lam hlam
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =
      conj (inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) +
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * correctedSourceTest L K v (Real.log q)) := by
  dsimp only
  rw [native_odd_response_eq_reciprocal_source hL K hK,
    correctedSourceTest_complete_arithmetic hL K (show 2 ≤ K by omega)]
  simp only [map_sub, map_neg, map_add]
  ring

theorem actual_odd_reciprocal_adaptive_membership {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let v := nativeOddReciprocalInput hL K hK lam hlam
    correctedSourceTest L K v ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ * ‖v‖) (nativeCorrectedVariation L K v) :=
  native_source_selected_membership hL K _ le_rfl le_rfl

theorem actual_odd_reciprocal_gap_norm {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) *
      ‖nativeOddReciprocalInput hL K hK lam hlam‖ ≤
        2 * ‖poleNeutralCubicCompressionVector L K‖ := by
  have hi := @native_inverse_gap_norm (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K)
    (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam)
    (poleNeutralEvenRayleighBottom L K hL hK - lam)
    (poleNeutralEvenShiftedCanonical_coercive hL K hK lam)
    ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm (poleNeutralCubicCompressionVector L K))
  exact hi.trans (native_index_inverse_cost hL K (show 1 ≤ K by omega) _)

/-- The actual odd response has the same complete arithmetic budget evaluated
on the reciprocal input. Sign and conjugation preserve this norm bound. -/
theorem native_odd_adaptive_response_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    {U V ε B : ℝ} (hu : ‖nativeOddReciprocalInput hL K hK lam hlam‖ ≤ U)
    (hv : nativeCorrectedVariation L K (nativeOddReciprocalInput hL K hK lam hlam) ≤ V)
    (harith : UniformPrimeDiscrepancyBound L (2 * ‖correctedSourceRow L K‖ * U) V ε)
    (hmain : ‖nativeArchContinuumRow L K (nativeOddReciprocalInput hL K hK lam hlam)‖ ≤ B) :
    ‖poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)‖ ≤ B + ε := by
  rw [native_odd_response_eq_reciprocal_source hL K hK, norm_neg, Complex.norm_conj]
  exact native_adaptive_complete_budget hL K (by omega) _ hu hv harith hmain

/-- A strict independently proved arithmetic budget gives the required odd
response comparison. No such arithmetic smallness is asserted here. -/
theorem native_odd_response_lt_one_of_adaptive_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    {U V ε B : ℝ} (hu : ‖nativeOddReciprocalInput hL K hK lam hlam‖ ≤ U)
    (hv : nativeCorrectedVariation L K (nativeOddReciprocalInput hL K hK lam hlam) ≤ V)
    (harith : UniformPrimeDiscrepancyBound L (2 * ‖correctedSourceRow L K‖ * U) V ε)
    (hmain : ‖nativeArchContinuumRow L K (nativeOddReciprocalInput hL K hK lam hlam)‖ ≤ B)
    (hstrict : B + ε < 1) :
    (poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re < 1 :=
  lt_of_le_of_lt ((Complex.re_le_norm _).trans
    (native_odd_adaptive_response_budget hL K hK lam hlam hu hv harith hmain)) hstrict

end Zeta23.OPICARound4
