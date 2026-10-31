import Zeta23.OPICARound4.GroundArithmetic
import Zeta23.OPICARound3.CofinalSimultaneousNegative

noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Absolute energy is attached to this actual eigenmode, with its physical
norm. It is not transferred to a reciprocal input. -/
theorem native_even_eigen_absolute_energy (L : ℝ) (K : ℕ) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) u.val.val).re =
      lam * ‖u‖ ^ 2 := by
  rw [← even_absolute_energy_anchor, hu]
  exact re_inner_ofReal_smul_self lam u

theorem native_odd_eigen_absolute_energy (L : ℝ) (K : ℕ) (lam : ℝ)
    (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin w.val.val) w.val.val).re =
      lam * ‖w‖ ^ 2 := by
  rw [← odd_absolute_energy_anchor, hw]
  exact re_inner_ofReal_smul_self lam w

/-- Every field is tied definitionally to the canonical source at this L,K.
These are necessary conditions; no independent closing bound is assumed. -/
structure NativeStrictEvenGroundConstraints {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : Prop where
  strict : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK
  even_negative : poleNeutralEvenRayleighBottom L K hL hK < 0
  odd_negative : poleNeutralOddRayleighBottom L K hL hK < 0
  eigen :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) strict
    r ≠ 0 ∧ poleNeutralEvenCompressedCanonical L K r =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • r
  absolute_energy :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) strict
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin r.val.val) r.val.val).re =
      poleNeutralEvenRayleighBottom L K hL hK * ‖r‖ ^ 2
  arithmetic :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) strict
    poleNeutralCorrectedCubicSource L K r = 1 ∧
      nativeSignedPrimeDiscrepancy L K r = nativeArchContinuumRow L K r - 1 ∧
      nativeGroundPrimePairing L K r = -1 - nativeGroundArchPairing L K r ∧
      ‖1 + nativeGroundArchPairing L K r‖ ≤
        nativePrimeConcentrationBudget L K (correctedSourceRow L K) r.val.val
  budget :
    poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2
  moment :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) strict
    (poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK) *
      ‖poleNeutralIndexLinearMap hL K r‖ ^ 2 ≤
        (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re ∧
    0 < (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re

/-- The odd eigenray carries energy; its distinct reciprocal even input
carries the corrected-row arithmetic. Their exact relation is retained. -/
structure NativeStrictOddGroundConstraints {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : Prop where
  strict : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK
  even_negative : poleNeutralEvenRayleighBottom L K hL hK < 0
  odd_negative : poleNeutralOddRayleighBottom L K hL hK < 0
  eigen :
    let w := poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) strict
    w ≠ 0 ∧ poleNeutralOddCompressedCanonical L K w =
      (poleNeutralOddRayleighBottom L K hL hK : ℂ) • w ∧
      poleNeutralCubicPairingFunctional L K w = 1
  absolute_energy :
    let w := poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) strict
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin w.val.val) w.val.val).re =
      poleNeutralOddRayleighBottom L K hL hK * ‖w‖ ^ 2
  reciprocity :
    poleNeutralCubicPairingFunctional L K
      (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) strict) =
      -star (poleNeutralCorrectedCubicSource L K
        (nativeOddReciprocalInput hL K hK (poleNeutralOddRayleighBottom L K hL hK) strict))
  arithmetic :
    let v := nativeOddReciprocalInput hL K hK (poleNeutralOddRayleighBottom L K hL hK) strict
    poleNeutralCorrectedCubicSource L K v = -1 ∧
      nativeSignedPrimeDiscrepancy L K v = nativeArchContinuumRow L K v + 1 ∧
      nativeGroundPrimePairing L K v = 1 - nativeGroundArchPairing L K v ∧
      ‖1 - nativeGroundArchPairing L K v‖ ≤
        nativePrimeConcentrationBudget L K (correctedSourceRow L K) v.val.val
  budget :
    poleNeutralEvenRayleighBottom L K hL hK - poleNeutralOddRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ -
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2

/-- The equality branch retains both singular kernels and every complement
response. No simplicity, nonvanishing source or strict-gap inverse is assumed. -/
structure NativeTiedGroundConstraints {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : Prop where
  equal_bottom : poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK
  negative : poleNeutralEvenRayleighBottom L K hL hK < 0
  shifted_positive :
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)) ∧
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK))
  even : ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
    poleNeutralEvenCompressedCanonical L K u = (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u ∧
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) u.val.val).re =
      poleNeutralEvenRayleighBottom L K hL hK * ‖u‖ ^ 2 ∧
    poleNeutralCorrectedCubicSource L K u •
      poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCubicCompressionVector L K) = 0 ∧
    ∃ hr : poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K ∈
        LinearMap.range (poleNeutralOddShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)),
      poleNeutralIndexLinearMap hL K u =
        (LinearMap.ker (poleNeutralOddShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK))).starProjection
          (poleNeutralIndexLinearMap hL K u) +
        poleNeutralOddKernelComplementResponse L K (poleNeutralEvenRayleighBottom L K hL hK)
          (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) hr
  odd : ∃ w : poleNeutralOddSubspace L K, w ≠ 0 ∧
    poleNeutralOddCompressedCanonical L K w = (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • w ∧
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin w.val.val) w.val.val).re =
      poleNeutralEvenRayleighBottom L K hL hK * ‖w‖ ^ 2 ∧
    -poleNeutralCubicPairingFunctional L K w •
      poleNeutralEvenShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCorrectedCubicRieszVector L K) = 0 ∧
    ∃ hr : -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K ∈
        LinearMap.range (poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)),
      (poleNeutralIndexLinearMap hL K).adjoint w =
        (LinearMap.ker (poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK))).starProjection
          ((poleNeutralIndexLinearMap hL K).adjoint w) +
        poleNeutralEvenKernelComplementResponse L K (poleNeutralEvenRayleighBottom L K hL hK)
          (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) hr

def NativeJointGroundConstraints {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : Prop :=
  NativeStrictEvenGroundConstraints hL K hK ∨
    NativeStrictOddGroundConstraints hL K hK ∨ NativeTiedGroundConstraints hL K hK

theorem native_tied_ground_constraints {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (ht : poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK)
    (hn : poleNeutralEvenRayleighBottom L K hL hK < 0) : NativeTiedGroundConstraints hL K hK := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  obtain ⟨w, hw0, hw⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K hK
  rw [← ht] at hw
  refine ⟨ht, hn, poleNeutral_tied_complements_positive hL K hK ht, ?_, ?_⟩
  · exact ⟨u, hu0, hu, native_even_eigen_absolute_energy L K _ u hu,
      poleNeutral_even_eigen_shifted_kernel_compatibility hL K hK _ u hu,
      (poleNeutral_tied_complementary_response hL K hK _).1 u hu⟩
  · exact ⟨w, hw0, hw, native_odd_eigen_absolute_energy L K _ w hw,
      poleNeutral_odd_eigen_shifted_kernel_compatibility hL K hK _ w hw,
      (poleNeutral_tied_complementary_response hL K hK _).2 w hw⟩

/-- Exhaustive join at the actual common cutoff. No quartic cutoff, deep
selector simplicity or common exponential depth is imported here. -/
theorem joint_ground_constraints_of_both_negative {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
    NativeJointGroundConstraints hL K hK := by
  obtain ⟨ue, hue⟩ := hboth.1
  obtain ⟨uo, huo⟩ := hboth.2
  obtain ⟨_, _, _, _, hbe⟩ := even_negative_witness_ground hL K hK ue hue
  obtain ⟨_, _, _, _, hbo⟩ := odd_negative_witness_ground hL K hK uo huo
  rcases lt_trichotomy (poleNeutralEvenRayleighBottom L K hL hK)
    (poleNeutralOddRayleighBottom L K hL hK) with hs | hs | hs
  · left
    have hr := actual_even_ground_ray_facts hL K hK hs
    exact ⟨hs, hbe, hbo, ⟨hr.1, hr.2.1⟩,
      native_even_eigen_absolute_energy L K _ _ hr.2.1,
      actual_even_ground_signed_discrepancy hL K hK hs,
      actual_even_ground_signed_budget_feasibility hL K hK hs,
      actual_even_ground_ray_moment_feasibility hL K hK hs⟩
  · exact Or.inr (Or.inr (native_tied_ground_constraints hL K hK hs hbe))
  · right; left
    have hw := actual_odd_ground_ray_facts hL K hK hs
    exact ⟨hs, hbe, hbo, hw, native_odd_eigen_absolute_energy L K _ _ hw.2.1,
      native_odd_response_eq_reciprocal_source hL K hK _ hs,
      actual_odd_ground_reciprocal_discrepancy hL K hK hs,
      actual_odd_ground_signed_budget_feasibility hL K hK hs⟩

/-- An off-line zero would satisfy all these same-source constraints at
cofinally large common apertures. This is not an independent exclusion. -/
theorem cofinally_joint_ground_constraints_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ ∃ hL : 0 < L, ∃ K : ℕ, ∃ hK : 3 ≤ K,
      BothNeutralNegative L K ∧ NativeJointGroundConstraints hL K hK := by
  obtain ⟨L, hLR, hL, K, hK, hboth⟩ :=
    cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  exact ⟨L, hLR, hL, K, hK, hboth, joint_ground_constraints_of_both_negative hL K hK hboth⟩

end Zeta23.OPICARound4
