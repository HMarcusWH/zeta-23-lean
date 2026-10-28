import Zeta23.OPICARound4.NativeSourceBudget
import Zeta23.OPICARound4.PrimeDiscrepancyIntegral

noncomputable section
namespace Zeta23.OPICARound4
open CCM MeasureTheory Set
open scoped BigOperators Interval

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- A declared C¹ test class, fixed before the source-selected input is used.
The two budgets are amplitude and total derivative variation on the aperture. -/
def nativeAdaptiveTestClass (L A V : ℝ) : Set (ℝ → ℂ) :=
  {F | F 0 = 0 ∧ F L = 0 ∧ ∃ G : ℝ → ℂ,
    (∀ y, HasDerivAt F (G y) y) ∧ Continuous G ∧
    (∀ y ∈ Icc 0 L, ‖F y‖ ≤ A) ∧ (∫ y in (0 : ℝ)..L, ‖G y‖) ≤ V}

/-- The arithmetic obligation quantifies over the entire declared class.
It is a proposition, not an assumption stored in any native state packet. -/
def UniformPrimeDiscrepancyBound (L A V ε : ℝ) : Prop :=
  ∀ F ∈ nativeAdaptiveTestClass L A V,
    ‖(∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * F (Real.log q)) -
      (∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * F y)‖ ≤ ε

def nativeCorrectedVariation (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) : ℝ :=
  ∫ y in (0 : ℝ)..L, ‖correctedSourceTestDerivative L K u y‖

/-- Coercivity prices an actual inverse input, without hiding the gap in a
normalization or replacing the input by a unit vector. -/
theorem native_inverse_gap_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E ≃ₗ[ℂ] E) (δ : ℝ)
    (hc : ∀ x, δ * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) (g : E) :
    δ * ‖T.symm g‖ ≤ ‖g‖ := by
  have h := hc (T.symm g)
  rw [T.apply_symm_apply] at h
  have hi := (Complex.re_le_norm (inner ℂ g (T.symm g))).trans
    (norm_inner_le_norm (𝕜 := ℂ) g (T.symm g))
  by_cases hz : ‖T.symm g‖ = 0
  · rw [hz, mul_zero]; exact norm_nonneg g
  · have hp : 0 < ‖T.symm g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith)

theorem actual_even_ray_gap_norm {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) *
      ‖poleNeutralEvenShiftedRay hL K hK lam hlam‖ ≤
        2 * ‖poleNeutralCubicCompressionVector L K‖ := by
  let T := poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam
  let g := poleNeutralCubicCompressionVector L K
  have hi := @native_inverse_gap_norm (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) T
    (poleNeutralOddRayleighBottom L K hL hK - lam)
    (poleNeutralOddShiftedCanonical_coercive hL K hK lam) g
  have hd := native_index_inverse_cost hL K (show 1 ≤ K by omega) (T.symm g)
  have hp := mul_le_mul_of_nonneg_left hd (sub_pos.mpr hlam).le
  change _ * ‖(poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm (T.symm g)‖ ≤ _
  nlinarith

theorem actual_odd_resolvent_gap_norm {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) *
      ‖(poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
        (poleNeutralCorrectedCubicRieszVector L K)‖ ≤ nativeCompleteRowBudget L K :=
  (@native_inverse_gap_norm (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam)
    (poleNeutralEvenRayleighBottom L K hL hK - lam)
    (poleNeutralEvenShiftedCanonical_coercive hL K hK lam)
    (poleNeutralCorrectedCubicRieszVector L K)).trans
      (native_corrected_riesz_budget hL K (by omega))

theorem nativeCorrectedVariation_nonneg {L : ℝ} (hL : 0 ≤ L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : 0 ≤ nativeCorrectedVariation L K u :=
  intervalIntegral.integral_nonneg hL (fun _ _ => norm_nonneg _)

/-- Membership is proved for the actual input with its full physical norm. -/
theorem native_source_selected_membership {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) {U V : ℝ} (hu : ‖u‖ ≤ U)
    (hv : nativeCorrectedVariation L K u ≤ V) :
    correctedSourceTest L K u ∈
      nativeAdaptiveTestClass L (2 * ‖correctedSourceRow L K‖ * U) V := by
  refine ⟨correctedSourceTest_lower_endpoint L K u,
    correctedSourceTest_upper_endpoint hL K u, correctedSourceTestDerivative L K u,
    correctedSourceTest_hasDerivAt L K u, correctedSourceTestDerivative_continuous L K u, ?_, hv⟩
  intro y hy
  have h0 : 0 ≤ 1 - y / L := sub_nonneg.mpr ((div_le_one hL).mpr hy.2)
  have h1 : 1 - y / L ≤ 1 := sub_le_self _ (div_nonneg hy.1 hL.le)
  exact (native_source_mixed_norm K h0 h1 (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) |>.trans
      (mul_le_mul_of_nonneg_left hu (by positivity))

theorem actual_even_ray_adaptive_membership {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    let u := poleNeutralEvenShiftedRay hL K hK lam hlam
    correctedSourceTest L K u ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ * ‖u‖) (nativeCorrectedVariation L K u) :=
  native_source_selected_membership hL K _ le_rfl le_rfl

/-- Odd membership uses the even resolvent applied to the actual corrected
source Riesz vector. It does not substitute the even shifted ray. -/
theorem actual_odd_resolvent_adaptive_membership {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let u := (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
      (poleNeutralCorrectedCubicRieszVector L K)
    correctedSourceTest L K u ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ * ‖u‖) (nativeCorrectedVariation L K u) :=
  native_source_selected_membership hL K _ le_rfl le_rfl

/-- The even adaptive class can be selected using an explicit inverse-gap
amplitude bound; the derivative variation is still charged exactly. -/
theorem actual_even_ray_priced_membership {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    let u := poleNeutralEvenShiftedRay hL K hK lam hlam
    correctedSourceTest L K u ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ *
        (2 * ‖poleNeutralCubicCompressionVector L K‖ /
          (poleNeutralOddRayleighBottom L K hL hK - lam)))
      (nativeCorrectedVariation L K u) := by
  apply native_source_selected_membership hL K _ _ le_rfl
  apply (le_div_iff₀ (sub_pos.mpr hlam)).mpr
  simpa [mul_comm] using actual_even_ray_gap_norm hL K hK lam hlam

theorem actual_odd_resolvent_priced_membership {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let u := (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
      (poleNeutralCorrectedCubicRieszVector L K)
    correctedSourceTest L K u ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ *
        (nativeCompleteRowBudget L K / (poleNeutralEvenRayleighBottom L K hL hK - lam)))
      (nativeCorrectedVariation L K u) := by
  apply native_source_selected_membership hL K _ _ le_rfl
  apply (le_div_iff₀ (sub_pos.mpr hlam)).mpr
  simpa [mul_comm] using actual_odd_resolvent_gap_norm hL K hK lam hlam

/-- The exact signed continuum remainder keeps the uncompressed arch action. -/
def nativeArchContinuumRow (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) : ℂ :=
  -inner ℂ (correctedSourceRow L K)
    ((canonicalArchMatrix L K).toEuclideanLin
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) -
    ∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * correctedSourceTest L K u y

/-- Conditional arithmetic consumer. The uniform bound and continuum budget
remain explicit hypotheses, separate from the actual source-selected state. -/
theorem native_adaptive_complete_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K)
    {U V ε B : ℝ} (hu : ‖u‖ ≤ U) (hv : nativeCorrectedVariation L K u ≤ V)
    (harith : UniformPrimeDiscrepancyBound L (2 * ‖correctedSourceRow L K‖ * U) V ε)
    (hmain : ‖nativeArchContinuumRow L K u‖ ≤ B) :
    ‖poleNeutralCorrectedCubicSource L K u‖ ≤ B + ε := by
  have hd := harith (correctedSourceTest L K u)
    (native_source_selected_membership hL K u hu hv)
  have heq : poleNeutralCorrectedCubicSource L K u = nativeArchContinuumRow L K u -
      ((∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * correctedSourceTest L K u (Real.log q)) -
        ∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * correctedSourceTest L K u y) := by
    rw [correctedSourceTest_complete_arithmetic hL K hK]
    unfold nativeArchContinuumRow
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hmain hd)

end Zeta23.OPICARound4
