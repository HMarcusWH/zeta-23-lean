import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormalization
import Zeta23.CCM.OriginalDetectorOriginalPhaseL1Bounds
import Zeta23.CCM.OriginalDetectorPaddedPhaseQuantitativeRates

/-! True physical normalization and paid uniform errors for the actual padded detector. -/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

private theorem inverse_mass_error_bound {t B : ℝ}
    (ht : 0 < t) (hmass : 1 / 2 < t ^ 2) (hB : |t ^ 2 - 1| ≤ B) :
    0 < t⁻¹ ∧ t⁻¹ ≤ 2 ∧ |t⁻¹ - 1| ≤ 2 * B := by
  have ht2 : 1 / 2 < t := by nlinarith
  have hti : t⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ ht).2
    linarith
  have hfactor : |t - 1| ≤ |t ^ 2 - 1| := by
    rw [show t ^ 2 - 1 = (t - 1) * (t + 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < t + 1)]
    nlinarith [abs_nonneg (t - 1)]
  have he : t⁻¹ - 1 = (1 - t) / t := by field_simp <;> ring
  refine ⟨inv_pos.mpr ht, hti, ?_⟩
  rw [he, abs_div, abs_of_pos ht, abs_sub_comm]
  have hnonneg : 0 ≤ B := (abs_nonneg _).trans hB
  apply (div_le_iff₀ ht).2
  nlinarith [hfactor.trans hB]

def originalDetectorOriginalKernelJetSupBudget (r : ℕ) : ℝ :=
  originalDetectorLobeJetBudget UniversalSinc.fixedScale (r + 2) +
    (1 / 4 : ℝ) * originalDetectorLobeJetBudget UniversalSinc.fixedScale r

theorem fixedOriginalSincKernel_iteratedDeriv_norm_le (r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r fixedOriginalSincKernel x‖ ≤ originalDetectorOriginalKernelJetSupBudget r := by
  have he := padded_poleKilled_originalDetectorLobe UniversalSinc.fixedScale 0
  have hf := originalDetectorLobe_contDiff UniversalSinc.fixedScale_pos 0
  have hh : fixedOriginalSincKernel = Zeta23.ExceptionalZero.poleKilled
      (originalDetectorLobe UniversalSinc.fixedScale 0) := by
    rw [he]
    funext y
    simp only [fixedOriginalSincKernel, sub_zero]
  rw [hh, padded_iteratedDeriv_poleKilled_infty hf]
  refine (norm_sub_le _ _).trans ?_
  unfold originalDetectorOriginalKernelJetSupBudget
  apply add_le_add
  · simpa only [originalDetectorLobeJetBudget] using
      originalDetectorLobe_iteratedDeriv_le_gevrey UniversalSinc.fixedScale_pos (r + 2) 0 x
  · rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [originalDetectorLobeJetBudget] using
        originalDetectorLobe_iteratedDeriv_le_gevrey UniversalSinc.fixedScale_pos r 0 x) (by norm_num)

def originalDetectorOriginalPhaseJetSupBudget (r : ℕ) : ℝ :=
  2 * fixedOriginalSincTrialNormalization * originalDetectorOriginalKernelJetSupBudget r

theorem fixedOriginalSincPhaseTrial_iteratedDeriv_norm_le
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤
      originalDetectorOriginalPhaseJetSupBudget r := by
  rw [fixedOriginalSincPhaseTrial_iteratedDeriv_formula, norm_mul]
  have hη : ‖(fixedOriginalSincTrialNormalization : ℂ)‖ = fixedOriginalSincTrialNormalization := by
    simp [abs_of_pos fixedOriginalSincTrialNormalization_pos]
  have hsig : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [hη]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) fixedOriginalSincTrialNormalization_pos.le).trans ?_
  rw [norm_mul, hsig, norm_smul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hh := add_le_add (fixedOriginalSincKernel_iteratedDeriv_norm_le r (x - fixedOriginalSincLobeCenter))
    (fixedOriginalSincKernel_iteratedDeriv_norm_le r (fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter - x))
  convert mul_le_mul_of_nonneg_left hh fixedOriginalSincTrialNormalization_pos.le using 1 <;>
    unfold originalDetectorOriginalPhaseJetSupBudget <;> ring

/-- This scalar is the actual physical norm of the original-normalized
finite trial, proved through the unchanged Fourier normalization bridge. -/
def originalDetectorPaddedFinitePhysicalNorm (σ a : ℝ) (hL : 0 < fixedOriginalSincTrialAperture a) : ℝ :=
  fixedOriginalSincTrialNormalization * ‖originalDetectorPaddedFinitePhaseVector σ
    (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hL‖

def originalDetectorPaddedFinitePhysicalUnit (σ a : ℝ) (hL : 0 < fixedOriginalSincTrialAperture a) : ℝ → ℂ :=
  fun x => ((originalDetectorPaddedFinitePhysicalNorm σ a hL)⁻¹ : ℂ) *
    originalDetectorPaddedFiniteOriginalPhaseHard σ a hL x

def originalDetectorPaddedFiniteNormalizedJetErrorBudget (L : ℝ) (r : ℕ) : ℝ :=
  4 * fixedOriginalSincTrialNormalization *
      originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L r +
    2 * originalDetectorPaddedFinitePhaseMassErrorBudget 1 L * originalDetectorOriginalPhaseJetSupBudget r

theorem originalDetectorPaddedFinitePhysicalUnit_jet_error_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hL : 0 < fixedOriginalSincTrialAperture a)
    (hmass : 1 / 2 < (originalDetectorPaddedFinitePhysicalNorm σ a hL) ^ 2)
    {r : ℕ} (hr : r ≤ 2) {x : ℝ} (hx : x ∈ Icc 0 (fixedOriginalSincTrialAperture a)) :
    ‖iteratedDeriv r (originalDetectorPaddedFinitePhysicalUnit σ a hL) x -
      iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤
        originalDetectorPaddedFiniteNormalizedJetErrorBudget (fixedOriginalSincTrialAperture a) r := by
  let L := fixedOriginalSincTrialAperture a
  let t := originalDetectorPaddedFinitePhysicalNorm σ a hL
  let E := 2 * fixedOriginalSincTrialNormalization *
    originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L r
  let M := originalDetectorPaddedFinitePhaseMassErrorBudget 1 L
  let H := originalDetectorOriginalPhaseJetSupBudget r
  have hL2 : 2 ≤ L := by
    dsimp [L, fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter]
    linarith [UniversalSinc.fixedScale_pos, ha]
  have ht0 : 0 ≤ t := mul_nonneg fixedOriginalSincTrialNormalization_pos.le (norm_nonneg _)
  have ht : 0 < t := by nlinarith
  have hsame : originalDetectorPaddedFinitePhaseMassErrorBudget σ L = M := by
    have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    simp only [originalDetectorPaddedFinitePhaseMassErrorBudget, hs, abs_one, M]
  have hmasserr : |t ^ 2 - 1| ≤ M := by
    have hh := originalDetectorPaddedFinitePhase_mass_error_le hσ ha hL
    rw [hsame] at hh
    convert! hh using 1 <;> dsimp [t, originalDetectorPaddedFinitePhysicalNorm] <;> ring
  obtain ⟨hti, htupper, htdiff⟩ := inverse_mass_error_bound ht hmass hmasserr
  have hraw : ‖iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseHard σ a hL) x -
      iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤ E := by
    have hh := originalDetectorPaddedFiniteOriginalPhaseApprox_iteratedDeriv_error_le
      (UniversalSinc.fixedScale_pos.le.trans ha.le) σ r hx
    have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [hs] at hh
    have hlocal : iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseHard σ a hL) x =
        iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseApprox σ a hL) x := by
      unfold originalDetectorPaddedFiniteOriginalPhaseHard originalDetectorPaddedFiniteOriginalPhaseApprox
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
      congr 1
      apply padded_iteratedDeriv_localizedFiniteVector_eq_formula_on_interval hL
      · rw [originalDetectorPaddedFinitePhaseVector_raw]
        exact originalDetectorPaddedFinitePhaseRaw_boundaryFlat σ _ hL2
      · exact hr
      · exact hx
    rw [hlocal, norm_sub_rev]
    convert! hh using 1 <;> dsimp [E, L] <;> ring
  have hsource : ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤ H :=
    fixedOriginalSincPhaseTrial_iteratedDeriv_norm_le hσ a r x
  have hE : 0 ≤ E := (norm_nonneg _).trans hraw
  have hH : 0 ≤ H := (norm_nonneg _).trans hsource
  have hM : 0 ≤ M := (abs_nonneg _).trans hmasserr
  unfold originalDetectorPaddedFinitePhysicalUnit
  rw [iteratedDeriv_const_mul_field]
  simp only [← Complex.ofReal_inv]
  have he : ((t⁻¹ : ℝ) : ℂ) * iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseHard σ a hL) x -
      iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x =
      ((t⁻¹ : ℝ) : ℂ) * (iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseHard σ a hL) x -
        iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x) +
      ((t⁻¹ - 1 : ℝ) : ℂ) * iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x := by push_cast; ring
  change ‖((t⁻¹ : ℝ) : ℂ) * _ - _‖ ≤ _
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hti]
  have hb := add_le_add
    (mul_le_mul htupper hraw (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul htdiff hsource (norm_nonneg _) (mul_nonneg (by norm_num) hM))
  convert! hb using 1 <;> unfold originalDetectorPaddedFiniteNormalizedJetErrorBudget <;>
    dsimp [E, M, H] <;> ring

theorem originalDetectorPaddedFiniteNormalizedJetErrorBudget_mul_quarticWeight_tendsto_zero
    (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFiniteNormalizedJetErrorBudget L r *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  have ha := (originalDetectorPaddedPoleBudget_mul_quarticWeight_tendsto_zero
    UniversalSinc.fixedScale r β).const_mul (4 * fixedOriginalSincTrialNormalization)
  have hb := (originalDetectorPaddedMassBudget_mul_quarticWeight_tendsto_zero 1 β).const_mul
    (2 * originalDetectorOriginalPhaseJetSupBudget r)
  have hh := ha.add hb
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1
  ext L
  unfold originalDetectorPaddedFiniteNormalizedJetErrorBudget
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.fixedOriginalSincKernel_iteratedDeriv_norm_le
#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_iteratedDeriv_norm_le
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_jet_error_le
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteNormalizedJetErrorBudget_mul_quarticWeight_tendsto_zero
