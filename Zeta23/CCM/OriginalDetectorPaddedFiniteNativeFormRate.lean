import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeTransport
import Zeta23.CCM.OriginalDetectorPaddedPhaseQuantitativeRates

/-! A concrete native quadratic-form rate after true physical normalization. -/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorOriginalPhaseWeilSizeBudget : ℝ :=
  zetaInvSqZeroMass *
    (originalDetectorOriginalPhaseL1JetBudget 0 + originalDetectorOriginalPhaseL1JetBudget 2) *
    originalDetectorOriginalPhaseL1JetBudget 0

theorem fixedOriginalSincPhaseTrial_Weil_norm_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hL : 0 < fixedOriginalSincTrialAperture a) :
    ‖zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)‖ ≤
      Real.exp (fixedOriginalSincTrialAperture a) * originalDetectorOriginalPhaseWeilSizeBudget := by
  let L := fixedOriginalSincTrialAperture a
  let h := fixedOriginalSincPhaseTrial σ a
  have hsupport (x : ℝ) (hx : h x ≠ 0) : |x| ≤ L := by
    have hh := fixedOriginalSincPhaseTrial_support ha σ (subset_closure hx)
    rw [abs_of_nonneg (by linarith [hh.1] : 0 ≤ x)]
    linarith [hh.2]
  have hc : ContDiff ℝ 2 h := fixedOriginalSincPhaseTrial_contDiff σ a
  have hb := zeta_W_norm_le_commonSupport hL.le hc hc.continuous hsupport hsupport
  have h0 := fixedOriginalSincPhaseTrial_originalPhase_L1_bound hσ a 0
  have h2 := fixedOriginalSincPhaseTrial_originalPhase_L1_bound hσ a 2
  simp only [iteratedDeriv_zero] at h0
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h2
  have hM := zetaInvSqZeroMass_nonneg
  have hH0 : 0 ≤ originalDetectorOriginalPhaseL1JetBudget 0 := (integral_nonneg fun _ => norm_nonneg _).trans h0
  have hH2 : 0 ≤ originalDetectorOriginalPhaseL1JetBudget 2 := (integral_nonneg fun _ => norm_nonneg _).trans h2
  calc
    _ ≤ Real.exp L * zetaInvSqZeroMass *
        ((∫ x, ‖h x‖) + ∫ x, ‖deriv (deriv h) x‖) * (∫ x, ‖h x‖) := hb
    _ ≤ Real.exp L * zetaInvSqZeroMass *
        (originalDetectorOriginalPhaseL1JetBudget 0 + originalDetectorOriginalPhaseL1JetBudget 2) *
        originalDetectorOriginalPhaseL1JetBudget 0 := by
      gcongr
    _ = _ := by unfold originalDetectorOriginalPhaseWeilSizeBudget; ring

def originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget (L : ℝ) : ℝ :=
  2 * originalDetectorPaddedFinitePhaseWeilErrorBudget L +
    2 * originalDetectorPaddedFinitePhaseMassErrorBudget 1 L *
      (Real.exp L * originalDetectorOriginalPhaseWeilSizeBudget)

private theorem ratio_error_le {a b μ M E H : ℝ}
    (hμ : 1 / 2 < μ) (hM : |μ - 1| ≤ M) (hE : |a - b| ≤ E) (hH : |b| ≤ H) :
    |a / μ - b| ≤ 2 * E + 2 * M * H := by
  have hp : 0 < μ := by linarith
  have hinv : μ⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).2
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hH
  have hdiff : |μ⁻¹ - 1| ≤ 2 * M := by
    have he : μ⁻¹ - 1 = (1 - μ) / μ := by field_simp <;> ring
    rw [he, abs_div, abs_of_pos hp, abs_sub_comm]
    apply (div_le_iff₀ hp).2
    nlinarith
  have he : a / μ - b = (a - b) / μ + (μ⁻¹ - 1) * b := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos hp, div_eq_mul_inv, abs_mul]
  have hleft : |a - b| * μ⁻¹ ≤ 2 * E := by
    have hh := mul_le_mul hE hinv (inv_nonneg.mpr hp.le) ((abs_nonneg _).trans hE)
    simpa only [mul_comm] using hh
  exact add_le_add hleft (mul_le_mul hdiff hH (abs_nonneg _) (mul_nonneg (by norm_num) hM0))

theorem originalDetectorPaddedFinitePhaseUnit_native_form_error_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hL : 0 < fixedOriginalSincTrialAperture a)
    (hmass : 1 / 2 < fixedOriginalSincTrialNormalization ^ 2 *
      ‖originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a)
        fixedOriginalSincLobeCenter hL‖ ^ 2) :
    |(inner ℂ ((canonicalSourceMatrix (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).toEuclideanLin
      (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
        fixedOriginalSincLobeCenter hL))
      (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
        fixedOriginalSincLobeCenter hL)).re -
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re| ≤
        originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget (fixedOriginalSincTrialAperture a) := by
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hv : originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a)
      fixedOriginalSincLobeCenter hL ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hmass
    norm_num at hmass
  rw [originalDetectorPaddedFinitePhaseUnitVector_nativeEnergy_eq_Weil_div_mass ha0 σ hL hv]
  have he := originalDetectorPaddedFinitePhase_Weil_error_le hσ ha hL
  have hre := (Complex.abs_re_le_norm _).trans he
  simp only [Complex.sub_re] at hre
  have hm := originalDetectorPaddedFinitePhase_mass_error_le hσ ha hL
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hsame : originalDetectorPaddedFinitePhaseMassErrorBudget σ (fixedOriginalSincTrialAperture a) =
      originalDetectorPaddedFinitePhaseMassErrorBudget 1 (fixedOriginalSincTrialAperture a) := by
    simp only [originalDetectorPaddedFinitePhaseMassErrorBudget, hs, abs_one]
  rw [hsame] at hm
  have hb := (Complex.abs_re_le_norm _).trans (fixedOriginalSincPhaseTrial_Weil_norm_le hσ ha hL)
  exact ratio_error_le hmass hm hre hb

theorem originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget_mul_quarticWeight_tendsto_zero
    (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget L *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  have ha := (originalDetectorPaddedWeilBudget_mul_quarticWeight_tendsto_zero β).const_mul 2
  have hb := (originalDetectorPaddedMassBudget_mul_quarticWeight_tendsto_zero 1 (β + 1)).const_mul
    (2 * originalDetectorOriginalPhaseWeilSizeBudget)
  have hh := ha.add hb
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1
  ext L
  have he : originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L (β + 1) =
      Real.exp L * originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β := by
    unfold originalDetectorQuarticErrorWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_Weil_norm_le
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseUnit_native_form_error_le
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget_mul_quarticWeight_tendsto_zero
