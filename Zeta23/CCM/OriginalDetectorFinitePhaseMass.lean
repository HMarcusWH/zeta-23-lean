import Zeta23.CCM.OriginalDetectorFinitePhaseApproximation

/-! # Actual physical mass control for the reflected finite phase vector -/

noncomputable section

open Set Complex MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def originalDetectorKernelSupBudget (s : ℝ) : ℝ :=
  originalDetectorLobeJetBudget s 2 + (1 / 4 : ℝ) * originalDetectorLobeJetBudget s 0

theorem originalDetectorKernelSupBudget_nonneg (s : ℝ) :
    0 ≤ originalDetectorKernelSupBudget s := by
  unfold originalDetectorKernelSupBudget originalDetectorLobeJetBudget
  positivity

/-- Uniform size is derived from the actual original source jets. -/
theorem norm_originalSincTest_le_source_budget {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖Zeta23.ExceptionalZero.originalSincTest s x‖ ≤ originalDetectorKernelSupBudget s := by
  have hsource := congrFun (poleKilled_originalDetectorLobe s 0) x
  simp only [sub_zero] at hsource
  rw [← hsource]
  unfold Zeta23.ExceptionalZero.poleKilled
  have h2 : ‖deriv (deriv (originalDetectorLobe s 0)) x‖ ≤ originalDetectorLobeJetBudget s 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, originalDetectorLobeJetBudget] using
      originalDetectorLobe_iteratedDeriv_le_gevrey hs 2 0 x
  have h0 : ‖originalDetectorLobe s 0 x‖ ≤ originalDetectorLobeJetBudget s 0 := by
    simpa only [iteratedDeriv_zero, originalDetectorLobeJetBudget] using
      originalDetectorLobe_iteratedDeriv_le_gevrey hs 0 0 x
  refine (norm_sub_le _ _).trans ?_
  unfold originalDetectorKernelSupBudget
  apply add_le_add h2
  rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left h0 (by norm_num)

theorem norm_fixedOriginalSincPhaseTrial_le_source_budget (σ a x : ℝ) :
    ‖Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x‖ ≤
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|) *
        originalDetectorKernelSupBudget UniversalSinc.fixedScale := by
  rw [Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_reflected_formula, norm_mul]
  have hη : ‖(Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ)‖ =
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization := by
    simp [abs_of_pos Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos]
  rw [hη]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos.le).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_originalSincTest_le_source_budget UniversalSinc.fixedScale_pos
    (x - Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter)
  have h2 := norm_originalSincTest_le_source_budget UniversalSinc.fixedScale_pos
    (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a - x -
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter)
  have hsum := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg σ))
  convert! mul_le_mul_of_nonneg_left hsum
    Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos.le using 1 <;> ring

/-- An elementary mass perturbation estimate, applied below to the actual
proved source envelope and actual constructed approximation error. -/
theorem interval_energy_error_le_of_uniform_error
    {L M δ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hg_bound : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ M)
    (herr : ∀ x ∈ Icc 0 L, ‖f x - g x‖ ≤ δ) :
    |(∫ x in (0 : ℝ)..L, ‖f x‖ ^ 2) - (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2)| ≤
      L * (δ * (2 * M + δ)) := by
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 L) : |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ≤ δ * (2 * M + δ) := by
    have hdiff := abs_norm_sub_norm_le (f x) (g x)
    have hsub : |‖f x‖ - ‖g x‖| ≤ δ := hdiff.trans (herr x hx)
    have hf_bound : ‖f x‖ ≤ M + δ := by
      have ht := norm_sub_le (f x - g x) (-g x)
      have hh := norm_add_le (f x - g x) (g x)
      have heq : (f x - g x) + g x = f x := sub_add_cancel _ _
      rw [heq] at hh
      linarith [herr x hx, hg_bound x hx]
    calc
      _ = |‖f x‖ - ‖g x‖| * (‖f x‖ + ‖g x‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
        congr 1
        ring
      _ ≤ δ * (2 * M + δ) := mul_le_mul hsub (by linarith [hg_bound x hx])
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hδ
  have hfi : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 L :=
    (hf.norm.pow 2).intervalIntegrable 0 L
  have hgi : IntervalIntegrable (fun x : ℝ => ‖g x‖ ^ 2) volume 0 L :=
    (hg.norm.pow 2).intervalIntegrable 0 L
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := L) (C := δ * (2 * M + δ))
    (f := fun x : ℝ => ‖f x‖ ^ 2 - ‖g x‖ ^ 2)
    (fun x hx => by
      have hx' : x ∈ Ioc (0 : ℝ) L := by simpa only [uIoc_of_le hL] using hx
      simpa only [Real.norm_eq_abs] using hpoint x ⟨hx'.1.le, hx'.2⟩)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hL, mul_comm] using hb

end Zeta23.CCM

#print axioms Zeta23.CCM.norm_originalSincTest_le_source_budget
#print axioms Zeta23.CCM.norm_fixedOriginalSincPhaseTrial_le_source_budget
#print axioms Zeta23.CCM.interval_energy_error_le_of_uniform_error
