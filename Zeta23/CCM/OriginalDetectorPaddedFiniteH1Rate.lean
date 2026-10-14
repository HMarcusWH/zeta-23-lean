import Zeta23.CCM.OriginalDetectorPaddedFiniteNormalizedErrors

/-! The full-line physical H1 error of the actual true-normalized padded image. -/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorPhysicalH1Error (f g : ℝ → ℂ) : ℝ :=
  Real.sqrt ((∫ x : ℝ, ‖f x - g x‖ ^ 2) + ∫ x : ℝ, ‖deriv (f - g) x‖ ^ 2)

private theorem integral_norm_sq_le_length_mul {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hf : Continuous f) (hs : Function.support f ⊆ Icc (0 : ℝ) L)
    (hb : ∀ x ∈ Icc (0 : ℝ) L, ‖f x‖ ≤ B) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤ L * B ^ 2 := by
  have hh := integral_norm_le_length_mul_of_support_Icc hL
    (f := fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hf.norm.pow 2)) (by
      intro x hx
      apply hs
      intro hz
      apply hx
      simp [hz]) (by
      intro x hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm] using hh

def originalDetectorPaddedFiniteH1ErrorBudget (L : ℝ) : ℝ :=
  L * (originalDetectorPaddedFiniteNormalizedJetErrorBudget L 0 +
    originalDetectorPaddedFiniteNormalizedJetErrorBudget L 1)

theorem originalDetectorPaddedFinitePhysicalUnit_H1_error_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hL : 0 < fixedOriginalSincTrialAperture a) (hlarge : 4 ≤ fixedOriginalSincTrialAperture a)
    (hmass : 1 / 2 < (originalDetectorPaddedFinitePhysicalNorm σ a hL) ^ 2) :
    originalDetectorPhysicalH1Error (originalDetectorPaddedFinitePhysicalUnit σ a hL)
      (fixedOriginalSincPhaseTrial σ a) ≤
        originalDetectorPaddedFiniteH1ErrorBudget (fixedOriginalSincTrialAperture a) := by
  let L := fixedOriginalSincTrialAperture a
  let f := originalDetectorPaddedFinitePhysicalUnit σ a hL
  let g := fixedOriginalSincPhaseTrial σ a
  let B0 := originalDetectorPaddedFiniteNormalizedJetErrorBudget L 0
  let B1 := originalDetectorPaddedFiniteNormalizedJetErrorBudget L 1
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hf : ContDiff ℝ 2 f := contDiff_const.mul
    (originalDetectorPaddedFiniteOriginalPhaseHard_contDiff ha0 σ hL)
  have hg : ContDiff ℝ 2 g := fixedOriginalSincPhaseTrial_contDiff σ a
  have hs : tsupport (f - g) ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    have hf0 : f x = 0 := by
      dsimp [f, originalDetectorPaddedFinitePhysicalUnit, originalDetectorPaddedFiniteOriginalPhaseHard]
      rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hout]
      simp
    have hg0 : g x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hb := fixedOriginalSincPhaseTrial_support ha σ hm
      exact hout ⟨by linarith [hb.1], by linarith [hb.2]⟩
    exact hx (by simp [Pi.sub_apply, hf0, hg0])
  have hd : Continuous (deriv (f - g)) := (hf.sub hg).continuous_deriv (by norm_num)
  have he0 (x : ℝ) (hx : x ∈ Icc (0 : ℝ) L) : ‖(f - g) x‖ ≤ B0 := by
    change ‖originalDetectorPaddedFinitePhysicalUnit σ a hL x - fixedOriginalSincPhaseTrial σ a x‖ ≤
      originalDetectorPaddedFiniteNormalizedJetErrorBudget (fixedOriginalSincTrialAperture a) 0
    simpa only [iteratedDeriv_zero] using
      originalDetectorPaddedFinitePhysicalUnit_jet_error_le hσ ha hL hmass (by norm_num : 0 ≤ 2) hx
  have he1 (x : ℝ) (hx : x ∈ Icc (0 : ℝ) L) : ‖deriv (f - g) x‖ ≤ B1 := by
    rw [deriv_sub ((hf.differentiable (by norm_num)) x) ((hg.differentiable (by norm_num)) x)]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      originalDetectorPaddedFinitePhysicalUnit_jet_error_le hσ ha hL hmass (by norm_num : 1 ≤ 2) hx
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (he0 0 ⟨le_rfl, hL.le⟩)
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (he1 0 ⟨le_rfl, hL.le⟩)
  have hi0 := integral_norm_sq_le_length_mul hL.le hB0 (hf.sub hg).continuous
    (subset_closure.trans hs) he0
  have hi1 := integral_norm_sq_le_length_mul hL.le hB1 hd
    (subset_closure.trans (tsupport_deriv_subset.trans hs)) he1
  unfold originalDetectorPhysicalH1Error
  change Real.sqrt ((∫ x, ‖(f - g) x‖ ^ 2) + ∫ x, ‖deriv (f - g) x‖ ^ 2) ≤ L * (B0 + B1)
  apply (Real.sqrt_le_iff).2
  refine ⟨mul_nonneg hL.le (add_nonneg hB0 hB1), ?_⟩
  calc
    _ ≤ L * B0 ^ 2 + L * B1 ^ 2 := add_le_add hi0 hi1
    _ = L * (B0 ^ 2 + B1 ^ 2) := by ring
    _ ≤ L * (B0 + B1) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hL.le
    _ ≤ L ^ 2 * (B0 + B1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by dsimp [L]; nlinarith) (sq_nonneg _)
    _ = _ := by ring

theorem originalDetectorPaddedFiniteH1ErrorBudget_mul_quarticWeight_tendsto_zero (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFiniteH1ErrorBudget L *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  have h0 := originalDetectorPaddedFiniteNormalizedJetErrorBudget_mul_quarticWeight_tendsto_zero 0 (β + 1)
  have h1 := originalDetectorPaddedFiniteNormalizedJetErrorBudget_mul_quarticWeight_tendsto_zero 1 (β + 1)
  have hh := (h0.add h1).mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  simp only [add_zero, mul_zero] at hh
  convert! hh using 1
  ext L
  have he : originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L (β + 1) * Real.exp (-L) =
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β := by
    unfold originalDetectorQuarticErrorWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pow_one, ← add_mul, mul_mul_mul_comm, he]
  unfold originalDetectorPaddedFiniteH1ErrorBudget
  ring

/-- The required concrete `L^(17/2)` physical H1 rate, with constants
constructed only from the frozen source. A retained part of the actual
stretched-exponential decay pays conservative polynomial normalization costs. -/
theorem originalDetectorPaddedFinitePhysicalUnit_H1_concrete_rate :
    ∃ C c L0 : ℝ, 0 < C ∧ 0 < c ∧ 4 ≤ L0 ∧
      ∀ (σ a : ℝ) (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
        (hL : 0 < fixedOriginalSincTrialAperture a),
        L0 ≤ fixedOriginalSincTrialAperture a →
        originalDetectorPhysicalH1Error (originalDetectorPaddedFinitePhysicalUnit σ a hL)
          (fixedOriginalSincPhaseTrial σ a) ≤
          C * (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
            Real.exp (-c * originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
  obtain ⟨Lm, hLm, hmass⟩ := exists_originalDetectorPaddedFinitePhase_mass_control_threshold
  obtain ⟨B, hB⟩ := eventually_atTop.1 (eventually_lt_retained_quartic_envelope
    UniversalSinc.fixedScale (originalDetectorPaddedFiniteH1ErrorBudget_mul_quarticWeight_tendsto_zero 0))
  refine ⟨1, originalDetectorRetainedDecayRate UniversalSinc.fixedScale,
    max 4 (max Lm B), by norm_num, originalDetectorRetainedDecayRate_pos _, le_max_left _ _, ?_⟩
  intro σ a hσ ha hL hlarge
  have h4 : 4 ≤ fixedOriginalSincTrialAperture a := (le_max_left _ _).trans hlarge
  have hm := (hmass σ a hσ ha hL ((le_max_left Lm B).trans ((le_max_right 4 _).trans hlarge))).1
  have hm' : 1 / 2 < (originalDetectorPaddedFinitePhysicalNorm σ a hL) ^ 2 := by
    convert! hm using 1 <;> unfold originalDetectorPaddedFinitePhysicalNorm <;> ring
  have herr := originalDetectorPaddedFinitePhysicalUnit_H1_error_le hσ ha hL h4 hm'
  have henv := hB (fixedOriginalSincTrialAperture a)
    ((le_max_right Lm B).trans ((le_max_right 4 _).trans hlarge))
  have hp : (1 : ℝ) ≤ (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  exact herr.trans (henv.le.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
      (Real.exp_pos (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
        originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))).le))

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_H1_error_le
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteH1ErrorBudget_mul_quarticWeight_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_H1_concrete_rate
