import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseMass

/-! # Norm control of the actual finite original phase without an input norm premise -/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

theorem originalDetectorPaddedFiniteOriginalPhaseApprox_interval_energy
    (σ a : ℝ) (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) :
    (∫ x in (0 : ℝ)..Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a,
      ‖originalDetectorPaddedFiniteOriginalPhaseApprox σ a hLp x‖ ^ 2) =
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization ^ 2 *
        ‖originalDetectorPaddedFinitePhaseVector σ
          (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp‖ ^ 2 := by
  unfold originalDetectorPaddedFiniteOriginalPhaseApprox
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos, mul_pow]
  rw [intervalIntegral.integral_const_mul, localizedFiniteFunction_energy_eq_norm_sq hLp]

private theorem originalPhase_interval_energy_eq_one
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) :
    (∫ x in (0 : ℝ)..Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a,
      ‖Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x‖ ^ 2) = 1 := by
  have hmass := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_integral_norm_sq hσ ha
  have heq : (fun x : ℝ => ‖Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x‖ ^ 2) =
      (Icc (0 : ℝ) (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)).indicator
        (fun x => ‖Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    · simp [hx]
    · have hz : Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        have hb := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_support ha σ hm
        exact hx ⟨by linarith [hb.1], by linarith [hb.2]⟩
      simp [hx, hz]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hLp.le] at hmass
  exact hmass

def originalDetectorPaddedFinitePhaseMassErrorBudget (σ L : ℝ) : ℝ :=
  let C := Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|)
  let ε := C * originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L 0
  let M := C * padded_originalDetectorKernelSupBudget UniversalSinc.fixedScale
  L * (ε * (2 * M + ε))

/-- The actual original-normalized finite phase mass differs from one by
an explicit source-derived budget. No native norm or nonzero premise is
introduced at this normalization step. -/
theorem originalDetectorPaddedFinitePhase_mass_error_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) :
    |Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization ^ 2 *
      ‖originalDetectorPaddedFinitePhaseVector σ
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
        Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp‖ ^ 2 - 1| ≤
      originalDetectorPaddedFinitePhaseMassErrorBudget σ (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) := by
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let C := Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|)
  let ε := C * originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L 0
  let M := C * padded_originalDetectorKernelSupBudget UniversalSinc.fixedScale
  let f := originalDetectorPaddedFiniteOriginalPhaseApprox σ a hLp
  let g := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hC : 0 ≤ C := mul_nonneg Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos.le (by positivity)
  have hM : 0 ≤ M := mul_nonneg hC (padded_originalDetectorKernelSupBudget_nonneg _)
  have herr (x : ℝ) (hx : x ∈ Icc (0 : ℝ) L) : ‖f x - g x‖ ≤ ε := by
    have he := originalDetectorPaddedFiniteOriginalPhaseApprox_iteratedDeriv_error_le ha0 σ 0 hx
    simp only [iteratedDeriv_zero] at he
    rw [norm_sub_rev]
    exact he
  have hε : 0 ≤ ε := (norm_nonneg _).trans (herr 0 ⟨le_rfl, hLp.le⟩)
  have hf : Continuous f := by
    dsimp [f]
    unfold originalDetectorPaddedFiniteOriginalPhaseApprox
    apply continuous_const.mul
    unfold localizedFiniteFunction
    fun_prop
  have hg : Continuous g := (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a).continuous
  have hbound (x : ℝ) (_hx : x ∈ Icc (0 : ℝ) L) : ‖g x‖ ≤ M :=
    padded_norm_fixedOriginalSincPhaseTrial_le_source_budget σ a x
  have hmass := padded_interval_energy_error_le_of_uniform_error hLp.le hM hε hf hg hbound herr
  rw [originalDetectorPaddedFiniteOriginalPhaseApprox_interval_energy,
    originalPhase_interval_energy_eq_one hσ ha hLp] at hmass
  exact hmass

/-- Multiplication by aperture still leaves decay faster than any fixed
linear exponential. This also pays the full-line L1-error aperture factor. -/
theorem originalDetectorPaddedFinitePoleImageJetBudget_mul_aperture_exp_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => L * originalDetectorPaddedFinitePoleImageJetBudget s L r * Real.exp (β * L))
      atTop (𝓝 0) := by
  have hfast := originalDetectorPaddedFinitePoleImageJetBudget_mul_exp_tendsto_zero s r (β + 1)
  have hpoly := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hprod := hfast.mul hpoly
  simp only [mul_zero] at hprod
  convert! hprod using 1
  ext L
  simp only [pow_one]
  have he : Real.exp ((β + 1) * L) * Real.exp (-L) = Real.exp (β * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_mul_mul_comm, he]
  ring

/-- The proved actual phase mass-error budget also beats every linear
exponential, so later normalization uses a cofinally controlled true norm. -/
theorem originalDetectorPaddedFinitePhaseMassErrorBudget_mul_exp_tendsto_zero
    (σ β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseMassErrorBudget σ L * Real.exp (β * L))
      atTop (𝓝 0) := by
  let C := Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|)
  let M := C * padded_originalDetectorKernelSupBudget UniversalSinc.fixedScale
  have hlinear := (originalDetectorPaddedFinitePoleImageJetBudget_mul_aperture_exp_tendsto_zero
    UniversalSinc.fixedScale 0 β).const_mul C
  have hzero := originalDetectorPaddedFinitePoleImageJetBudget_mul_exp_tendsto_zero UniversalSinc.fixedScale 0 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hzero
  have hfactor : Tendsto
    (fun L : ℝ => 2 * M + C * originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L 0)
      atTop (𝓝 (2 * M + C * 0)) := tendsto_const_nhds.add (hzero.const_mul C)
  have hprod := hlinear.mul hfactor
  simp only [mul_zero, add_zero, zero_mul] at hprod
  convert! hprod using 1
  ext L
  unfold originalDetectorPaddedFinitePhaseMassErrorBudget
  dsimp [C, M]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteOriginalPhaseApprox_interval_energy
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhase_mass_error_le
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImageJetBudget_mul_aperture_exp_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseMassErrorBudget_mul_exp_tendsto_zero
