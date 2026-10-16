import Zeta23.ExceptionalZero.UniversalSincSignedExcursions
import Zeta23.ExceptionalZero.TwoTranslateContraction
import Zeta23.ExceptionalZero.WeilZeroSideEvenization
import Zeta23.CCM.UniversalSincSourceFacade

/-!
# Genuine normalization of the original two reflected lobes

The scale, source and kernel are fixed. The lobe centers are 1+s0 and
1+s0+2a, and L=2a+2(1+s0); reflection in L interchanges those lobes.
For a>s0 they are disjoint. Their normalization is the literal positive
L2 mass of k, proved positive from the actual transform at frequency zero.
The Weil value is identified with the existing localized additive RHS.
No Fourier, normalization, or phase-depth certificate is a caller input.

Finite-image approximation and the complete Step123 producer are separate
obligations. This module only constructs the original physical trial.
-/

noncomputable section

open Set MeasureTheory Complex
open scoped Topology ComplexConjugate

namespace Zeta23.ExceptionalZero

def fixedOriginalSincKernel : ℝ → ℂ := originalSincTest CCM.UniversalSinc.fixedScale

def fixedOriginalSincKernelL2Mass : ℝ := ∫ x : ℝ, ‖fixedOriginalSincKernel x‖ ^ 2

def fixedOriginalSincLobeCenter : ℝ := 1 + CCM.UniversalSinc.fixedScale

def fixedOriginalSincTrialAperture (a : ℝ) : ℝ := 2 * a + 2 * fixedOriginalSincLobeCenter

def fixedOriginalSincTrialNormalization : ℝ := (Real.sqrt (2 * fixedOriginalSincKernelL2Mass))⁻¹

def fixedOriginalSincPhaseTrial (σ a : ℝ) : ℝ → ℂ :=
  translateRight (twoTranslateCombination fixedOriginalSincKernel (2 * a)
    (fixedOriginalSincTrialNormalization : ℂ)
    ((σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ)) fixedOriginalSincLobeCenter

theorem integrable_fixedOriginalSincKernel_norm_sq :
    Integrable (fun x : ℝ => ‖fixedOriginalSincKernel x‖ ^ 2) := by
  have hc := (contDiff_originalSincTest CCM.UniversalSinc.fixedScale_pos).continuous.norm.pow 2
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-CCM.UniversalSinc.fixedScale)
    CCM.UniversalSinc.fixedScale) isCompact_Icc
  intro x hx
  have hz : originalSincTest CCM.UniversalSinc.fixedScale x = 0 :=
    CCM.universalSincKernel_zero_outside CCM.UniversalSinc.fixedScale_pos hx
  change ‖originalSincTest CCM.UniversalSinc.fixedScale x‖ ^ 2 = 0
  rw [hz, norm_zero]
  norm_num

theorem fixedOriginalSincKernel_integral :
    (∫ x : ℝ, fixedOriginalSincKernel x) = (-1 / 4 : ℂ) := by
  have h := paperFT_originalSincTest CCM.UniversalSinc.fixedScale_pos 0
  norm_num [paperFT_def, originalSincMultiplier, CCM.UniversalSinc.product_zero] at h
  change (∫ x : ℝ, originalSincTest CCM.UniversalSinc.fixedScale x) = _
  simpa only [neg_div] using h

/-- The genuine L2 mass is positive without a zeta-zero assumption. -/
theorem fixedOriginalSincKernelL2Mass_pos : 0 < fixedOriginalSincKernelL2Mass := by
  have hne : ∃ x : ℝ, fixedOriginalSincKernel x ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hfun : fixedOriginalSincKernel = fun _ => (0 : ℂ) := funext hnone
    have hmass := fixedOriginalSincKernel_integral
    rw [hfun, integral_zero] at hmass
    norm_num at hmass
  obtain ⟨x, hx⟩ := hne
  exact integral_pos_of_integrable_nonneg_nonzero
    ((contDiff_originalSincTest CCM.UniversalSinc.fixedScale_pos).continuous.norm.pow 2)
    integrable_fixedOriginalSincKernel_norm_sq (fun _ => sq_nonneg _)
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem fixedOriginalSincTrialNormalization_pos : 0 < fixedOriginalSincTrialNormalization :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (by norm_num) fixedOriginalSincKernelL2Mass_pos))

theorem fixedOriginalSincTrialNormalization_sq_mass :
    fixedOriginalSincTrialNormalization ^ 2 * (2 * fixedOriginalSincKernelL2Mass) = 1 := by
  have hp : 0 < 2 * fixedOriginalSincKernelL2Mass :=
    mul_pos (by norm_num) fixedOriginalSincKernelL2Mass_pos
  rw [fixedOriginalSincTrialNormalization, inv_pow,
    Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']

private theorem fixedOriginalSincKernel_zero_outside {x : ℝ}
    (hx : x ∉ Icc (-CCM.UniversalSinc.fixedScale) CCM.UniversalSinc.fixedScale) :
    fixedOriginalSincKernel x = 0 :=
  CCM.universalSincKernel_zero_outside CCM.UniversalSinc.fixedScale_pos hx

theorem fixedOriginalSincPhaseTrial_reflected_formula (σ a x : ℝ) :
    fixedOriginalSincPhaseTrial σ a x =
      (fixedOriginalSincTrialNormalization : ℂ) *
        (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
          (σ : ℂ) * fixedOriginalSincKernel
            (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter)) := by
  have heven : Function.Even fixedOriginalSincKernel :=
    originalSincTest_even CCM.UniversalSinc.fixedScale_pos
  have harg : fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter =
      -((x - fixedOriginalSincLobeCenter) - 2 * a) := by
    unfold fixedOriginalSincTrialAperture
    ring
  rw [harg, heven]
  simp only [fixedOriginalSincPhaseTrial, translateRight, twoTranslateCombination,
    map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

private theorem fixedOriginalSinc_lobes_disjoint {a : ℝ}
    (ha : CCM.UniversalSinc.fixedScale < a) (x : ℝ) :
    fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) = 0 ∨
      fixedOriginalSincKernel ((x - fixedOriginalSincLobeCenter) - 2 * a) = 0 := by
  by_cases hx : x - fixedOriginalSincLobeCenter ∈
      Icc (-CCM.UniversalSinc.fixedScale) CCM.UniversalSinc.fixedScale
  · right
    apply fixedOriginalSincKernel_zero_outside
    intro hright
    linarith [hx.2, hright.1]
  · exact Or.inl (fixedOriginalSincKernel_zero_outside hx)

/-- The literal normalized trial has unit full-line L2 mass. -/
theorem fixedOriginalSincPhaseTrial_integral_norm_sq {σ a : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (ha : CCM.UniversalSinc.fixedScale < a) :
    (∫ x : ℝ, ‖fixedOriginalSincPhaseTrial σ a x‖ ^ 2) = 1 := by
  have hσnorm : ‖(σ : ℂ)‖ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hr := fixedOriginalSincTrialNormalization_pos.le
  have hpoint (x : ℝ) : ‖fixedOriginalSincPhaseTrial σ a x‖ ^ 2 =
      fixedOriginalSincTrialNormalization ^ 2 *
        (‖fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter)‖ ^ 2 +
          ‖fixedOriginalSincKernel ((x - fixedOriginalSincLobeCenter) - 2 * a)‖ ^ 2) := by
    have hformula : fixedOriginalSincPhaseTrial σ a x =
        (fixedOriginalSincTrialNormalization : ℂ) *
          (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
            (σ : ℂ) * fixedOriginalSincKernel ((x - fixedOriginalSincLobeCenter) - 2 * a)) := by
      simp only [fixedOriginalSincPhaseTrial, translateRight, twoTranslateCombination,
        map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [hformula, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    rcases fixedOriginalSinc_lobes_disjoint ha x with h | h
    · simp only [h, norm_zero, zero_add, norm_mul, hσnorm, one_mul]
      ring
    · simp only [h, mul_zero, add_zero, norm_zero]
      ring
  have hleft := integrable_fixedOriginalSincKernel_norm_sq.comp_sub_right fixedOriginalSincLobeCenter
  have hright := (integrable_fixedOriginalSincKernel_norm_sq.comp_sub_right (2 * a)).comp_sub_right
    fixedOriginalSincLobeCenter
  have hIleft : (∫ x : ℝ, ‖fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter)‖ ^ 2) =
      fixedOriginalSincKernelL2Mass :=
    integral_sub_right_eq_self (fun x : ℝ => ‖fixedOriginalSincKernel x‖ ^ 2)
      fixedOriginalSincLobeCenter
  have hIright : (∫ x : ℝ, ‖fixedOriginalSincKernel
      (x - fixedOriginalSincLobeCenter - 2 * a)‖ ^ 2) = fixedOriginalSincKernelL2Mass := by
    rw [integral_sub_right_eq_self
      (fun x : ℝ => ‖fixedOriginalSincKernel (x - 2 * a)‖ ^ 2) fixedOriginalSincLobeCenter]
    exact integral_sub_right_eq_self (fun x : ℝ => ‖fixedOriginalSincKernel x‖ ^ 2) (2 * a)
  simp_rw [hpoint]
  rw [integral_const_mul, integral_add hleft hright, hIleft, hIright]
  change fixedOriginalSincTrialNormalization ^ 2 *
    (fixedOriginalSincKernelL2Mass + fixedOriginalSincKernelL2Mass) = 1
  rw [← two_mul]
  exact fixedOriginalSincTrialNormalization_sq_mass

theorem fixedOriginalSincPhaseTrial_contDiff (σ a : ℝ) :
    ContDiff ℝ 2 (fixedOriginalSincPhaseTrial σ a) :=
  contDiff_translateRight
    (twoTranslateCombination_contDiff
      ((contDiff_originalSincTest CCM.UniversalSinc.fixedScale_pos).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) _ _ _) _

theorem fixedOriginalSincPhaseTrial_hasCompactSupport (σ a : ℝ) :
    HasCompactSupport (fixedOriginalSincPhaseTrial σ a) :=
  hasCompactSupport_translateRight
    (twoTranslateCombination_hasCompactSupport
      (hasCompactSupport_originalSincTest CCM.UniversalSinc.fixedScale_pos) _ _ _) _

/-- Both literal lobes lie inside the fixed unit endpoint collars. -/
theorem fixedOriginalSincPhaseTrial_support {a : ℝ}
    (ha : CCM.UniversalSinc.fixedScale < a) (σ : ℝ) :
    tsupport (fixedOriginalSincPhaseTrial σ a) ⊆
      Icc 1 (fixedOriginalSincTrialAperture a - 1) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hout
  have hleft : fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) = 0 := by
    apply fixedOriginalSincKernel_zero_outside
    intro h
    apply hout
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter] at *
    constructor <;> linarith [h.1, h.2]
  have hright : fixedOriginalSincKernel
      (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) = 0 := by
    apply fixedOriginalSincKernel_zero_outside
    intro h
    apply hout
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter] at *
    constructor <;> linarith [h.1, h.2]
  apply hx
  rw [fixedOriginalSincPhaseTrial_reflected_formula, hleft, hright]
  simp

/-- Exact normalized original-phase energy. The diagonal is finite, with
no assumption about its sign. -/
theorem fixedOriginalSincPhaseTrial_Weil_re {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re =
      (fixedOriginalSincCorrelationReal 0 + σ * fixedOriginalSincCorrelationReal a) /
        fixedOriginalSincKernelL2Mass := by
  have hNne : fixedOriginalSincKernelL2Mass ≠ 0 := fixedOriginalSincKernelL2Mass_pos.ne'
  have hcoef : 2 * fixedOriginalSincTrialNormalization ^ 2 =
      1 / fixedOriginalSincKernelL2Mass := by
    apply (eq_div_iff hNne).mpr
    nlinarith [fixedOriginalSincTrialNormalization_sq_mass]
  have h0 : zetaZeroConfig.W fixedOriginalSincKernel fixedOriginalSincKernel =
      (fixedOriginalSincCorrelationReal 0 : ℂ) := by
    rw [fixedOriginalSincCorrelationReal_ofReal]
    change zetaZeroConfig.W fixedOriginalSincKernel fixedOriginalSincKernel =
      zetaZeroConfig.W (translateRight fixedOriginalSincKernel (2 * 0)) fixedOriginalSincKernel
    have ht : translateRight fixedOriginalSincKernel (2 * (0 : ℝ)) = fixedOriginalSincKernel := by
      funext x
      simp only [translateRight, mul_zero, sub_zero]
    rw [ht]
  have hC : weilRelativeCorrelation zetaZeroConfig fixedOriginalSincKernel (2 * a) =
      (fixedOriginalSincCorrelationReal a : ℂ) := (fixedOriginalSincCorrelationReal_ofReal a).symm
  have hCraw : zetaZeroConfig.W (translateRight fixedOriginalSincKernel (2 * a))
      fixedOriginalSincKernel = (fixedOriginalSincCorrelationReal a : ℂ) := hC
  unfold fixedOriginalSincPhaseTrial
  have hk : ContDiff ℝ 2 fixedOriginalSincKernel :=
    (contDiff_originalSincTest CCM.UniversalSinc.fixedScale_pos).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hkc : HasCompactSupport fixedOriginalSincKernel :=
    hasCompactSupport_originalSincTest CCM.UniversalSinc.fixedScale_pos
  rw [W_translateRight_self, zeta_W_twoTranslateCombination_expansion
    hk hkc,
    W_f_translateRight_eq_star_relativeCorrelation, W_translateRight_self, h0, hC, hCraw]
  simp only [Complex.conj_ofReal]
  change (((fixedOriginalSincTrialNormalization : ℂ) * (fixedOriginalSincTrialNormalization : ℂ) *
      (fixedOriginalSincCorrelationReal 0 : ℂ) +
    (fixedOriginalSincTrialNormalization : ℂ) * ((σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ) *
      (fixedOriginalSincCorrelationReal a : ℂ) +
    ((σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ) * (fixedOriginalSincTrialNormalization : ℂ) *
      (fixedOriginalSincCorrelationReal a : ℂ) +
    ((σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ) *
      ((σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ) * (fixedOriginalSincCorrelationReal 0 : ℂ)).re = _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero]
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  calc
    _ = fixedOriginalSincTrialNormalization ^ 2 *
        ((1 + σ ^ 2) * fixedOriginalSincCorrelationReal 0 +
          2 * σ * fixedOriginalSincCorrelationReal a) := by ring
    _ = (2 * fixedOriginalSincTrialNormalization ^ 2) *
        (fixedOriginalSincCorrelationReal 0 + σ * fixedOriginalSincCorrelationReal a) := by
      rw [hσsq]
      ring
    _ = _ := by rw [hcoef]; ring

/-- The physical trial uses the already established native additive
normalization dictionary, with no separately supplied Fourier premise. -/
theorem fixedOriginalSincPhaseTrial_Weil_eq_native (σ a : ℝ) :
    zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a) =
      CCM.localizedWeilAdditiveRHS (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a) :=
  zeta_W_self_eq_localizedWeilAdditiveRHS
    (fixedOriginalSincPhaseTrial_contDiff σ a) (fixedOriginalSincPhaseTrial_hasCompactSupport σ a)

/-- For each prescribed original phase, the actual normalized physical
trial has the requested exponential depth at arbitrarily late apertures.
The two phase apertures may differ. -/
theorem exists_fixedOriginalSincPhaseTrial_depth_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) {β σ : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (hσ : σ = 1 ∨ σ = -1) (R : ℝ) :
    ∃ a : ℝ, max R 4 < fixedOriginalSincTrialAperture a ∧
      tsupport (fixedOriginalSincPhaseTrial σ a) ⊆
        Icc 1 (fixedOriginalSincTrialAperture a - 1) ∧
      (∫ x : ℝ, ‖fixedOriginalSincPhaseTrial σ a x‖ ^ 2) = 1 ∧
      (CCM.localizedWeilAdditiveRHS
        (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture a) := by
  have hoff : (ρ : ℂ).re ≠ 1 / 2 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hβρ
    linarith
  have hNpos := fixedOriginalSincKernelL2Mass_pos
  let B : ℝ := fixedOriginalSincKernelL2Mass *
    Real.exp (2 * β * fixedOriginalSincLobeCenter) + |fixedOriginalSincCorrelationReal 0| + 1
  let A : ℝ := max (max R 4) CCM.UniversalSinc.fixedScale + 1
  have hexc := fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
    ρ hoff hβρ A B
  have hexists : ∃ a : ℝ, A < a ∧
      σ * fixedOriginalSincCorrelationReal a < -(B * Real.exp (2 * β * a)) := by
    rcases hσ with h | h
    · simpa only [h, one_mul] using hexc.2
    · obtain ⟨a, ha, hv⟩ := hexc.1
      refine ⟨a, ha, ?_⟩
      rw [h]
      nlinarith
  obtain ⟨a, ha, hv⟩ := hexists
  have hasep : CCM.UniversalSinc.fixedScale < a := by
    dsimp [A] at ha
    linarith [le_max_right (max R (4 : ℝ)) CCM.UniversalSinc.fixedScale]
  have ha0 : 0 < a := CCM.UniversalSinc.fixedScale_pos.trans hasep
  have hlate : max R 4 < fixedOriginalSincTrialAperture a := by
    dsimp [A] at ha
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter]
    linarith [le_max_left (max R (4 : ℝ)) CCM.UniversalSinc.fixedScale,
      CCM.UniversalSinc.fixedScale_pos]
  refine ⟨a, hlate, fixedOriginalSincPhaseTrial_support hasep σ,
    fixedOriginalSincPhaseTrial_integral_norm_sq hσ hasep, ?_⟩
  rw [← fixedOriginalSincPhaseTrial_Weil_eq_native, fixedOriginalSincPhaseTrial_Weil_re hσ]
  apply (div_le_iff₀ fixedOriginalSincKernelL2Mass_pos).mpr
  have hE1 : 1 ≤ Real.exp (2 * β * a) := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hCabs := le_abs_self (fixedOriginalSincCorrelationReal 0)
  have hAbsE : |fixedOriginalSincCorrelationReal 0| ≤
      |fixedOriginalSincCorrelationReal 0| * Real.exp (2 * β * a) :=
    le_mul_of_one_le_right (abs_nonneg _) hE1
  have hExp : Real.exp (β * fixedOriginalSincTrialAperture a) =
      Real.exp (2 * β * fixedOriginalSincLobeCenter) * Real.exp (2 * β * a) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [fixedOriginalSincTrialAperture]
    ring
  rw [hExp]
  dsimp [B] at hv
  nlinarith [Real.exp_pos (2 * β * a)]

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.fixedOriginalSincKernel_integral
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincKernelL2Mass_pos
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_reflected_formula
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_integral_norm_sq
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_support
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_Weil_re
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_Weil_eq_native
#print axioms Zeta23.ExceptionalZero.exists_fixedOriginalSincPhaseTrial_depth_of_off_line_zero
