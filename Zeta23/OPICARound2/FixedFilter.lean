import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICARound2.ClassicalAdapter
import Zeta23.OPICAFollowup.LogFourierSobolev
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The literal fixed filter and its probability source

The kernel and density in this file are the physical objects required by
S04. Algebraic multiplier identities are kept separate from the L2/Fourier
identification: no algebraic factorization is called an operator isometry.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
open scoped Topology ENNReal FourierTransform Convolution

namespace Zeta23.OPICARound2

/-- The literal delayed original probability density (one source copy). -/
def qPlus (t : ℝ) : ℝ := CCM.universalSincSource probeSigma (t - probeSigma)

theorem qPlus_nonneg (t : ℝ) : 0 ≤ qPlus t :=
  CCM.universalSincSource_nonneg probeSigma_pos _

theorem qPlus_zero_outside {t : ℝ} (ht : t ∉ Icc 0 (2 * probeSigma)) :
    qPlus t = 0 := by
  change CCM.universalSincSource probeSigma (t - probeSigma) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hx' := CCM.universalSincSource_support probeSigma_pos hx
  apply ht
  constructor <;> linarith [hx'.1, hx'.2]

theorem qPlus_zero_of_neg {t : ℝ} (ht : t < 0) : qPlus t = 0 :=
  qPlus_zero_outside (fun h => (not_le_of_gt ht) h.1)

theorem qPlus_contDiff : ContDiff ℝ (⊤ : ℕ∞) qPlus :=
  (CCM.universalSincSource_contDiff probeSigma_pos).comp
    (contDiff_id.sub contDiff_const)

theorem qPlus_hasCompactSupport : HasCompactSupport qPlus := by
  apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
  exact fun _ hx => qPlus_zero_outside hx

theorem qPlus_integrable : Integrable qPlus :=
  qPlus_contDiff.continuous.integrable_of_hasCompactSupport qPlus_hasCompactSupport

theorem qPlus_integral_one : (∫ t : ℝ, qPlus t) = 1 := by
  change (∫ t : ℝ, CCM.universalSincSource probeSigma (t - probeSigma)) = _
  rw [integral_sub_right_eq_self]
  exact CCM.universalSincSource_integral_one probeSigma_pos

theorem qPlus_integral_norm_one : (∫ t : ℝ, ‖qPlus t‖) = 1 := by
  simp_rw [Real.norm_of_nonneg (qPlus_nonneg _)]
  exact qPlus_integral_one

/-- Probability smoothing by the literal source is constructed before use. -/
def qPlusOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator qPlus qPlus_integrable (fun t ht => qPlus_zero_of_neg ht)

theorem qPlusOperator_norm_le_one : ‖qPlusOperator‖ ≤ 1 := by
  exact (causalKernelOperator_norm_le qPlus qPlus_integrable
    (fun t ht => qPlus_zero_of_neg ht)).trans_eq qPlus_integral_norm_one

theorem qPlusOperator_contracts (f : CausalProbeL2) : ‖qPlusOperator f‖ ≤ ‖f‖ := by
  calc
    ‖qPlusOperator f‖ ≤ ‖qPlusOperator‖ * ‖f‖ := qPlusOperator.le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right qPlusOperator_norm_le_one (norm_nonneg _)
    _ = ‖f‖ := one_mul _

def QPlus (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (qPlus t : ℂ)

theorem QPlus_integrand_integrable (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (qPlus t : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp qPlus_contDiff.continuous)
  · exact (qPlus_hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left

theorem QPlus_one_copy_formula (z : ℂ) :
    QPlus z = Complex.exp (-z * (probeSigma : ℂ)) *
      CCM.UniversalSinc.product probeSigma (Complex.I * z) := by
  have hdelay : QPlus z = Complex.exp (-z * (probeSigma : ℂ)) *
      ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
        (CCM.universalSincSource probeSigma t : ℂ) := by
    unfold QPlus qPlus
    have heq (t : ℝ) :
        Complex.exp (-z * (t : ℂ)) *
            (CCM.universalSincSource probeSigma (t - probeSigma) : ℂ) =
          Complex.exp (-z * (probeSigma : ℂ)) *
            (Complex.exp (-z * ((t - probeSigma : ℝ) : ℂ)) *
              (CCM.universalSincSource probeSigma (t - probeSigma) : ℂ)) := by
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
        (CCM.universalSincSource probeSigma t : ℂ)) probeSigma
  rw [hdelay]
  congr 1
  have hf := congrFun (CCM.paperFT_universalSincSource probeSigma_pos) (Complex.I * z)
  rw [Zeta23.paperFT_def] at hf
  convert hf using 1
  apply integral_congr_ae
  filter_upwards with t
  have he : Complex.I * (Complex.I * z) * (t : ℂ) = -z * (t : ℂ) := by
    calc
      _ = (Complex.I * Complex.I) * z * (t : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he]
  ring

theorem JPlus_eq_pole_polynomial_QPlus (z : ℂ) :
    JPlus z = (z ^ 2 - 1 / 4) ^ 2 * QPlus z := by
  rw [JPlus_one_copy_formula, QPlus_one_copy_formula]
  have he : ((Complex.I * z) ^ 2 + 1 / 4) ^ 2 = (z ^ 2 - 1 / 4) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [he]
  ring

theorem QPlus_re_integral (z : ℂ) :
    (QPlus z).re = ∫ t : ℝ,
      qPlus t * Real.exp (-z.re * t) * Real.cos (z.im * t) := by
  change RCLike.re (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (qPlus t : ℂ)) = _
  rw [← integral_re (QPlus_integrand_integrable z)]
  apply integral_congr_ae
  filter_upwards with t
  change (Complex.exp (-z * (t : ℂ)) * (qPlus t : ℂ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add,
    Real.cos_neg]
  simp only [neg_mul, Real.cos_neg]
  ring

/-- The elementary pointwise source lower works before numerical specialization. -/
theorem damped_cos_lower (delta tau t : ℝ) (hdelta : 0 ≤ delta) (ht : 0 ≤ t) :
    1 - delta * t - (tau * t) ^ 2 / 2 ≤
      Real.exp (-delta * t) * Real.cos (tau * t) := by
  have he : Real.exp (-delta * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hc : Real.cos (tau * t) ≤ 1 := Real.cos_le_one _
  have hexp := Real.add_one_le_exp (-delta * t)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := tau * t)
  have hprod := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hc)
  nlinarith

/-- Uniform source visibility on the actual baseline rectangle. This
integrates the literal nonnegative probability density, not a supplied
source-margin premise. -/
theorem QPlus_baseline_rectangle_lower (z : ℂ) (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 3 / 8) (him : |z.im| ≤ 2) :
    (2096767 / 2097152 : ℝ) ≤ ‖QPlus z‖ := by
  let margin : ℝ := 2096767 / 2097152
  have hmarg : (1 : ℝ) - (3 / 8 : ℝ) * (2 * probeSigma) -
      2 * (2 * probeSigma) ^ 2 = margin := by
    rw [probeSigma_eq]
    norm_num [margin]
  have hpoint (t : ℝ) : qPlus t * margin ≤
      qPlus t * Real.exp (-z.re * t) * Real.cos (z.im * t) := by
    by_cases ht : t ∈ Icc 0 (2 * probeSigma)
    · have hd : z.re * t ≤ (3 / 8 : ℝ) * (2 * probeSigma) :=
        mul_le_mul hz1 ht.2 ht.1 (by norm_num)
      have htsq : t ^ 2 ≤ (2 * probeSigma) ^ 2 :=
        pow_le_pow_left₀ ht.1 ht.2 2
      have hisq : z.im ^ 2 ≤ 4 := by
        have h := pow_le_pow_left₀ (abs_nonneg z.im) him 2
        norm_num only [sq_abs, OfNat.ofNat] at h ⊢
        exact h
      have hprod : z.im ^ 2 * t ^ 2 ≤ 4 * (2 * probeSigma) ^ 2 :=
        mul_le_mul hisq htsq (sq_nonneg _) (by norm_num)
      have hlower := damped_cos_lower z.re z.im t hz0 ht.1
      have hfull : margin ≤ Real.exp (-z.re * t) * Real.cos (z.im * t) := by
        rw [← hmarg]
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfull (qPlus_nonneg t)
    · rw [qPlus_zero_outside ht]
      norm_num
  have hreal : Integrable (fun t : ℝ =>
      qPlus t * Real.exp (-z.re * t) * Real.cos (z.im * t)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (qPlus_contDiff.continuous.mul (by fun_prop)).mul (by fun_prop)
    · exact qPlus_hasCompactSupport.mul_right.mul_right
  have hbound := integral_mono (qPlus_integrable.mul_const margin) hreal hpoint
  rw [integral_mul_const, qPlus_integral_one, one_mul, ← QPlus_re_integral z] at hbound
  exact hbound.trans (Complex.re_le_norm _)

/-- The fixed stable rational multiplier; it is never a variable filter. -/
def fixedFilterMultiplier (z : ℂ) : ℂ := (z + 3 / 2) / (z + 1 / 2) ^ 5

/-- The causal all-pass factor. Its range on causal L2 need not be the whole space. -/
def causalInnerMultiplier (z : ℂ) : ℂ := (z - 1 / 2) / (z + 1 / 2)

/-- The elementary uncompleted comparison multiplier. -/
def classicalProbeMultiplier (z : ℂ) : ℂ := (z - 1 / 2) / (z + 1 / 2) ^ 2

/-- The literal causal filter density. -/
def fixedFilterKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t / 2) * (t ^ 3 / 6 + t ^ 4 / 24) else 0

/-- The literal causal exponential used in `I f = f - e * f`. -/
def causalInnerKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t / 2) else 0

/-- Comparison source before convolution by `qPlus`. -/
def classicalProbeKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t / 2) * (1 - t) else 0

/-- Complete fractional-part comparison source, retaining the factorial term. -/
def classicalCompletionKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t / 2) *
    ((1 - t) * (⌊Real.exp t⌋₊ : ℝ) + Real.log (Nat.factorial ⌊Real.exp t⌋₊)) else 0

theorem fixedFilterKernel_zero_of_neg (t : ℝ) (ht : t < 0) :
    fixedFilterKernel t = 0 := by simp [fixedFilterKernel, not_le.mpr ht]

theorem causalInnerKernel_zero_of_neg (t : ℝ) (ht : t < 0) :
    causalInnerKernel t = 0 := by simp [causalInnerKernel, not_le.mpr ht]

theorem fixedFilterKernel_nonneg (t : ℝ) : 0 ≤ fixedFilterKernel t := by
  by_cases ht : 0 ≤ t
  · simp only [fixedFilterKernel, if_pos ht]
    positivity
  · simp only [fixedFilterKernel, if_neg ht, le_refl]

theorem fixedFilterMultiplier_ne_zero {z : ℂ} (hz : 0 ≤ z.re) :
    fixedFilterMultiplier z ≠ 0 := by
  apply div_ne_zero
  · intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  · apply pow_ne_zero
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith

/-- The all-pass assertion is first proved as exact boundary algebra.
It does not alone assert the causal convolution operator is an isometry. -/
theorem causalInnerMultiplier_boundary_norm (tau : ℝ) :
    ‖causalInnerMultiplier ((tau : ℂ) * Complex.I)‖ = 1 := by
  have hnorm : ‖(tau : ℂ) * Complex.I - 1 / 2‖ =
      ‖(tau : ℂ) * Complex.I + 1 / 2‖ := by
    have hs : ‖(tau : ℂ) * Complex.I - 1 / 2‖ ^ 2 =
        ‖(tau : ℂ) * Complex.I + 1 / 2‖ ^ 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    nlinarith [norm_nonneg ((tau : ℂ) * Complex.I - 1 / 2),
      norm_nonneg ((tau : ℂ) * Complex.I + 1 / 2)]
  have hne : (tau : ℂ) * Complex.I + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  rw [causalInnerMultiplier, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hne)]

/-- The scalar cancellation needed before native physical factorization.
Both denominators are retained; no analytic continuation is assumed. -/
theorem fixedFilter_pole_polynomial_factorization (z : ℂ)
    (hhalf : z + 1 / 2 ≠ 0) (hthree : z + 3 / 2 ≠ 0) :
    fixedFilterMultiplier z *
      ((z - 1 / 2) / ((z + 1 / 2) * (z + 3 / 2))) *
      (z ^ 2 - 1 / 4) ^ 2 =
        causalInnerMultiplier z ^ 2 * classicalProbeMultiplier z := by
  unfold fixedFilterMultiplier causalInnerMultiplier classicalProbeMultiplier
  rw [show z ^ 2 - 1 / 4 = (z - 1 / 2) * (z + 1 / 2) by ring, mul_pow]
  generalize ha : z + 1 / 2 = a at *
  generalize hc : z + 3 / 2 = c at *
  field_simp [hhalf, hthree]
  <;> ring

/-- Exponential moments are physical half-line kernels, not spectral packets. -/
def halfExponentialPower (n : ℕ) (t : ℝ) : ℝ :=
  if 0 ≤ t then t ^ n * Real.exp (-(1 / 2 : ℝ) * t) else 0

theorem halfExponentialPower_integrable (n : ℕ) :
    Integrable (halfExponentialPower n) := by
  have hpos : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(1 / 2 : ℝ) * t))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) (by norm_num)
    simpa only [Real.rpow_natCast, Real.rpow_one] using h
  have hclosed : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(1 / 2 : ℝ) * t))
      (Ici 0) := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
  have heq : halfExponentialPower n =
      (Ici (0 : ℝ)).indicator (fun t : ℝ => t ^ n * Real.exp (-(1 / 2 : ℝ) * t)) := by
    ext t
    simp only [halfExponentialPower, mem_Ici, indicator_apply]
  rw [heq]
  exact hclosed.integrable_indicator measurableSet_Ici

theorem halfExponentialPower_integral (n : ℕ) :
    (∫ t : ℝ, halfExponentialPower n t) =
      (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
  have heq : halfExponentialPower n =
      (Ici (0 : ℝ)).indicator (fun t : ℝ => t ^ n * Real.exp (-(1 / 2 : ℝ) * t)) := by
    ext t
    simp only [halfExponentialPower, indicator_apply, mem_Ici]
  rw [heq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := (1 / 2 : ℝ)) (by positivity) (by norm_num)
  norm_num only [one_div_div, div_one, add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  · congr 1
    ext t
    ring
  · rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]

theorem fixedFilterKernel_eq_exponential_powers :
    fixedFilterKernel = fun t => halfExponentialPower 3 t / 6 +
      halfExponentialPower 4 t / 24 := by
  ext t
  by_cases ht : 0 ≤ t
  · simp only [fixedFilterKernel, halfExponentialPower, if_pos ht]
    have he : -t / 2 = -(1 / 2 : ℝ) * t := by ring
    rw [he]
    ring
  · simp [fixedFilterKernel, halfExponentialPower, ht]

theorem fixedFilterKernel_integrable : Integrable fixedFilterKernel := by
  rw [fixedFilterKernel_eq_exponential_powers]
  exact ((halfExponentialPower_integrable 3).div_const 6).add
    ((halfExponentialPower_integrable 4).div_const 24)

theorem fixedFilterKernel_integral : (∫ t : ℝ, fixedFilterKernel t) = 48 := by
  rw [fixedFilterKernel_eq_exponential_powers,
    integral_add ((halfExponentialPower_integrable 3).div_const 6)
      ((halfExponentialPower_integrable 4).div_const 24), integral_div, integral_div,
    halfExponentialPower_integral, halfExponentialPower_integral]
  norm_num

theorem fixedFilterKernel_integral_norm : (∫ t : ℝ, ‖fixedFilterKernel t‖) = 48 := by
  simp_rw [Real.norm_of_nonneg (fixedFilterKernel_nonneg _)]
  exact fixedFilterKernel_integral

/-- The actual causal convolution by the fixed physical kernel. -/
def fixedFilterOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator fixedFilterKernel fixedFilterKernel_integrable
    fixedFilterKernel_zero_of_neg

theorem fixedFilterOperator_norm_le : ‖fixedFilterOperator‖ ≤ 48 := by
  exact (causalKernelOperator_norm_le fixedFilterKernel fixedFilterKernel_integrable
    fixedFilterKernel_zero_of_neg).trans_eq fixedFilterKernel_integral_norm

theorem causalInnerKernel_eq_half_power :
    causalInnerKernel = halfExponentialPower 0 := by
  ext t
  by_cases ht : 0 ≤ t
  · simp only [causalInnerKernel, halfExponentialPower, if_pos ht, pow_zero, one_mul]
    congr 1
    ring
  · simp [causalInnerKernel, halfExponentialPower, ht]

theorem causalInnerKernel_integrable : Integrable causalInnerKernel := by
  rw [causalInnerKernel_eq_half_power]
  exact halfExponentialPower_integrable 0

theorem causalInnerKernel_integral : (∫ t : ℝ, causalInnerKernel t) = 2 := by
  rw [causalInnerKernel_eq_half_power, halfExponentialPower_integral]
  norm_num

/-- This is the physical causal formula. Its isometry needs a separate proof;
the definition does not assume any norm equality or surjectivity. -/
def causalInnerOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  ContinuousLinearMap.id ℂ CausalProbeL2 -
    causalKernelOperator causalInnerKernel causalInnerKernel_integrable
      causalInnerKernel_zero_of_neg

theorem causalInnerOperator_apply (f : CausalProbeL2) :
    causalInnerOperator f = f -
      causalKernelOperator causalInnerKernel causalInnerKernel_integrable
        causalInnerKernel_zero_of_neg f := rfl

private theorem complex_power_exp_integrableOn (n : ℕ) (a : ℂ) (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-a * (t : ℂ))) (Ioi 0) := by
  have hreal : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-a.re * t)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := (1 : ℝ)) (b := a.re)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) ha
    simpa only [Real.rpow_natCast, Real.rpow_one] using h
  apply (integrable_norm_iff (by fun_prop)).mp
  apply hreal.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  symm
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht),
    Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem complex_power_exp_tendsto_zero (n : ℕ) (a : ℂ) (ha : 0 < a.re) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-a * (t : ℂ)))
      Filter.atTop (𝓝 0) := by
  have hr : Filter.Tendsto (fun t : ℝ => a.re * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop ha
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hr
  have hscaled : Filter.Tendsto
      (fun t : ℝ => t ^ n * Real.exp (-a.re * t)) Filter.atTop (𝓝 0) := by
    have he (t : ℝ) : t ^ n * Real.exp (-a.re * t) =
        (a.re ^ n)⁻¹ * ((a.re * t) ^ n * Real.exp (-(a.re * t))) := by
      rw [mul_pow]
      field_simp [ne_of_gt ha]
      <;> ring
    simp_rw [he]
    simpa only [mul_zero, Function.comp_apply] using hbase.const_mul (a.re ^ n)⁻¹
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hscaled.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Exact complex half-line exponential moments, proved by integration by
parts; the complex damping is not replaced by its real part. -/
theorem complex_power_exp_integral (n : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ n * Complex.exp (-a * (t : ℂ))) =
      (n.factorial : ℂ) / a ^ (n + 1) := by
  have hane : a ≠ 0 := by intro h; simp [h] at ha
  induction n with
  | zero =>
    simpa using integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
  | succ n ih =>
    let u : ℝ → ℂ := fun t => (t : ℂ) ^ (n + 1)
    let up : ℝ → ℂ := fun t => ((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n
    let v : ℝ → ℂ := fun t => -Complex.exp (-a * (t : ℂ)) / a
    let vp : ℝ → ℂ := fun t => Complex.exp (-a * (t : ℂ))
    have hcast (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t :=
      Complex.ofRealCLM.hasDerivAt
    have hu (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt u (up t) t := by
      simpa [u, up] using (hasDerivAt_pow (n + 1) t).ofReal_comp
    have hv (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt v (vp t) t := by
      have hd := (((hcast t).const_mul (-a)).cexp.neg).div_const a
      have he : -(Complex.exp (-a * (t : ℂ)) * (-a * 1)) / a = vp t := by
        dsimp [vp]
        field_simp [hane]
        <;> ring
      rw [he] at hd
      exact hd
    have huv : IntegrableOn (u * vp) (Ioi 0) :=
      complex_power_exp_integrableOn (n + 1) a ha
    have hupv : IntegrableOn (up * v) (Ioi 0) := by
      have h : IntegrableOn (fun x : ℝ => (-((n + 1 : ℕ) : ℂ) / a) *
          ((x : ℂ) ^ n * Complex.exp (-a * (x : ℂ)))) (Ioi 0) :=
        (complex_power_exp_integrableOn n a ha).const_mul (-((n + 1 : ℕ) : ℂ) / a)
      apply h.congr_fun _ measurableSet_Ioi
      intro t ht
      dsimp [up, v, Pi.mul_apply]
      ring
    have hz : Filter.Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hc : Continuous (u * v) := by dsimp [u, v]; fun_prop
      convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
        simp [u, v]
    have ht : Filter.Tendsto (u * v) Filter.atTop (𝓝 (0 : ℂ)) := by
      have h := (complex_power_exp_tendsto_zero (n + 1) a ha).mul_const (-(a⁻¹))
      convert h using 1
      · ext t; dsimp [u, v]; ring
      · simp
    have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv hupv hz ht
    change (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (n + 1) * Complex.exp (-a * (t : ℂ))) = _
    calc
      _ = -∫ t : ℝ in Ioi 0, up t * v t := by simpa [u, vp] using hparts
      _ = (((n + 1 : ℕ) : ℂ) / a) *
          ∫ t : ℝ in Ioi 0, (t : ℂ) ^ n * Complex.exp (-a * (t : ℂ)) := by
        rw [← integral_const_mul]
        rw [← integral_neg]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [up, v]
        ring
      _ = _ := by
        rw [ih, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        field_simp [hane]
        <;> ring

private theorem halfExponentialPower_damped_eq (n : ℕ) (z : ℂ) :
    (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (halfExponentialPower n t : ℂ)) =
      (Ici (0 : ℝ)).indicator (fun t : ℝ =>
        (t : ℂ) ^ n * Complex.exp (-(z + 1 / 2) * (t : ℂ))) := by
  ext t
  by_cases ht : 0 ≤ t
  · simp only [halfExponentialPower, if_pos ht, indicator_apply, mem_Ici, if_pos ht,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
    rw [← mul_assoc, mul_comm (Complex.exp _) ((t : ℂ) ^ n), mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [halfExponentialPower, ht]

theorem halfExponentialPower_damped_integrable (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
      (halfExponentialPower n t : ℂ)) := by
  rw [halfExponentialPower_damped_eq]
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  apply complex_power_exp_integrableOn
  simp only [Complex.add_re]
  norm_num
  linarith

theorem halfExponentialPower_laplace (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace (fun t => (halfExponentialPower n t : ℂ)) z =
      (n.factorial : ℂ) / (z + 1 / 2) ^ (n + 1) := by
  unfold probeLaplace
  rw [halfExponentialPower_damped_eq, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  apply complex_power_exp_integral
  simp only [Complex.add_re]
  norm_num
  linarith

/-- The actual physical kernel has exactly the prescribed rational Laplace
multiplier. This is obtained from complex moments of the literal kernel. -/
theorem fixedFilterKernel_laplace (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace (fun t => (fixedFilterKernel t : ℂ)) z = fixedFilterMultiplier z := by
  have heq : (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (fixedFilterKernel t : ℂ)) =
      fun t : ℝ => (Complex.exp (-z * (t : ℂ)) * (halfExponentialPower 3 t : ℂ)) / 6 +
        (Complex.exp (-z * (t : ℂ)) * (halfExponentialPower 4 t : ℂ)) / 24 := by
    ext t
    rw [fixedFilterKernel_eq_exponential_powers]
    push_cast
    ring
  unfold probeLaplace
  rw [heq, integral_add ((halfExponentialPower_damped_integrable 3 z hz).div_const 6)
    ((halfExponentialPower_damped_integrable 4 z hz).div_const 24), integral_div,
    integral_div]
  change probeLaplace (fun t => (halfExponentialPower 3 t : ℂ)) z / 6 +
    probeLaplace (fun t => (halfExponentialPower 4 t : ℂ)) z / 24 = _
  rw [halfExponentialPower_laplace 3 z hz, halfExponentialPower_laplace 4 z hz]
  norm_num only [Nat.factorial]
  unfold fixedFilterMultiplier
  have hne : z + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  field_simp [hne]
  <;> ring

theorem fixedFilterOperator_laplace (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (fixedFilterOperator f : ProbeL2) =
      fixedFilterMultiplier z * CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  rw [fixedFilterOperator, causalKernelOperator_laplace, fixedFilterKernel_laplace z hz.le]
  exact hz

theorem causalInnerKernel_laplace (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace (fun t => (causalInnerKernel t : ℂ)) z = 1 / (z + 1 / 2) := by
  rw [causalInnerKernel_eq_half_power]
  simpa using halfExponentialPower_laplace 0 z hz

theorem causalInnerOperator_laplace (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (causalInnerOperator f : ProbeL2) =
      causalInnerMultiplier z * CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  rw [causalInnerOperator_apply,
    ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hz 0,
    inner_sub_right, CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    causalKernelOperator_laplace _ _ _ z hz, causalInnerKernel_laplace z hz.le]
  unfold causalInnerMultiplier
  have hne : z + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hid : 1 - 1 / (z + 1 / 2) = (z - 1 / 2) / (z + 1 / 2) := by
    apply (eq_div_iff hne).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
    ring
  calc
    _ = (1 - 1 / (z + 1 / 2)) * CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by ring
    _ = _ := by rw [hid]

/-- The causal all-pass operator has a proper range: its half-plane moment
at 1/2 vanishes, while the exponential witness has nonzero self-pairing. -/
theorem causalInnerOperator_not_surjective : ¬ Function.Surjective causalInnerOperator := by
  have hp : 0 < (1 / 2 : ℂ).re := by norm_num
  let w := CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) hp 0
  intro honto
  obtain ⟨f, hf⟩ := honto w
  have hm := causalInnerOperator_laplace (1 / 2 : ℂ) hp f
  rw [hf, show causalInnerMultiplier (1 / 2 : ℂ) = 0 by norm_num [causalInnerMultiplier],
    zero_mul, ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0] at hm
  change inner ℂ w w = 0 at hm
  have hnorm : ‖w‖ ^ 2 = 1 := by
    simpa only [w, show (1 / (2 * (1 / 2 : ℂ).re) : ℝ) = 1 by norm_num] using
      probeLaplaceWitness_norm_sq (1 / 2 : ℂ) hp
  have hr : ‖w‖ ^ 2 = 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hm]
    rfl
  linarith

theorem causalInnerKernel_measurable : Measurable causalInnerKernel := by
  unfold causalInnerKernel
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem causalInnerKernel_abs_le_one (t : ℝ) : |causalInnerKernel t| ≤ 1 := by
  by_cases ht : 0 ≤ t
  · rw [causalInnerKernel, if_pos ht, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · simp [causalInnerKernel, ht]

theorem causalInnerKernel_memLp : MemLp (fun t : ℝ => (causalInnerKernel t : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (causalInnerKernel t : ℂ)) volume :=
    causalInnerKernel_measurable.complex_ofReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply causalInnerKernel_integrable.norm.mono' (hm.norm.pow 2)
  filter_upwards with t
  change ‖‖(causalInnerKernel t : ℂ)‖ ^ 2‖ ≤ ‖causalInnerKernel t‖
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs]
  nlinarith [abs_nonneg (causalInnerKernel t), causalInnerKernel_abs_le_one t]

/-- The same literal causal formula acts on the whole line. -/
def fullCausalInnerOperator : ProbeL2 →L[ℂ] ProbeL2 :=
  ContinuousLinearMap.id ℂ ProbeL2 -
    kernelL2Operator causalInnerKernel causalInnerKernel_integrable

def fullCausalInnerPhysical (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t - ∫ s : ℝ, (causalInnerKernel s : ℂ) * f (t - s)

theorem fullCausalInnerPhysical_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fullCausalInnerPhysical f) :=
  hf.sub (causalInnerKernel_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hf)

theorem fullCausalInnerOperator_coeFn (f : ProbeL2) :
    fullCausalInnerOperator f =ᵐ[volume] fullCausalInnerPhysical f := by
  have hk := kernelL2Operator_coeFn_pointwise causalInnerKernel causalInnerKernel_integrable
    causalInnerKernel_measurable causalInnerKernel_memLp f
  filter_upwards [Lp.coeFn_sub f (kernelL2Operator causalInnerKernel causalInnerKernel_integrable f),
    hk] with t ht hkt
  change (f - kernelL2Operator causalInnerKernel causalInnerKernel_integrable f) t = _
  rw [ht]
  change f t - kernelL2Operator causalInnerKernel causalInnerKernel_integrable f t = _
  rw [hkt]
  rfl

theorem fullCausalInnerOperator_coeFn_of_representative (f : ProbeL2) (g : ℝ → ℂ)
    (hfg : f =ᵐ[volume] g) :
    fullCausalInnerOperator f =ᵐ[volume] fullCausalInnerPhysical g := by
  apply (fullCausalInnerOperator_coeFn f).trans
  filter_upwards [hfg] with t ht
  rw [fullCausalInnerPhysical, fullCausalInnerPhysical, ht]
  congr 1
  apply integral_congr_ae
  exact ((volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq hfg).mono
    fun s hs => congrArg (fun z : ℂ => (causalInnerKernel s : ℂ) * z) hs

theorem causalInnerKernel_logFourier (tau : ℝ) :
    OPICAFollowup.logFourier (fun t => (causalInnerKernel t : ℂ)) tau =
      1 / ((tau : ℂ) * Complex.I + 1 / 2) := by
  have h := causalInnerKernel_laplace ((tau : ℂ) * Complex.I) (by simp)
  unfold OPICAFollowup.logFourier probeLaplace at *
  convert h using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  push_cast
  ring

private theorem logFourier_integrand_integrable {f : ℝ → ℂ} (hf : Integrable f) (tau : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t) := by
  have hm : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t) volume :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply hf.norm.mono' hm
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem imaginaryDamping_eq (f : ℝ → ℂ) (tau : ℝ) :
    (fun t : ℝ => Complex.exp (-((tau : ℂ) * Complex.I) * (t : ℂ)) * f t) =
      fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t := by
  ext t
  congr 2
  push_cast
  ring

private theorem probeLaplace_imaginary (f : ℝ → ℂ) (tau : ℝ) :
    probeLaplace f ((tau : ℂ) * Complex.I) = OPICAFollowup.logFourier f tau := by
  unfold probeLaplace OPICAFollowup.logFourier
  rw [imaginaryDamping_eq]

theorem fullCausalInnerPhysical_logFourier {f : ℝ → ℂ} (hf : Integrable f) (tau : ℝ) :
    OPICAFollowup.logFourier (fullCausalInnerPhysical f) tau =
      causalInnerMultiplier ((tau : ℂ) * Complex.I) * OPICAFollowup.logFourier f tau := by
  let conv : ℝ → ℂ := (fun t => (causalInnerKernel t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hconv : Integrable conv := causalInnerKernel_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hf
  have hsub : OPICAFollowup.logFourier (fullCausalInnerPhysical f) tau =
      OPICAFollowup.logFourier f tau - OPICAFollowup.logFourier conv tau := by
    unfold OPICAFollowup.logFourier fullCausalInnerPhysical
    simp_rw [mul_sub]
    change (∫ t : ℝ, Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t -
      Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * conv t) = _
    rw [integral_sub (logFourier_integrand_integrable hf tau)
      (logFourier_integrand_integrable hconv tau)]
  have hkD : Integrable (fun t : ℝ => Complex.exp (-((tau : ℂ) * Complex.I) * (t : ℂ)) *
      (causalInnerKernel t : ℂ)) := by
    rw [imaginaryDamping_eq]
    exact logFourier_integrand_integrable causalInnerKernel_integrable.ofReal tau
  have hfD : Integrable (fun t : ℝ => Complex.exp (-((tau : ℂ) * Complex.I) * (t : ℂ)) * f t) := by
    rw [imaginaryDamping_eq]
    exact logFourier_integrand_integrable hf tau
  have hconvFT := (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t : ℝ => (causalInnerKernel t : ℂ)) f ((tau : ℂ) * Complex.I) hkD hfD).2
  change probeLaplace conv ((tau : ℂ) * Complex.I) =
    probeLaplace (fun t : ℝ => (causalInnerKernel t : ℂ)) ((tau : ℂ) * Complex.I) *
      probeLaplace f ((tau : ℂ) * Complex.I) at hconvFT
  simp_rw [probeLaplace_imaginary] at hconvFT
  rw [hsub, hconvFT, causalInnerKernel_logFourier]
  have hne : (tau : ℂ) * Complex.I + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hid : 1 - 1 / ((tau : ℂ) * Complex.I + 1 / 2) =
      causalInnerMultiplier ((tau : ℂ) * Complex.I) := by
    unfold causalInnerMultiplier
    apply (eq_div_iff hne).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
    ring
  rw [← hid]
  ring

set_option maxHeartbeats 200000 in
private theorem fullCausalInnerOperator_norm_schwartz (phi : SchwartzMap ℝ ℂ) :
    ‖fullCausalInnerOperator (phi.toLp 2 (volume : Measure ℝ))‖ =
      ‖phi.toLp 2 (volume : Measure ℝ)‖ := by
  let f : ProbeL2 := phi.toLp 2 (volume : Measure ℝ)
  have hphi : (f : ℝ → ℂ) =ᵐ[volume] phi := phi.coeFn_toLp 2 (volume : Measure ℝ)
  have hae : (fullCausalInnerOperator f : ℝ → ℂ) =ᵐ[volume] fullCausalInnerPhysical phi :=
    fullCausalInnerOperator_coeFn_of_representative f phi hphi
  have hf2 : MemLp (fullCausalInnerPhysical phi) 2 volume :=
    MemLp.ae_eq hae (Lp.memLp (fullCausalInnerOperator f))
  have hfp := OPICAFollowup.logFourier_plancherel
    (fullCausalInnerPhysical_integrable phi.integrable) hf2
  have hpp := OPICAFollowup.logFourier_plancherel phi.integrable (phi.memLp 2 volume)
  have hfreq (tau : ℝ) :
      ‖OPICAFollowup.logFourier (fullCausalInnerPhysical phi) tau‖ ^ 2 =
        ‖OPICAFollowup.logFourier phi tau‖ ^ 2 := by
    rw [fullCausalInnerPhysical_logFourier phi.integrable tau, norm_mul,
      causalInnerMultiplier_boundary_norm, one_mul]
  have henergy : (∫ t : ℝ, ‖fullCausalInnerPhysical phi t‖ ^ 2) =
      ∫ t : ℝ, ‖phi t‖ ^ 2 := by
    rw [hfp.2, hpp.2]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hfreq)
  have hs : ‖fullCausalInnerOperator f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [OPICAFollowup.L2_norm_sq_eq_integral, OPICAFollowup.L2_norm_sq_eq_integral]
    calc
      _ = ∫ t : ℝ, ‖fullCausalInnerPhysical phi t‖ ^ 2 :=
        integral_congr_ae (hae.mono fun t ht => by rw [ht])
      _ = ∫ t : ℝ, ‖phi t‖ ^ 2 := henergy
      _ = _ := integral_congr_ae (hphi.mono fun t ht => by rw [ht])
  change ‖fullCausalInnerOperator f‖ = ‖f‖
  nlinarith [norm_nonneg (fullCausalInnerOperator f), norm_nonneg f]

/-- Actual full-line norm preservation, established first on Schwartz inputs
by convolution and Plancherel, then on all L2 inputs by density. -/
theorem fullCausalInnerOperator_norm (f : ProbeL2) : ‖fullCausalInnerOperator f‖ = ‖f‖ := by
  apply DenseRange.induction_on (p := fun f : ProbeL2 => ‖fullCausalInnerOperator f‖ = ‖f‖)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq fullCausalInnerOperator.continuous.norm continuous_norm
  · intro phi
    exact fullCausalInnerOperator_norm_schwartz phi

/-- Restriction preserves the actual causal norm; it does not turn the proper
causal range into the whole causal space. -/
theorem causalInnerOperator_norm (f : CausalProbeL2) : ‖causalInnerOperator f‖ = ‖f‖ := by
  change ‖(causalInnerOperator f : ProbeL2)‖ = ‖(f : ProbeL2)‖
  exact fullCausalInnerOperator_norm (f : ProbeL2)

/-- The exact compact-rectangle rational estimate used after isometric
reduction. It is independent of any zero-free theorem. -/
theorem classicalProbeMultiplier_rectangle_lower (z : ℂ)
    (hdelta0 : (1 / 4 : ℝ) ≤ z.re) (hdelta1 : z.re ≤ 3 / 8)
    (htau0 : (1 : ℝ) ≤ |z.im|) (htau1 : |z.im| ≤ 2) :
    (8192 / 93025 : ℝ) ≤ 2 * z.re * ‖classicalProbeMultiplier z‖ ^ 2 := by
  let u : ℝ := z.im ^ 2
  let a : ℝ := (z.re + 1 / 2) ^ 2
  have hu0 : 1 ≤ u := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) htau0 2
    simpa only [sq_abs, one_pow] using h
  have hu1 : u ≤ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg z.im) htau1 2
    norm_num only [sq_abs, OfNat.ofNat] at h ⊢
    exact h
  have ha0 : 0 ≤ a := sq_nonneg _
  have ha1 : a ≤ 49 / 64 := by dsimp [a]; nlinarith
  have hd : 0 < a + u := by linarith
  have hpoly : (8192 / 93025 : ℝ) * (u + 49 / 64) ^ 2 ≤ u / 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hu1)
      (show 0 ≤ u - 2401 / 16384 by linarith)
    nlinarith
  have hden : (a + u) ^ 2 ≤ (u + 49 / 64) ^ 2 := by nlinarith
  have hnum : u / 2 ≤ 2 * z.re * ((z.re - 1 / 2) ^ 2 + u) := by
    have hp := mul_nonneg (show 0 ≤ 2 * z.re - 1 / 2 by linarith)
      (show 0 ≤ (z.re - 1 / 2) ^ 2 + u by positivity)
    nlinarith [sq_nonneg (z.re - 1 / 2)]
  have hne : z + 1 / 2 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hnorm : ‖classicalProbeMultiplier z‖ ^ 2 =
      ((z.re - 1 / 2) ^ 2 + u) / (a + u) ^ 2 := by
    have hplus : ‖z + 1 / 2‖ ^ 2 = a + u := by
      norm_num [Complex.sq_norm, Complex.normSq_apply, a, u]
      <;> ring
    have hminus : ‖z - 1 / 2‖ ^ 2 = (z.re - 1 / 2) ^ 2 + u := by
      norm_num [Complex.sq_norm, Complex.normSq_apply, u]
      <;> ring
    calc
      _ = ‖z - 1 / 2‖ ^ 2 / (‖z + 1 / 2‖ ^ 2) ^ 2 := by
        rw [classicalProbeMultiplier, norm_div, div_pow, norm_pow]
      _ = _ := by rw [hplus, hminus]
  rw [hnorm, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hc := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 8192 / 93025)
  linarith

theorem reduced_probe_source_rectangle_lower (z : ℂ)
    (hdelta0 : (1 / 4 : ℝ) ≤ z.re) (hdelta1 : z.re ≤ 3 / 8)
    (htau0 : (1 : ℝ) ≤ |z.im|) (htau1 : |z.im| ≤ 2) :
    (4396431852289 / 49942416588800 : ℝ) ≤
      2 * z.re * ‖classicalProbeMultiplier z * QPlus z‖ ^ 2 := by
  have hrat := classicalProbeMultiplier_rectangle_lower z hdelta0 hdelta1 htau0 htau1
  have hq := QPlus_baseline_rectangle_lower z (by linarith) hdelta1 htau1
  have hqsq : (2096767 / 2097152 : ℝ) ^ 2 ≤ ‖QPlus z‖ ^ 2 := by nlinarith [norm_nonneg (QPlus z)]
  have hnonneg : 0 ≤ 2 * z.re * ‖classicalProbeMultiplier z‖ ^ 2 := by positivity
  have hmul := mul_le_mul hrat hqsq (by norm_num : (0 : ℝ) ≤ (2096767 / 2097152) ^ 2) hnonneg
  calc
    _ = (8192 / 93025 : ℝ) * (2096767 / 2097152 : ℝ) ^ 2 := by norm_num
    _ ≤ (2 * z.re * ‖classicalProbeMultiplier z‖ ^ 2) * ‖QPlus z‖ ^ 2 := hmul
    _ = _ := by rw [norm_mul, mul_pow]; ring

/-- One fixed physical filter applied to the unchanged native finite residual. -/
def fixedFilteredProbeResidual {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  fixedFilterOperator (probeResidual x)

theorem probeResidual_laplace_at_right_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {N : ℕ} (x : Fin N → ℂ) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0 (probeResidual x : ProbeL2) =
      CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2) := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  rw [probeResidual, ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0,
    inner_sub_right, CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    probeFiniteOutput_eq_operator, probe_laplace_annihilates_range rho hright,
    sub_zero, probeTarget_laplace_eq_physical, probeV_laplace hp.le]

def fixedFilteredZeroBound (rho : zetaZeroConfig.carrier) : ℝ :=
  Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
    ‖fixedFilterMultiplier ((rho : ℂ) - 1 / 2) *
      (CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2))‖

/-- Every finite trial has a strict positive lower at each actual right zero,
including multiple zeros. No inverse filter is used. -/
theorem fixed_filtered_native_zero_separation (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    0 < fixedFilteredZeroBound rho ∧
      ∀ (N : ℕ) (x : Fin N → ℂ),
        fixedFilteredZeroBound rho ≤ ‖fixedFilteredProbeResidual x‖ := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  have hv : CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
      JPlus ((rho : ℂ) - 1 / 2) ≠ 0 :=
    mul_ne_zero (probe_rational_multiplier_ne_zero rho)
      (JPlus_ne_zero_at_off_line_zero rho (ne_of_gt hright))
  constructor
  · exact mul_pos (Real.sqrt_pos.2 (by positivity))
      (norm_pos_iff.2 (mul_ne_zero (fixedFilterMultiplier_ne_zero hp.le) hv))
  · intro N x
    have hb := probe_laplace_evaluation_bound _ hp (fixedFilteredProbeResidual x)
    rw [fixedFilteredProbeResidual, fixedFilterOperator_laplace _ hp,
      probeResidual_laplace_at_right_zero rho hright] at hb
    exact hb

/-- The approximation premise remains an explicit, unproved proposition. Its
trials may have any finite dimensions, including a cofinal subsequence. -/
def FixedFilteredNativeApproximation : Prop :=
  ∃ (dims : ℕ → ℕ) (trials : (k : ℕ) → Fin (dims k) → ℂ),
    Filter.Tendsto (fun k => ‖fixedFilteredProbeResidual (trials k)‖)
      Filter.atTop (𝓝 0)

/-- Conditional RH consumer for one fixed physical B and the original source.
The antecedent is not manufactured from a raw residual estimate. -/
theorem rh_of_fixed_filtered_native_approximation
    (happrox : FixedFilteredNativeApproximation) : RiemannHypothesis := by
  rcases happrox with ⟨dims, trials, htendsto⟩
  have hnoRight (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re) : False := by
    have hsep := fixed_filtered_native_zero_separation rho hright
    have hnonpos : fixedFilteredZeroBound rho ≤ 0 :=
      ge_of_tendsto htendsto (Filter.Eventually.of_forall fun k => hsep.2 (dims k) (trials k))
    exact (not_le_of_gt hsep.1) hnonpos
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    ExceptionalZero.isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by simpa using hs
  let rho : zetaZeroConfig.carrier := ⟨s, hmem⟩
  by_contra hoff
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · let rhor : zetaZeroConfig.carrier :=
      ⟨Zeta23.reflect s, zetaZeroConfig.reflect_mem s hmem⟩
    have hr : 1 / 2 < (rhor : ℂ).re := by
      change 1 / 2 < (Zeta23.reflect s).re
      simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    exact hnoRight rhor hr
  · exact hnoRight rho hright

/-- Literal stable-factor relation beneath the classical comparison source. -/
theorem classicalProbeKernel_eq_probeC_plus_inner_convolution (t : ℝ) :
    classicalProbeKernel t = probeC t +
      ∫ s : ℝ, causalInnerKernel s * probeC (t - s) := by
  by_cases ht : 0 ≤ t
  · have hfun : (fun s : ℝ => causalInnerKernel s * probeC (t - s)) =
        (Icc (0 : ℝ) t).indicator (fun s : ℝ =>
          -Real.exp (-t / 2) + 2 * Real.exp (-(3 * t / 2)) * Real.exp s) := by
      ext s
      by_cases hs : s ∈ Icc (0 : ℝ) t
      · have hts : 0 ≤ t - s := by linarith [hs.2]
        rw [indicator_of_mem hs]
        simp only [causalInnerKernel, if_pos hs.1, probeC, CCM.nativeCompletionCorrection,
          if_pos hts]
        have h1 : Real.exp (-s / 2) * Real.exp (-((t - s) / 2)) =
            Real.exp (-t / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have h3 : Real.exp (-s / 2) * Real.exp (-(3 * (t - s) / 2)) =
            Real.exp (-(3 * t / 2)) * Real.exp s := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        nlinarith [h1, h3]
      · rw [indicator_of_notMem hs]
        by_cases hs0 : 0 ≤ s
        · have hts : t - s < 0 := by
            have hst : ¬s ≤ t := fun h => hs ⟨hs0, h⟩
            linarith
          rw [probeC_zero_of_neg (t - s) hts, mul_zero]
        · rw [causalInnerKernel_zero_of_neg s (lt_of_not_ge hs0), zero_mul]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
    have hint : IntervalIntegrable
        (fun s : ℝ => 2 * Real.exp (-(3 * t / 2)) * Real.exp s) volume 0 t :=
      (by fun_prop : Continuous (fun s : ℝ =>
        2 * Real.exp (-(3 * t / 2)) * Real.exp s)).intervalIntegrable 0 t
    rw [intervalIntegral.integral_add intervalIntegrable_const
      hint,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_exp]
    simp only [sub_zero, Real.exp_zero, smul_eq_mul]
    have he : Real.exp (-(3 * t / 2)) * Real.exp t = Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [classicalProbeKernel, if_pos ht, probeC, CCM.nativeCompletionCorrection,
      show -(t / 2) = -t / 2 by ring]
    nlinarith [he]
  · have hneg : t < 0 := lt_of_not_ge ht
    rw [show classicalProbeKernel t = 0 by simp [classicalProbeKernel, ht],
      probeC_zero_of_neg t hneg]
    simp only [zero_add]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards with s
    change causalInnerKernel s * probeC (t - s) = 0
    by_cases hs : s < 0
    · rw [causalInnerKernel_zero_of_neg s hs, zero_mul]
    · rw [probeC_zero_of_neg (t - s) (by linarith [le_of_not_gt hs]), mul_zero]

theorem classicalProbeKernel_eq_half_powers :
    classicalProbeKernel = fun t => halfExponentialPower 0 t - halfExponentialPower 1 t := by
  ext t
  by_cases ht : 0 ≤ t
  · simp only [classicalProbeKernel, halfExponentialPower, if_pos ht, pow_zero, pow_one,
      one_mul]
    rw [show -(1 / 2 : ℝ) * t = -t / 2 by ring]
    ring
  · simp [classicalProbeKernel, halfExponentialPower, ht]

theorem classicalProbeKernel_integrable : Integrable classicalProbeKernel := by
  rw [classicalProbeKernel_eq_half_powers]
  exact (halfExponentialPower_integrable 0).sub (halfExponentialPower_integrable 1)

open scoped BigOperators

theorem nativeIntegerCoefficient_exp_shift {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    CCM.nativeIntegerCoefficient n * Real.exp (-(t - Real.log n) / 2) =
      Real.exp (-t / 2) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hroot : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnreal]
    congr 1
    ring
  unfold CCM.nativeIntegerCoefficient
  rw [hroot, one_div, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem classicalProbeKernel_weighted_atom {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (hlog : Real.log n ≤ t) :
    CCM.nativeIntegerCoefficient n * classicalProbeKernel (t - Real.log n) =
      Real.exp (-t / 2) * (1 - t + Real.log n) := by
  rw [classicalProbeKernel, if_pos (sub_nonneg.mpr hlog), ← mul_assoc,
    nativeIntegerCoefficient_exp_shift hn]
  ring

theorem log_factorial_eq_sum_range (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.log ((n + 1 : ℕ) : ℝ)) =
      Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- The required literal floor/log-factorial kernel is the unchanged causal
integer completion of u0, with the zero index retained explicitly as zero. -/
theorem classicalCompletionKernel_eq_integer_completion (t : ℝ) :
    classicalCompletionKernel t = CCM.nativeIntegerTranslateAction classicalProbeKernel t := by
  rw [CCM.nativeIntegerTranslateAction_eq_causal_history
    (fun s hs => by simp [classicalProbeKernel, not_le_of_gt hs]) t]
  let N : ℕ := ⌊Real.exp t⌋₊
  change classicalCompletionKernel t =
    ∑ n ∈ Finset.range (N + 1), CCM.nativeIntegerCoefficient n *
      classicalProbeKernel (t - Real.log n)
  rw [Finset.sum_range_succ']
  have hzero : CCM.nativeIntegerCoefficient 0 = 0 := by norm_num [CCM.nativeIntegerCoefficient]
  simp only [hzero, zero_mul, zero_add, add_zero]
  by_cases ht : 0 ≤ t
  · symm
    calc
      _ = ∑ n ∈ Finset.range N, Real.exp (-t / 2) *
          (1 - t + Real.log (n + 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnN : n + 1 ≤ N := by simp only [Finset.mem_range] at hn; omega
        have hexp : ((n + 1 : ℕ) : ℝ) ≤ Real.exp t :=
          (Nat.le_floor_iff (Real.exp_pos t).le).mp hnN
        exact classicalProbeKernel_weighted_atom (by omega)
          ((Real.log_le_iff_le_exp (by positivity)).mpr hexp)
      _ = Real.exp (-t / 2) * ((N : ℝ) * (1 - t) + Real.log (N.factorial : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, log_factorial_eq_sum_range]
      _ = _ := by
        rw [classicalCompletionKernel, if_pos ht]
        dsimp [N]
        ring
  · have hfloor : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (lt_of_not_ge ht))
    simp [N, hfloor, classicalCompletionKernel, ht]

theorem classicalProbeKernel_eq_probeC_plus_source_first (t : ℝ) :
    classicalProbeKernel t = probeC t + ∫ s : ℝ, probeC s * causalInnerKernel (t - s) := by
  rw [classicalProbeKernel_eq_probeC_plus_inner_convolution]
  congr 1
  have h := integral_sub_left_eq_self
    (fun s : ℝ => causalInnerKernel s * probeC (t - s)) t
    (μ := (volume : Measure ℝ))
  simpa only [sub_sub_cancel, mul_comm] using h.symm

/-- The native inclusive floor kernel commutes with this actual stable
causal exponential through a finite history at each time. -/
theorem innerConvolution_native_integer_completion (t : ℝ) :
    (∫ s : ℝ, CCM.nativePositiveCompletion s * causalInnerKernel (t - s)) =
      ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), CCM.nativeIntegerCoefficient n *
        ∫ s : ℝ, probeC s * causalInnerKernel ((t - Real.log n) - s) := by
  let history := Finset.range (⌊Real.exp t⌋₊ + 1)
  have hpoint : (fun s : ℝ => CCM.nativePositiveCompletion s * causalInnerKernel (t - s)) =
      fun s => ∑ n ∈ history, CCM.nativeIntegerCoefficient n *
        probeC (s - Real.log n) * causalInnerKernel (t - s) := by
    ext s
    by_cases hs : s ≤ t
    · rw [CCM.nativePositiveCompletion_eq_integerTranslateCorrection,
        CCM.nativeIntegerTranslateAction_eq_causal_history_at_horizon
          (fun _ hx => CCM.nativeCompletionCorrection_zero_of_neg hx) hs,
        Finset.sum_mul]
      rfl
    · rw [causalInnerKernel_zero_of_neg (t - s) (by linarith), mul_zero]
      simp only [mul_zero, Finset.sum_const_zero]
  have hint (n : ℕ) : Integrable (fun s : ℝ => CCM.nativeIntegerCoefficient n *
      probeC (s - Real.log n) * causalInnerKernel (t - s)) := by
    have hm : AEStronglyMeasurable
        (fun s : ℝ => probeC (s - Real.log n) * causalInnerKernel (t - s)) volume :=
      ((probeC_measurable.comp (by fun_prop)).mul
        (causalInnerKernel_measurable.comp (by fun_prop))).aestronglyMeasurable
    have hprod : Integrable (fun s : ℝ => probeC (s - Real.log n) *
        causalInnerKernel (t - s)) := by
      apply (probeC_integrable.comp_sub_right (Real.log n)).norm.mono' hm
      filter_upwards with s
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using causalInnerKernel_abs_le_one (t - s)
    simpa only [mul_assoc] using hprod.const_mul (CCM.nativeIntegerCoefficient n)
  rw [hpoint, integral_finsetSum _ (fun n _ => hint n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hf : (fun s : ℝ => CCM.nativeIntegerCoefficient n * probeC (s - Real.log n) *
      causalInnerKernel (t - s)) = fun s => CCM.nativeIntegerCoefficient n *
        (probeC (s - Real.log n) * causalInnerKernel (t - s)) := by ext s; ring
  rw [hf, integral_const_mul]
  congr 1
  have hshift : (fun s : ℝ => probeC (s - Real.log n) * causalInnerKernel (t - s)) =
      fun s => (fun u : ℝ => probeC u * causalInnerKernel ((t - Real.log n) - u))
        (s - Real.log n) := by
    ext s
    congr 2
    ring
  rw [hshift]
  exact integral_sub_right_eq_self
    (fun u : ℝ => probeC u * causalInnerKernel ((t - Real.log n) - u))
    (Real.log n) (μ := (volume : Measure ℝ))

/-- This is the literal required h0, not a newly defined surrogate. -/
theorem classicalCompletionKernel_eq_native_plus_inner_convolution (t : ℝ) :
    classicalCompletionKernel t = CCM.nativePositiveCompletion t +
      ∫ s : ℝ, CCM.nativePositiveCompletion s * causalInnerKernel (t - s) := by
  have ha := CCM.nativePositiveCompletion_eq_integerTranslateCorrection t
  rw [CCM.nativeIntegerTranslateAction_eq_causal_history
    (fun _ hs => CCM.nativeCompletionCorrection_zero_of_neg hs) t] at ha
  change CCM.nativePositiveCompletion t =
    ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), CCM.nativeIntegerCoefficient n *
      probeC (t - Real.log n) at ha
  rw [classicalCompletionKernel_eq_integer_completion,
    CCM.nativeIntegerTranslateAction_eq_causal_history
      (fun s hs => by simp [classicalProbeKernel, not_le_of_gt hs]) t]
  simp_rw [classicalProbeKernel_eq_probeC_plus_source_first, mul_add]
  rw [Finset.sum_add_distrib, ← ha, ← innerConvolution_native_integer_completion]

theorem classicalCompletionKernel_integrable : Integrable classicalCompletionKernel := by
  have heq : classicalCompletionKernel = fun t => CCM.nativePositiveCompletion t +
      ∫ s : ℝ, CCM.nativePositiveCompletion s * causalInnerKernel (t - s) :=
    funext classicalCompletionKernel_eq_native_plus_inner_convolution
  rw [heq]
  exact CCM.nativePositiveCompletion_integrable.add
    (CCM.nativePositiveCompletion_integrable.integrable_convolution
      (L := ContinuousLinearMap.mul ℝ ℝ) causalInnerKernel_integrable)

theorem kernelL2Operator_coeFn_of_representative (k : ℝ → ℝ) (hk : Integrable k)
    (hm : Measurable k) (hk2 : MemLp (fun t : ℝ => (k t : ℂ)) 2 volume)
    (f : ProbeL2) (g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    kernelL2Operator k hk f =ᵐ[volume] fun t => ∫ s : ℝ, (k s : ℂ) * g (t - s) := by
  apply (kernelL2Operator_coeFn_pointwise k hk hm hk2 f).trans
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  exact ((volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq hfg).mono
    fun s hs => congrArg (fun z : ℂ => (k s : ℂ) * z) hs

theorem realKernelConvolution_coe (k f : ℝ → ℝ) (t : ℝ) :
    (∫ s : ℝ, (k s : ℂ) * (f (t - s) : ℂ)) =
      ((∫ s : ℝ, k s * f (t - s) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => (Complex.ofReal_mul _ _).symm

theorem realKernelConvolution_commute (k f : ℝ → ℝ) (t : ℝ) :
    (∫ s : ℝ, k s * f (t - s)) = ∫ s : ℝ, f s * k (t - s) := by
  have h := integral_sub_left_eq_self (fun s : ℝ => k s * f (t - s)) t
    (μ := (volume : Measure ℝ))
  simpa only [sub_sub_cancel, mul_comm] using h.symm

theorem realKernelL2_filter_plus_memLp (k f : ℝ → ℝ) (hk : Integrable k)
    (hm : Measurable k) (hk2 : MemLp (fun t : ℝ => (k t : ℂ)) 2 volume)
    (hf2 : MemLp (fun t : ℝ => (f t : ℂ)) 2 volume) :
    MemLp (fun t : ℝ => ((f t + ∫ s : ℝ, k s * f (t - s) : ℝ) : ℂ)) 2 volume := by
  let F : ProbeL2 := hf2.toLp (fun t : ℝ => (f t : ℂ))
  let KF : ProbeL2 := kernelL2Operator k hk F
  have hF : F =ᵐ[volume] fun t : ℝ => (f t : ℂ) := hf2.coeFn_toLp
  have hKF : KF =ᵐ[volume] fun t : ℝ => ∫ s : ℝ, (k s : ℂ) * (f (t - s) : ℂ) :=
    kernelL2Operator_coeFn_of_representative k hk hm hk2 F _ hF
  have hsum : (F + KF : ProbeL2) =ᵐ[volume]
      fun t : ℝ => ((f t + ∫ s : ℝ, k s * f (t - s) : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_add F KF, hF, hKF] with t ht hf hk
    rw [ht]
    change F t + KF t = _
    rw [hf, hk, realKernelConvolution_coe, ← Complex.ofReal_add]
  exact MemLp.ae_eq hsum (Lp.memLp (F + KF))

theorem classicalProbeKernel_memLp :
    MemLp (fun t : ℝ => (classicalProbeKernel t : ℂ)) 2 volume := by
  have heq : (fun t : ℝ => (classicalProbeKernel t : ℂ)) = fun t : ℝ =>
      ((probeC t + ∫ s : ℝ, causalInnerKernel s * probeC (t - s) : ℝ) : ℂ) :=
    funext fun t => congrArg Complex.ofReal (classicalProbeKernel_eq_probeC_plus_inner_convolution t)
  rw [heq]
  exact realKernelL2_filter_plus_memLp causalInnerKernel probeC causalInnerKernel_integrable
    causalInnerKernel_measurable causalInnerKernel_memLp probeC_memLp

theorem classicalCompletionKernel_memLp :
    MemLp (fun t : ℝ => (classicalCompletionKernel t : ℂ)) 2 volume := by
  have ha2 : MemLp (fun t : ℝ => (CCM.nativePositiveCompletion t : ℂ)) 2 volume := by
    simpa [CCM.nativeDampedCompletionKernel] using
      (CCM.nativeDampedCompletionKernel_complex_memLp_two (epsilon := 0) (by norm_num))
  have heq : (fun t : ℝ => (classicalCompletionKernel t : ℂ)) = fun t : ℝ =>
      ((CCM.nativePositiveCompletion t +
        ∫ s : ℝ, causalInnerKernel s * CCM.nativePositiveCompletion (t - s) : ℝ) : ℂ) := by
    ext t
    rw [classicalCompletionKernel_eq_native_plus_inner_convolution,
      realKernelConvolution_commute CCM.nativePositiveCompletion causalInnerKernel]
  rw [heq]
  exact realKernelL2_filter_plus_memLp causalInnerKernel CCM.nativePositiveCompletion
    causalInnerKernel_integrable causalInnerKernel_measurable causalInnerKernel_memLp ha2

def comparisonU0 : CausalProbeL2 :=
  ⟨classicalProbeKernel_memLp.toLp (fun t : ℝ => (classicalProbeKernel t : ℂ)), by
    filter_upwards [classicalProbeKernel_memLp.coeFn_toLp] with t ht
    intro hneg
    rw [ht]
    simp [classicalProbeKernel, not_le_of_gt hneg]⟩

def comparisonH0 : CausalProbeL2 :=
  ⟨classicalCompletionKernel_memLp.toLp (fun t : ℝ => (classicalCompletionKernel t : ℂ)), by
    filter_upwards [classicalCompletionKernel_memLp.coeFn_toLp] with t ht
    intro hneg
    rw [ht]
    simp [classicalCompletionKernel, not_le_of_gt hneg]⟩

theorem comparisonU0_coeFn : (comparisonU0 : ProbeL2) =ᵐ[volume]
    fun t : ℝ => (classicalProbeKernel t : ℂ) := classicalProbeKernel_memLp.coeFn_toLp

theorem comparisonH0_coeFn : (comparisonH0 : ProbeL2) =ᵐ[volume]
    fun t : ℝ => (classicalCompletionKernel t : ℂ) := classicalCompletionKernel_memLp.coeFn_toLp

theorem classicalProbeKernel_laplace (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace (fun t => (classicalProbeKernel t : ℂ)) z = classicalProbeMultiplier z := by
  have heq : (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (classicalProbeKernel t : ℂ)) =
      fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (halfExponentialPower 0 t : ℂ) -
        Complex.exp (-z * (t : ℂ)) * (halfExponentialPower 1 t : ℂ) := by
    ext t
    rw [classicalProbeKernel_eq_half_powers]
    push_cast
    ring
  unfold probeLaplace
  rw [heq, integral_sub (halfExponentialPower_damped_integrable 0 z hz)
    (halfExponentialPower_damped_integrable 1 z hz)]
  change probeLaplace (fun t => (halfExponentialPower 0 t : ℂ)) z -
    probeLaplace (fun t => (halfExponentialPower 1 t : ℂ)) z = _
  rw [halfExponentialPower_laplace 0 z hz, halfExponentialPower_laplace 1 z hz]
  norm_num only [Nat.factorial, pow_one]
  have hhalf : z + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  unfold classicalProbeMultiplier
  rw [show z - 1 / 2 = (z + 1 / 2) - 1 by ring]
  generalize ha : z + 1 / 2 = a at *
  field_simp [hhalf]
  <;> ring

theorem classicalCompletionKernel_laplace_native (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace (fun t => (classicalCompletionKernel t : ℂ)) z =
      (1 + 1 / (z + 1 / 2)) * CCM.nativePositiveCompletionLaplace z := by
  have hA : Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
      (CCM.nativePositiveCompletion t : ℂ)) := by
    exact CCM.nativeCausalComplexDamping_integrable hz CCM.nativePositiveCompletion_integrable
      (fun _ ht => CCM.nativePositiveCompletion_eq_zero_of_neg ht)
  have hE : Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (causalInnerKernel t : ℂ)) := by
    rw [causalInnerKernel_eq_half_power]
    exact halfExponentialPower_damped_integrable 0 z hz
  have hconv := OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t : ℝ => (CCM.nativePositiveCompletion t : ℂ))
    (fun t : ℝ => (causalInnerKernel t : ℂ)) z hA hE
  have heq : (fun t : ℝ => (classicalCompletionKernel t : ℂ)) = fun t : ℝ =>
      (CCM.nativePositiveCompletion t : ℂ) +
        ∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) * (causalInnerKernel (t - s) : ℂ) := by
    ext t
    rw [classicalCompletionKernel_eq_native_plus_inner_convolution,
      Complex.ofReal_add, realKernelConvolution_coe]
  unfold probeLaplace
  rw [heq]
  simp_rw [mul_add]
  rw [integral_add hA hconv.1, hconv.2]
  change CCM.nativePositiveCompletionLaplace z + CCM.nativePositiveCompletionLaplace z *
    probeLaplace (fun t => (causalInnerKernel t : ℂ)) z = _
  rw [causalInnerKernel_laplace z hz]
  ring

theorem classicalProbeMultiplier_eq_innerPlus_nativeRational (z : ℂ)
    (hhalf : z + 1 / 2 ≠ 0) (hthree : z + 3 / 2 ≠ 0) :
    (1 + 1 / (z + 1 / 2)) * CCM.nativeCompletionRationalMultiplier z =
      classicalProbeMultiplier z := by
  have hid : 1 + 1 / (z + 1 / 2) = (z + 3 / 2) / (z + 1 / 2) := by
    apply (eq_div_iff hhalf).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hhalf]
    ring
  rw [hid]
  unfold CCM.nativeCompletionRationalMultiplier classicalProbeMultiplier
  generalize ha : z + 1 / 2 = a at *
  generalize hc : z + 3 / 2 = c at *
  field_simp [hhalf, hthree]
  <;> ring

/-- The elementary point z=1/2 is excluded from this zeta formula; its true
physical value is proved separately below. -/
theorem classicalCompletionKernel_laplace (z : ℂ) (hz : 0 < z.re) (hne : z ≠ 1 / 2) :
    probeLaplace (fun t => (classicalCompletionKernel t : ℂ)) z =
      classicalProbeMultiplier z * riemannZeta (z + 1 / 2) := by
  have hhalf : z + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hthree : z + 3 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  rw [classicalCompletionKernel_laplace_native z hz.le]
  have hA := CCM.nativePositiveCompletion_complexLaplace hz hne
  change CCM.nativePositiveCompletionLaplace z =
    CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2) at hA
  rw [hA, ← mul_assoc, classicalProbeMultiplier_eq_innerPlus_nativeRational z hhalf hthree]

theorem classicalCompletionKernel_laplace_half :
    probeLaplace (fun t => (classicalCompletionKernel t : ℂ)) (1 / 2) = 1 := by
  rw [classicalCompletionKernel_laplace_native (1 / 2) (by norm_num)]
  have hA := CCM.nativePositiveCompletion_complexLaplace_half
  change CCM.nativePositiveCompletionLaplace (1 / 2) = 1 / 2 at hA
  rw [hA]
  norm_num

theorem comparisonU0_laplace_eq_physical (z : ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (comparisonU0 : ProbeL2) =
      probeLaplace (fun t => (classicalProbeKernel t : ℂ)) z := by
  unfold CCM.nativeCausalLaplaceMoment probeLaplace
  apply integral_congr_ae
  filter_upwards [comparisonU0_coeFn] with t ht
  simp [ht]

theorem comparisonH0_laplace_eq_physical (z : ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (comparisonH0 : ProbeL2) =
      probeLaplace (fun t => (classicalCompletionKernel t : ℂ)) z := by
  unfold CCM.nativeCausalLaplaceMoment probeLaplace
  apply integral_congr_ae
  filter_upwards [comparisonH0_coeFn] with t ht
  simp [ht]


/-- Literal probability-smoothed classical comparison sources. -/
def comparisonU : CausalProbeL2 := qPlusOperator comparisonU0
def comparisonH : CausalProbeL2 := qPlusOperator comparisonH0

theorem qPlusOperator_laplace (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (qPlusOperator f : ProbeL2) =
      QPlus z * CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  exact causalKernelOperator_laplace qPlus qPlus_integrable
    (fun _ ht => qPlus_zero_of_neg ht) z hz f

theorem probeDelay_laplace (z : ℂ) (hz : 0 < z.re) (t : ℝ) (ht : 0 ≤ t)
    (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (probeDelay t ht f : ProbeL2) =
      Complex.exp (-z * (t : ℂ)) * CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  change CCM.nativeCausalLaplaceMoment z 0 (CCM.nativeCompletionL2Delay t (f : ProbeL2)) = _
  rw [CCM.nativeCausalLaplaceMoment_delay z hz 0 f t]
  simp

theorem fixedFilterOperator_delay (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    fixedFilterOperator (probeDelay t ht f) = probeDelay t ht (fixedFilterOperator f) := by
  apply probeCausalLaplace_ext
  intro z hz
  rw [fixedFilterOperator_laplace z hz, probeDelay_laplace z hz,
    probeDelay_laplace z hz, fixedFilterOperator_laplace z hz]
  ring

theorem causalInnerOperator_delay (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    causalInnerOperator (probeDelay t ht f) = probeDelay t ht (causalInnerOperator f) := by
  apply probeCausalLaplace_ext
  intro z hz
  rw [causalInnerOperator_laplace z hz, probeDelay_laplace z hz,
    probeDelay_laplace z hz, causalInnerOperator_laplace z hz]
  ring

theorem qPlusOperator_delay (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    qPlusOperator (probeDelay t ht f) = probeDelay t ht (qPlusOperator f) := by
  apply probeCausalLaplace_ext
  intro z hz
  rw [qPlusOperator_laplace z hz, probeDelay_laplace z hz,
    probeDelay_laplace z hz, qPlusOperator_laplace z hz]
  ring

theorem fixedFilter_target_factorization :
    fixedFilterOperator probeTarget = causalInnerOperator (causalInnerOperator comparisonU) := by
  apply probeCausalLaplace_ext
  intro z hz
  have hh : z + 1 / 2 ≠ 0 := by
    intro he
    have he := congrArg Complex.re he
    norm_num at he
    linarith
  have hc : z + 3 / 2 ≠ 0 := by
    intro he
    have he := congrArg Complex.re he
    norm_num at he
    linarith
  rw [fixedFilterOperator_laplace z hz, probeTarget_laplace_eq_physical,
    probeV_laplace hz.le, JPlus_eq_pole_polynomial_QPlus,
    causalInnerOperator_laplace z hz, causalInnerOperator_laplace z hz,
    comparisonU, qPlusOperator_laplace z hz, comparisonU0_laplace_eq_physical,
    classicalProbeKernel_laplace z hz.le]
  have h := fixedFilter_pole_polynomial_factorization z hh hc
  change fixedFilterMultiplier z * CCM.nativeCompletionRationalMultiplier z *
      (z ^ 2 - 1 / 4) ^ 2 = _ at h
  calc
    _ = (fixedFilterMultiplier z * CCM.nativeCompletionRationalMultiplier z *
      (z ^ 2 - 1 / 4) ^ 2) * QPlus z := by ring
    _ = _ := by rw [h]; ring

theorem fixedFilter_completed_factorization :
    fixedFilterOperator probeCompletedSource = causalInnerOperator (causalInnerOperator comparisonH) := by
  apply probeCausalLaplace_ext
  intro z hz
  rw [fixedFilterOperator_laplace z hz, probeCompletedSource_laplace_eq_physical,
    causalInnerOperator_laplace z hz, causalInnerOperator_laplace z hz,
    comparisonH, qPlusOperator_laplace z hz, comparisonH0_laplace_eq_physical]
  by_cases he : z = 1 / 2
  · subst z
    rw [probeW_laplace_half]
    simp [causalInnerMultiplier]
  · have hh : z + 1 / 2 ≠ 0 := by
      intro he
      have he := congrArg Complex.re he
      norm_num at he
      linarith
    have hc : z + 3 / 2 ≠ 0 := by
      intro he
      have he := congrArg Complex.re he
      norm_num at he
      linarith
    rw [probeW_laplace hz he, JPlus_eq_pole_polynomial_QPlus,
      classicalCompletionKernel_laplace z hz he]
    have h := fixedFilter_pole_polynomial_factorization z hh hc
    change fixedFilterMultiplier z * CCM.nativeCompletionRationalMultiplier z *
      (z ^ 2 - 1 / 4) ^ 2 = _ at h
    calc
      _ = (fixedFilterMultiplier z * CCM.nativeCompletionRationalMultiplier z *
        (z ^ 2 - 1 / 4) ^ 2) * QPlus z * riemannZeta (z + 1 / 2) := by ring
      _ = _ := by rw [h]; ring

def comparisonFiniteResidual {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  comparisonU - ∑ i : Fin N, x i • ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) •
    probeDelay (Real.log ((i.val + 1 : ℕ) : ℝ)) (probe_log_nonneg (Nat.succ_ne_zero i.val)) comparisonH)

def comparisonRawFiniteResidual {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  comparisonU0 - ∑ i : Fin N, x i • ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) •
    probeDelay (Real.log ((i.val + 1 : ℕ) : ℝ)) (probe_log_nonneg (Nat.succ_ne_zero i.val)) comparisonH0)

theorem comparisonFiniteResidual_eq_probability_smoothing {N : ℕ} (x : Fin N → ℂ) :
    comparisonFiniteResidual x = qPlusOperator (comparisonRawFiniteResidual x) := by
  unfold comparisonFiniteResidual comparisonRawFiniteResidual comparisonU comparisonH
  simp only [map_sub, map_sum, map_smul, qPlusOperator_delay]

theorem fixedFilteredProbeResidual_factorization {N : ℕ} (x : Fin N → ℂ) :
    fixedFilteredProbeResidual x =
      causalInnerOperator (causalInnerOperator (comparisonFiniteResidual x)) := by
  unfold fixedFilteredProbeResidual probeResidual probeFiniteOutput comparisonFiniteResidual
  simp only [map_sub, map_sum, map_smul]
  rw [fixedFilter_target_factorization]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [probeColumn_eq_delay (by omega : i.val + 1 ≠ 0), map_smul,
    fixedFilterOperator_delay, fixedFilter_completed_factorization,
    causalInnerOperator_delay, causalInnerOperator_delay]

theorem fixedFilteredProbeResidual_norm_eq {N : ℕ} (x : Fin N → ℂ) :
    ‖fixedFilteredProbeResidual x‖ = ‖comparisonFiniteResidual x‖ := by
  rw [fixedFilteredProbeResidual_factorization, causalInnerOperator_norm, causalInnerOperator_norm]

theorem fixedFilteredProbeResidual_norm_le_raw {N : ℕ} (x : Fin N → ℂ) :
    ‖fixedFilteredProbeResidual x‖ ≤ ‖comparisonRawFiniteResidual x‖ := by
  rw [fixedFilteredProbeResidual_norm_eq, comparisonFiniteResidual_eq_probability_smoothing]
  exact qPlusOperator_contracts _


theorem qPlus_memLp : MemLp (fun t : ℝ => (qPlus t : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp qPlus_contDiff.continuous).memLp_of_hasCompactSupport
    (qPlus_hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero)

def comparisonUPhysical (t : ℝ) : ℂ :=
  ∫ s : ℝ, (qPlus s : ℂ) * (classicalProbeKernel (t - s) : ℂ)

def comparisonHPhysical (t : ℝ) : ℂ :=
  ∫ s : ℝ, (qPlus s : ℂ) * (classicalCompletionKernel (t - s) : ℂ)

theorem comparisonU_coeFn : (comparisonU : ProbeL2) =ᵐ[volume] comparisonUPhysical := by
  exact kernelL2Operator_coeFn_of_representative qPlus qPlus_integrable
    qPlus_contDiff.continuous.measurable qPlus_memLp (comparisonU0 : ProbeL2)
      (fun t : ℝ => (classicalProbeKernel t : ℂ)) comparisonU0_coeFn

theorem comparisonH_coeFn : (comparisonH : ProbeL2) =ᵐ[volume] comparisonHPhysical := by
  exact kernelL2Operator_coeFn_of_representative qPlus qPlus_integrable
    qPlus_contDiff.continuous.measurable qPlus_memLp (comparisonH0 : ProbeL2)
      (fun t : ℝ => (classicalCompletionKernel t : ℂ)) comparisonH0_coeFn

theorem comparisonUPhysical_integrable : Integrable comparisonUPhysical :=
  qPlus_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) classicalProbeKernel_integrable.ofReal

theorem comparisonHPhysical_integrable : Integrable comparisonHPhysical :=
  qPlus_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) classicalCompletionKernel_integrable.ofReal

theorem classicalProbeKernel_logFourier (tau : ℝ) :
    OPICAFollowup.logFourier (fun t : ℝ => (classicalProbeKernel t : ℂ)) tau =
      classicalProbeMultiplier ((tau : ℂ) * Complex.I) := by
  rw [← probeLaplace_imaginary]
  exact classicalProbeKernel_laplace _ (by simp)

theorem classicalCompletionKernel_logFourier (tau : ℝ) :
    OPICAFollowup.logFourier (fun t : ℝ => (classicalCompletionKernel t : ℂ)) tau =
      classicalProbeMultiplier ((tau : ℂ) * Complex.I) *
        riemannZeta ((tau : ℂ) * Complex.I + 1 / 2) := by
  rw [← probeLaplace_imaginary, classicalCompletionKernel_laplace_native _ (by simp)]
  have ha := nativeCompletionLaplace_boundary tau
  rw [mul_comm Complex.I (tau : ℂ)] at ha
  rw [ha, ← mul_assoc]
  congr 1
  apply classicalProbeMultiplier_eq_innerPlus_nativeRational
  · intro h
    have h := congrArg Complex.re h
    norm_num at h
  · intro h
    have h := congrArg Complex.re h
    norm_num at h


theorem comparisonH_laplace_at_right_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0 (comparisonH : ProbeL2) = 0 := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hn : (rho : ℂ) - 1 / 2 ≠ (1 / 2 : ℂ) := by
    intro he
    have he := congrArg Complex.re he
    norm_num at he
    linarith [rho.property.2.2]
  rw [comparisonH, qPlusOperator_laplace _ hp, comparisonH0_laplace_eq_physical,
    classicalCompletionKernel_laplace _ hp hn]
  rw [sub_add_cancel, rho.property.1, mul_zero, mul_zero]

theorem comparisonFiniteResidual_laplace_at_right_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {N : ℕ} (x : Fin N → ℂ) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0
      (comparisonFiniteResidual x : ProbeL2) =
        classicalProbeMultiplier ((rho : ℂ) - 1 / 2) * QPlus ((rho : ℂ) - 1 / 2) := by
  let z : ℂ := (rho : ℂ) - 1 / 2
  have hp : 0 < z.re := by
    change 0 < ((rho : ℂ) - 1 / 2).re
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hh := comparisonH_laplace_at_right_zero rho hright
  change CCM.nativeCausalLaplaceMoment z 0 (comparisonH : ProbeL2) = 0 at hh
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0]
  unfold comparisonFiniteResidual
  rw [inner_sub_right, inner_sum]
  have hterm (i : Fin N) : inner ℂ (CCM.nativeCausalExponentialWitness z hp 0)
      (x i • ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) •
        probeDelay (Real.log ((i.val + 1 : ℕ) : ℝ)) (probe_log_nonneg (Nat.succ_ne_zero i.val)) comparisonH)) = 0 := by
    rw [inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
      inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
      CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      probeDelay_laplace z hp, hh]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const_zero, sub_zero,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    comparisonU, qPlusOperator_laplace z hp, comparisonU0_laplace_eq_physical,
    classicalProbeKernel_laplace z hp.le]
  ring

/-- The witness is evaluated after removal of the proved I squared isometry.
Its squared lower is therefore the reduced U0 QPlus expression. -/
theorem fixedFilteredProbeResidual_reduced_zero_lower (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {N : ℕ} (x : Fin N → ℂ) :
    2 * ((rho : ℂ) - 1 / 2).re *
      ‖classicalProbeMultiplier ((rho : ℂ) - 1 / 2) * QPlus ((rho : ℂ) - 1 / 2)‖ ^ 2 ≤
        ‖fixedFilteredProbeResidual x‖ ^ 2 := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]
    norm_num
    linarith
  have he := probe_laplace_evaluation_bound ((rho : ℂ) - 1 / 2) hp (comparisonFiniteResidual x)
  rw [comparisonFiniteResidual_laplace_at_right_zero rho hright x] at he
  rw [fixedFilteredProbeResidual_norm_eq]
  have hs := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) he 2
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ((rho : ℂ) - 1 / 2).re)] at hs
  exact hs


theorem fixedFilter_column_factorization {n : ℕ} (hn : n ≠ 0) :
    fixedFilterOperator (probeColumn n) = causalInnerOperator (causalInnerOperator
      ((CCM.nativeIntegerCoefficient n : ℂ) •
        probeDelay (Real.log n) (probe_log_nonneg hn) comparisonH)) := by
  rw [probeColumn_eq_delay hn, map_smul, fixedFilterOperator_delay,
    fixedFilter_completed_factorization]
  simp only [map_smul, causalInnerOperator_delay]

/-- The complete literal fixed-filter package. Its finite norm identity retains
both the original probability convolution and the actual dictionary columns. -/
theorem native_probe_fixed_stable_filter :
    Integrable fixedFilterKernel ∧ (∫ t : ℝ, ‖fixedFilterKernel t‖) = 48 ∧
    (∀ z : ℂ, 0 ≤ z.re → probeLaplace (fun t : ℝ => (fixedFilterKernel t : ℂ)) z =
      (z + 3 / 2) / (z + 1 / 2) ^ 5) ∧
    (∀ f : CausalProbeL2, ‖causalInnerOperator f‖ = ‖f‖) ∧
    ¬Function.Surjective causalInnerOperator ∧
    Integrable classicalProbeKernel ∧ MemLp (fun t : ℝ => (classicalProbeKernel t : ℂ)) 2 volume ∧
    Integrable classicalCompletionKernel ∧
      MemLp (fun t : ℝ => (classicalCompletionKernel t : ℂ)) 2 volume ∧
    (∀ z : ℂ, 0 < z.re → z ≠ 1 / 2 →
      probeLaplace (fun t : ℝ => (classicalCompletionKernel t : ℂ)) z =
        ((z - 1 / 2) / (z + 1 / 2) ^ 2) * riemannZeta (z + 1 / 2)) ∧
    probeLaplace (fun t : ℝ => (classicalCompletionKernel t : ℂ)) (1 / 2) = 1 ∧
    (comparisonU : ProbeL2) =ᵐ[volume] comparisonUPhysical ∧
    (comparisonH : ProbeL2) =ᵐ[volume] comparisonHPhysical ∧
    fixedFilterOperator probeTarget = causalInnerOperator (causalInnerOperator comparisonU) ∧
    fixedFilterOperator probeCompletedSource = causalInnerOperator (causalInnerOperator comparisonH) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0, fixedFilterOperator (probeColumn n) =
      causalInnerOperator (causalInnerOperator ((CCM.nativeIntegerCoefficient n : ℂ) •
        probeDelay (Real.log n) (probe_log_nonneg hn) comparisonH))) ∧
    (∀ N : ℕ, ∀ x : Fin N → ℂ, ‖fixedFilteredProbeResidual x‖ = ‖comparisonFiniteResidual x‖) := by
  exact ⟨fixedFilterKernel_integrable, fixedFilterKernel_integral_norm,
    fixedFilterKernel_laplace, causalInnerOperator_norm, causalInnerOperator_not_surjective,
    classicalProbeKernel_integrable, classicalProbeKernel_memLp,
    classicalCompletionKernel_integrable, classicalCompletionKernel_memLp,
    classicalCompletionKernel_laplace, classicalCompletionKernel_laplace_half,
    comparisonU_coeFn, comparisonH_coeFn, fixedFilter_target_factorization,
    fixedFilter_completed_factorization, fun _ hn => fixedFilter_column_factorization hn,
    fun _ x => fixedFilteredProbeResidual_norm_eq x⟩

end Zeta23.OPICARound2
