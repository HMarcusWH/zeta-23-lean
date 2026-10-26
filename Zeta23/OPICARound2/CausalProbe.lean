import Zeta23.CCM.NativeDampedCompletionPointwiseBridge
import Zeta23.CCM.NativeCausalRangeObstruction
import Zeta23.CCM.NativeFloorCompletionSource
import Zeta23.CCM.NativeCompletionIntegerKernel
import Zeta23.CCM.NativePositiveCompletionComplexLaplace
import Zeta23.CCM.OriginalSincWeightedPoleMoments
import Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt
import Zeta23.OPICAFollowup.MultiplicityTail
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The literal delayed original source and causal probe

The original source is unchanged. Translation makes a separate causal source.
The generic kernel operator below is the actual strong integral of translations,
with its own integrability and norm proof. It accepts no range, positivity or
zero-location conclusion as a construction premise.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ENNReal BigOperators ComplexConjugate

namespace Zeta23.OPICARound2

abbrev ProbeL2 := CCM.NativeCompletionL2
abbrev CausalProbeL2 := CCM.nativeCompletionCausalL2

def probeSigma : ℝ := CCM.UniversalSinc.fixedScale

theorem probeSigma_pos : 0 < probeSigma := CCM.UniversalSinc.fixedScale_pos

theorem probeSigma_eq : probeSigma = 1 / 4096 := rfl

/-- Literal translation of the one-copy source, rather than a new bump. -/
def jPlus (t : ℝ) : ℝ := CCM.nativeOriginalSource (t - probeSigma)

def JPlus (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)

theorem jPlus_zero_outside {t : ℝ} (ht : t ∉ Icc 0 (2 * probeSigma)) :
    jPlus t = 0 := by
  apply CCM.nativeOriginalSource_supported
  change t - probeSigma ∉ Icc (-probeSigma) probeSigma
  intro h
  apply ht
  constructor <;> linarith [h.1, h.2]

theorem jPlus_zero_of_neg {t : ℝ} (ht : t < 0) : jPlus t = 0 :=
  jPlus_zero_outside (fun h => (not_le_of_gt ht) h.1)

theorem jPlus_contDiff : ContDiff ℝ (⊤ : ℕ∞) jPlus :=
  CCM.nativeOriginalSource_contDiff.comp (contDiff_id.sub contDiff_const)

theorem jPlus_hasCompactSupport : HasCompactSupport jPlus := by
  apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
  exact fun _ hx => jPlus_zero_outside hx

theorem jPlus_integrable : Integrable jPlus :=
  jPlus_contDiff.continuous.integrable_of_hasCompactSupport jPlus_hasCompactSupport

theorem jPlus_integral : (∫ t : ℝ, jPlus t) = (1 / 16 : ℝ) := by
  change (∫ t : ℝ, CCM.nativeOriginalSource (t - probeSigma)) = _
  rw [integral_sub_right_eq_self]
  exact CCM.nativeOriginalSource_integral

theorem jPlus_complex_hasCompactSupport :
    HasCompactSupport (fun t : ℝ => (jPlus t : ℂ)) := by
  apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
  intro t ht
  rw [jPlus_zero_outside ht, Complex.ofReal_zero]

theorem jPlus_complex_integrable : Integrable (fun t : ℝ => (jPlus t : ℂ)) :=
  jPlus_integrable.ofReal

theorem jPlus_memLp : MemLp (fun t : ℝ => (jPlus t : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp jPlus_contDiff.continuous).memLp_of_hasCompactSupport
    jPlus_complex_hasCompactSupport

def probeSource : CausalProbeL2 :=
  ⟨jPlus_memLp.toLp (fun t : ℝ => (jPlus t : ℂ)), by
    change ∀ᵐ t : ℝ, t < 0 → _
    filter_upwards [jPlus_memLp.coeFn_toLp] with t ht
    intro hneg
    rw [ht, jPlus_zero_of_neg hneg, Complex.ofReal_zero]⟩

theorem probeSource_coeFn :
    (probeSource : ProbeL2) =ᵐ[volume] fun t : ℝ => (jPlus t : ℂ) :=
  jPlus_memLp.coeFn_toLp

theorem JPlus_eq_delay (z : ℂ) :
    JPlus z = Complex.exp (-z * (probeSigma : ℂ)) * CCM.nativeOriginalSourceLaplace z := by
  unfold JPlus jPlus CCM.nativeOriginalSourceLaplace
  have heq (t : ℝ) :
      Complex.exp (-z * (t : ℂ)) * (CCM.nativeOriginalSource (t - probeSigma) : ℂ) =
        Complex.exp (-z * (probeSigma : ℂ)) *
          (Complex.exp (-z * ((t - probeSigma : ℝ) : ℂ)) *
            (CCM.nativeOriginalSource (t - probeSigma) : ℂ)) := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self
    (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (CCM.nativeOriginalSource t : ℂ))
    probeSigma (μ := (volume : Measure ℝ))

theorem JPlus_one_copy_formula (z : ℂ) :
    JPlus z = Complex.exp (-z * (probeSigma : ℂ)) *
      (((Complex.I * z) ^ 2 + 1 / 4) ^ 2 *
        CCM.UniversalSinc.product probeSigma (Complex.I * z)) := by
  rw [JPlus_eq_delay, ExceptionalZero.nativeOriginalSourceLaplace_formula]
  rfl

theorem JPlus_ne_zero_at_off_line_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    JPlus ((rho : ℂ) - 1 / 2) ≠ 0 := by
  rw [JPlus_eq_delay]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (ExceptionalZero.nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho hoff)

theorem JPlus_half : JPlus (1 / 2 : ℂ) = 0 := by
  rw [JPlus_one_copy_formula]
  norm_num [mul_pow, Complex.I_sq]

theorem JPlus_neg_half : JPlus (-1 / 2 : ℂ) = 0 := by
  rw [JPlus_one_copy_formula]
  norm_num [mul_pow, Complex.I_sq]

private theorem original_weighted_integrable (r : ℝ) :
    Integrable (fun t : ℝ => Real.exp (r * t) * CCM.nativeOriginalSource t) ∧
    Integrable (fun t : ℝ => t * Real.exp (r * t) * CCM.nativeOriginalSource t) := by
  have h0 : HasCompactSupport
      (fun t : ℝ => Real.exp (r * t) * CCM.nativeOriginalSource t) := by
    apply HasCompactSupport.intro (K := Icc (-probeSigma) probeSigma) isCompact_Icc
    intro t ht
    rw [CCM.nativeOriginalSource_supported t ht, mul_zero]
  have h1 : HasCompactSupport
      (fun t : ℝ => t * Real.exp (r * t) * CCM.nativeOriginalSource t) := by
    apply HasCompactSupport.intro (K := Icc (-probeSigma) probeSigma) isCompact_Icc
    intro t ht
    rw [CCM.nativeOriginalSource_supported t ht, mul_zero]
  constructor
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      CCM.nativeOriginalSource_contDiff.continuous).integrable_of_hasCompactSupport h0
  · exact ((continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul
      CCM.nativeOriginalSource_contDiff.continuous).integrable_of_hasCompactSupport h1

private theorem jPlus_elementary_moment_shift (r : ℝ) :
    (∫ t : ℝ, Real.exp (r * t) * jPlus t) = Real.exp (r * probeSigma) *
      ∫ t : ℝ, Real.exp (r * t) * CCM.nativeOriginalSource t := by
  have heq (t : ℝ) : Real.exp (r * t) * jPlus t =
      Real.exp (r * probeSigma) *
        (Real.exp (r * (t - probeSigma)) * CCM.nativeOriginalSource (t - probeSigma)) := by
    unfold jPlus
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self
    (fun t : ℝ => Real.exp (r * t) * CCM.nativeOriginalSource t)
    probeSigma (μ := (volume : Measure ℝ))

private theorem jPlus_first_moment_shift (r : ℝ) :
    (∫ t : ℝ, t * Real.exp (r * t) * jPlus t) = Real.exp (r * probeSigma) *
      ((∫ t : ℝ, t * Real.exp (r * t) * CCM.nativeOriginalSource t) +
        probeSigma * (∫ t : ℝ, Real.exp (r * t) * CCM.nativeOriginalSource t)) := by
  have heq (t : ℝ) : t * Real.exp (r * t) * jPlus t =
      Real.exp (r * probeSigma) *
        ((t - probeSigma) * Real.exp (r * (t - probeSigma)) *
          CCM.nativeOriginalSource (t - probeSigma) +
        probeSigma * (Real.exp (r * (t - probeSigma)) *
          CCM.nativeOriginalSource (t - probeSigma))) := by
    have he : Real.exp (r * t) =
        Real.exp (r * probeSigma) * Real.exp (r * (t - probeSigma)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [jPlus, he]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul,
    integral_add ((original_weighted_integrable r).2.comp_sub_right probeSigma)
      (((original_weighted_integrable r).1.comp_sub_right probeSigma).const_mul probeSigma),
    integral_const_mul]
  have h0 := integral_sub_right_eq_self
    (fun t : ℝ => Real.exp (r * t) * CCM.nativeOriginalSource t)
    probeSigma (μ := (volume : Measure ℝ))
  have h1 := integral_sub_right_eq_self
    (fun t : ℝ => t * Real.exp (r * t) * CCM.nativeOriginalSource t)
    probeSigma (μ := (volume : Measure ℝ))
  rw [h0, h1]

theorem jPlus_double_killed_moments :
    (∫ t : ℝ, Real.exp (t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, Real.exp (-t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, t * Real.exp (t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, t * Real.exp (-t / 2) * jPlus t) = 0 := by
  rcases CCM.nativeOriginalSource_weighted_elementary_moments with ⟨hp, hm, hfp, hfm⟩
  have hp' : (∫ t : ℝ, Real.exp ((1 / 2) * t) * CCM.nativeOriginalSource t) = 0 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hp
  have hm' : (∫ t : ℝ, Real.exp ((-1 / 2) * t) * CCM.nativeOriginalSource t) = 0 := by
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, one_mul, mul_comm] using hm
  have hfp' : (∫ t : ℝ, t * Real.exp ((1 / 2) * t) * CCM.nativeOriginalSource t) = 0 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hfp
  have hfm' : (∫ t : ℝ, t * Real.exp ((-1 / 2) * t) * CCM.nativeOriginalSource t) = 0 := by
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, one_mul, mul_comm] using hfm
  have h0p := jPlus_elementary_moment_shift (1 / 2)
  have h0m := jPlus_elementary_moment_shift (-1 / 2)
  have h1p := jPlus_first_moment_shift (1 / 2)
  have h1m := jPlus_first_moment_shift (-1 / 2)
  rw [hp', mul_zero] at h0p
  rw [hm', mul_zero] at h0m
  rw [hfp', hp', mul_zero, add_zero, mul_zero] at h1p
  rw [hfm', hm', mul_zero, add_zero, mul_zero] at h1m
  simpa only [div_eq_mul_inv, neg_mul, mul_neg, one_mul, mul_comm] using
    And.intro h0p (And.intro h0m (And.intro h1p h1m))

theorem delayed_original_source :
    probeSigma = 1 / 4096 ∧ 0 < probeSigma ∧
    (∀ t : ℝ, jPlus t = CCM.nativeOriginalSource (t - probeSigma)) ∧
    (∀ t : ℝ, t ∉ Icc 0 (2 * probeSigma) → jPlus t = 0) ∧
    ContDiff ℝ (⊤ : ℕ∞) jPlus ∧ Integrable jPlus ∧
    MemLp (fun t : ℝ => (jPlus t : ℂ)) 2 volume ∧
    (∫ t : ℝ, jPlus t) = 1 / 16 ∧
    (∀ z : ℂ, JPlus z = Complex.exp (-z * (probeSigma : ℂ)) *
      CCM.nativeOriginalSourceLaplace z) ∧
    ((∫ t : ℝ, Real.exp (t / 2) * jPlus t) = 0 ∧
      (∫ t : ℝ, Real.exp (-t / 2) * jPlus t) = 0 ∧
      (∫ t : ℝ, t * Real.exp (t / 2) * jPlus t) = 0 ∧
      (∫ t : ℝ, t * Real.exp (-t / 2) * jPlus t) = 0) := by
  exact ⟨probeSigma_eq, probeSigma_pos, fun _ => rfl,
    fun _ ht => jPlus_zero_outside ht, jPlus_contDiff, jPlus_integrable, jPlus_memLp,
    jPlus_integral, JPlus_eq_delay, jPlus_double_killed_moments⟩

/-- The strong kernel integral uses the actual full-line translation x-t. -/
def kernelL2Integrand (k : ℝ → ℝ) (f : ProbeL2) (t : ℝ) : ProbeL2 :=
  OPICAFollowup.causalFilterL2Integrand k f t

theorem kernelL2Integrand_norm (k : ℝ → ℝ) (f : ProbeL2) (t : ℝ) :
    ‖kernelL2Integrand k f t‖ = ‖k t‖ * ‖f‖ := by
  exact OPICAFollowup.causalFilterL2Integrand_norm k f t

theorem kernelL2Integrand_integrable (k : ℝ → ℝ) (hk : Integrable k) (f : ProbeL2) :
    Integrable (kernelL2Integrand k f) := by
  have hm : AEStronglyMeasurable (kernelL2Integrand k f) :=
    hk.aestronglyMeasurable.smul (CCM.nativeCompletionL2Delay_continuous f).aestronglyMeasurable
  apply (hk.norm.mul_const ‖f‖).mono' hm
  exact Filter.Eventually.of_forall fun t => (kernelL2Integrand_norm k f t).le

def kernelL2Value (k : ℝ → ℝ) (f : ProbeL2) : ProbeL2 :=
  OPICAFollowup.causalFilterL2Value k f

theorem kernelL2Value_norm_le (k : ℝ → ℝ) (hk : Integrable k) (f : ProbeL2) :
    ‖kernelL2Value k f‖ ≤ (∫ t : ℝ, ‖k t‖) * ‖f‖ := by
  exact OPICAFollowup.causalFilterL2Value_norm_le k f

def kernelL2LinearMap (k : ℝ → ℝ) (hk : Integrable k) : ProbeL2 →ₗ[ℂ] ProbeL2 where
  toFun := kernelL2Value k
  map_add' f g := by
    change (∫ t : ℝ, kernelL2Integrand k (f + g) t) =
      (∫ t : ℝ, kernelL2Integrand k f t) + ∫ t : ℝ, kernelL2Integrand k g t
    have hp : kernelL2Integrand k (f + g) =
        fun t => kernelL2Integrand k f t + kernelL2Integrand k g t := by
      funext t
      simp only [kernelL2Integrand, OPICAFollowup.causalFilterL2Integrand, map_add, smul_add]
    rw [hp, integral_add (kernelL2Integrand_integrable k hk f)
      (kernelL2Integrand_integrable k hk g)]
  map_smul' c f := by
    change (∫ t : ℝ, kernelL2Integrand k (c • f) t) =
      c • ∫ t : ℝ, kernelL2Integrand k f t
    have hp : kernelL2Integrand k (c • f) = fun t => c • kernelL2Integrand k f t := by
      funext t
      simp only [kernelL2Integrand, OPICAFollowup.causalFilterL2Integrand, map_smul]
      exact smul_comm _ _ _
    rw [hp, integral_smul]

def kernelL2Operator (k : ℝ → ℝ) (hk : Integrable k) : ProbeL2 →L[ℂ] ProbeL2 :=
  (kernelL2LinearMap k hk).mkContinuous (∫ t : ℝ, ‖k t‖) (kernelL2Value_norm_le k hk)

theorem kernelL2Operator_apply (k : ℝ → ℝ) (hk : Integrable k) (f : ProbeL2) :
    kernelL2Operator k hk f = ∫ t : ℝ, k t • CCM.nativeCompletionL2Delay t f := rfl

theorem kernelL2Operator_norm_le (k : ℝ → ℝ) (hk : Integrable k) :
    ‖kernelL2Operator k hk‖ ≤ ∫ t : ℝ, ‖k t‖ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _)
    (kernelL2Value_norm_le k hk)

theorem kernelL2Integrand_causal (k : ℝ → ℝ)
    (hc : ∀ t, t < 0 → k t = 0) (f : CausalProbeL2) (t : ℝ) :
    kernelL2Integrand k (f : ProbeL2) t ∈ CCM.nativeCompletionCausalL2 := by
  exact OPICAFollowup.causalFilterL2Integrand_causal k hc f t

theorem kernelL2Operator_causal (k : ℝ → ℝ) (hk : Integrable k)
    (hc : ∀ t, t < 0 → k t = 0) (f : CausalProbeL2) :
    kernelL2Operator k hk (f : ProbeL2) ∈ CCM.nativeCompletionCausalL2 := by
  exact OPICAFollowup.causalFilterL2Value_causal k hc f

def causalKernelOperator (k : ℝ → ℝ) (hk : Integrable k)
    (hc : ∀ t, t < 0 → k t = 0) : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  ContinuousLinearMap.codRestrict
    ((kernelL2Operator k hk).domRestrict CCM.nativeCompletionCausalL2)
    CCM.nativeCompletionCausalL2 (fun f => kernelL2Operator_causal k hk hc f)

theorem causalKernelOperator_coe_apply (k : ℝ → ℝ) (hk : Integrable k)
    (hc : ∀ t, t < 0 → k t = 0) (f : CausalProbeL2) :
    (causalKernelOperator k hk hc f : ProbeL2) = kernelL2Operator k hk (f : ProbeL2) := rfl

theorem causalKernelOperator_norm_le (k : ℝ → ℝ) (hk : Integrable k)
    (hc : ∀ t, t < 0 → k t = 0) :
    ‖causalKernelOperator k hk hc‖ ≤ ∫ t : ℝ, ‖k t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
  intro f
  exact kernelL2Value_norm_le k hk (f : ProbeL2)

theorem kernelL2Operator_coeFn_pointwise (k : ℝ → ℝ) (hk : Integrable k)
    (hm : Measurable k) (hk2 : MemLp (fun t : ℝ => (k t : ℂ)) 2 volume)
    (f : ProbeL2) :
    kernelL2Operator k hk f =ᵐ[volume] fun x => ∫ t : ℝ, (k t : ℂ) * f (x - t) :=
  OPICAFollowup.causalFilterL2Value_coe_pointwise k hm hk hk2 f

def probeC : ℝ → ℝ := CCM.nativeCompletionCorrection

theorem probeC_eq_nativeRationalKernel : probeC = CCM.nativeRationalCausalKernel :=
  CCM.nativeCompletionCorrection_eq_rationalKernel

theorem probeC_integrable : Integrable probeC := CCM.nativeCompletionCorrection_integrable

theorem probeC_measurable : Measurable probeC := CCM.nativeCompletionCorrection_measurable

theorem probeC_zero_of_neg (t : ℝ) (ht : t < 0) : probeC t = 0 :=
  CCM.nativeCompletionCorrection_zero_of_neg ht

theorem probeC_memLp : MemLp (fun t : ℝ => (probeC t : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (probeC t : ℂ)) volume :=
    probeC_measurable.complex_ofReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (probeC_integrable.norm.const_mul 3).mono' (hm.norm.pow 2)
  filter_upwards with t
  change ‖‖(probeC t : ℂ)‖ ^ 2‖ ≤ 3 * ‖probeC t‖
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs]
  have hb := CCM.nativeCompletionCorrection_abs_le_three t
  change |probeC t| ≤ 3 at hb
  nlinarith [abs_nonneg (probeC t)]

def probeOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)

/-- The target is the actual signed-kernel convolution of the delayed source. -/
def probeTarget : CausalProbeL2 :=
  causalKernelOperator probeC probeC_integrable probeC_zero_of_neg probeSource

/-- The completed source is an actual output of the unchanged floor operator. -/
def probeCompletedSource : CausalProbeL2 := probeOperator probeSource

def probeV (t : ℝ) : ℂ :=
  ∫ s : ℝ, (probeC s : ℂ) * (jPlus (t - s) : ℂ)

def probeW (t : ℝ) : ℂ :=
  ∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) * (jPlus (t - s) : ℂ)

theorem probeTarget_coeFn : (probeTarget : ProbeL2) =ᵐ[volume] probeV := by
  have hg := kernelL2Operator_coeFn_pointwise probeC probeC_integrable
    probeC_measurable probeC_memLp (probeSource : ProbeL2)
  apply hg.trans
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  have hd := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq probeSource_coeFn
  filter_upwards [hd] with s hs
  exact congrArg (fun x : ℂ => (probeC s : ℂ) * x) hs

theorem probeCompletedSource_coeFn :
    (probeCompletedSource : ProbeL2) =ᵐ[volume] probeW := by
  have hg := CCM.nativeDampedCompletionL2Operator_coeFn_pointwise 0 (le_rfl)
    (probeSource : ProbeL2)
  apply hg.trans
  apply Filter.Eventually.of_forall
  intro t
  unfold CCM.nativeDampedCompletionPointwise probeW
  apply integral_congr_ae
  have hd := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq probeSource_coeFn
  filter_upwards [hd] with s hs
  dsimp only [Function.comp_def] at hs
  rw [hs]
  simp [CCM.nativeDampedCompletionKernel]

theorem probeV_memLp : MemLp probeV 2 volume :=
  MemLp.ae_eq probeTarget_coeFn (Lp.memLp (probeTarget : ProbeL2))

theorem probeW_memLp : MemLp probeW 2 volume :=
  MemLp.ae_eq probeCompletedSource_coeFn (Lp.memLp (probeCompletedSource : ProbeL2))

theorem probeV_integrable : Integrable probeV := by
  exact probeC_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) jPlus_complex_integrable

theorem probeW_integrable : Integrable probeW := by
  exact CCM.nativePositiveCompletion_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) jPlus_complex_integrable

private theorem probe_causal_product_integrable {g f : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ s : ℝ, s < 0 → g s = 0)
    (hf : Continuous f) (hf0 : ∀ s : ℝ, s < 0 → f s = 0) (t : ℝ) :
    Integrable (fun s : ℝ => g s * f (t - s)) := by
  have hc : Continuous (fun s : ℝ => f (t - s)) :=
    hf.comp (continuous_const.sub continuous_id)
  have hi : IntegrableOn (fun s : ℝ => g s * f (t - s)) (Icc 0 t) :=
    hg.integrableOn.mul_continuousOn hc.continuousOn isCompact_Icc
  apply (hi.integrable_indicator measurableSet_Icc).congr
  filter_upwards with s
  by_cases hs : s ∈ Icc 0 t
  · simp only [indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hcases : s < 0 ∨ t < s := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hs
    rcases hcases with hneg | hafter
    · rw [hg0 s hneg, zero_mul]
    · rw [hf0 _ (by linarith), mul_zero]

theorem probeV_eq_real_integral (t : ℝ) :
    probeV t = ((∫ s : ℝ, probeC s * jPlus (t - s) : ℝ) : ℂ) := by
  calc
    probeV t = ∫ s : ℝ, ((probeC s * jPlus (t - s) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with s
      exact (Complex.ofReal_mul _ _).symm
    _ = _ := _root_.integral_complex_ofReal

theorem probeW_eq_real_integral (t : ℝ) :
    probeW t = ((∫ s : ℝ, CCM.nativePositiveCompletion s * jPlus (t - s) : ℝ) : ℂ) := by
  calc
    probeW t = ∫ s : ℝ, ((CCM.nativePositiveCompletion s * jPlus (t - s) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with s
      exact (Complex.ofReal_mul _ _).symm
    _ = _ := _root_.integral_complex_ofReal

/-- Every time has its own finite inclusive integer history. No L2 limit of the
integer partial sums is asserted. -/
theorem native_probe_integer_action (t : ℝ) :
    probeW t = ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1),
      (CCM.nativeIntegerCoefficient n : ℂ) * probeV (t - Real.log n) := by
  let history := Finset.range (⌊Real.exp t⌋₊ + 1)
  have hpoint : (fun s : ℝ => CCM.nativePositiveCompletion s * jPlus (t - s)) =
      fun s => ∑ n ∈ history,
        CCM.nativeIntegerCoefficient n * probeC (s - Real.log n) * jPlus (t - s) := by
    funext s
    by_cases hs : s ≤ t
    · rw [CCM.nativePositiveCompletion_eq_integerTranslateCorrection,
        CCM.nativeIntegerTranslateAction_eq_causal_history_at_horizon
          (fun _ ht => CCM.nativeCompletionCorrection_zero_of_neg ht) hs,
        Finset.sum_mul]
      rfl
    · rw [jPlus_zero_of_neg (by linarith), mul_zero]
      simp only [mul_zero, Finset.sum_const_zero]
  have hint (n : ℕ) : Integrable (fun s : ℝ =>
      CCM.nativeIntegerCoefficient n * probeC (s - Real.log n) * jPlus (t - s)) := by
    by_cases hn : n = 0
    · simp [hn, CCM.nativeIntegerCoefficient]
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hgc : ∀ s : ℝ, s < 0 → probeC (s - Real.log n) = 0 := by
      intro s hs
      exact probeC_zero_of_neg _ (by linarith)
    simpa only [mul_assoc] using
      (probe_causal_product_integrable (probeC_integrable.comp_sub_right (Real.log n))
        hgc jPlus_contDiff.continuous (fun _ ht => jPlus_zero_of_neg ht) t).const_mul
          (CCM.nativeIntegerCoefficient n)
  have hreal : (∫ s : ℝ, CCM.nativePositiveCompletion s * jPlus (t - s)) =
      ∑ n ∈ history, CCM.nativeIntegerCoefficient n *
        ∫ s : ℝ, probeC s * jPlus ((t - Real.log n) - s) := by
    rw [hpoint, integral_finsetSum _ (fun n _ => hint n)]
    apply Finset.sum_congr rfl
    intro n _
    have hf : (fun s : ℝ => CCM.nativeIntegerCoefficient n *
        probeC (s - Real.log n) * jPlus (t - s)) =
        fun s => CCM.nativeIntegerCoefficient n *
          (probeC (s - Real.log n) * jPlus (t - s)) := by funext s; ring
    rw [hf, integral_const_mul]
    congr 1
    have hshift : (fun s : ℝ => probeC (s - Real.log n) * jPlus (t - s)) =
        fun s => (fun u : ℝ => probeC u * jPlus ((t - Real.log n) - u))
          (s - Real.log n) := by
      funext s
      congr 2
      ring
    rw [hshift]
    exact integral_sub_right_eq_self
      (fun u : ℝ => probeC u * jPlus ((t - Real.log n) - u))
      (Real.log n) (μ := (volume : Measure ℝ))
  rw [probeW_eq_real_integral, hreal]
  simp_rw [probeV_eq_real_integral, Complex.ofReal_sum, Complex.ofReal_mul]
  rfl

theorem probeV_zero_of_neg {t : ℝ} (ht : t < 0) : probeV t = 0 := by
  unfold probeV
  apply integral_eq_zero_of_ae
  filter_upwards with s
  change (probeC s : ℂ) * (jPlus (t - s) : ℂ) = 0
  by_cases hs : s < 0
  · rw [probeC_zero_of_neg s hs, Complex.ofReal_zero, zero_mul]
  · rw [jPlus_zero_of_neg (by linarith [le_of_not_gt hs]), Complex.ofReal_zero, mul_zero]

theorem probeW_zero_of_neg {t : ℝ} (ht : t < 0) : probeW t = 0 := by
  unfold probeW
  apply integral_eq_zero_of_ae
  filter_upwards with s
  change (CCM.nativePositiveCompletion s : ℂ) * (jPlus (t - s) : ℂ) = 0
  by_cases hs : s < 0
  · rw [CCM.nativePositiveCompletion_eq_zero_of_neg hs, Complex.ofReal_zero, zero_mul]
  · rw [jPlus_zero_of_neg (by linarith [le_of_not_gt hs]), Complex.ofReal_zero, mul_zero]

def probeLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * f t

/-- The literal causal kernel operator transports bounded Laplace evaluation;
its proof uses the strong integral, rather than a multiplier realization. -/
theorem causalKernelOperator_laplace (k : ℝ → ℝ) (hk : Integrable k)
    (hc : ∀ t, t < 0 → k t = 0) (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (causalKernelOperator k hk hc f : ProbeL2) =
      probeLaplace (fun t => (k t : ℂ)) z *
        CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  have hi : CCM.nativeCausalLaplaceMoment z 0
      (causalKernelOperator k hk hc f : ProbeL2) =
      ∫ s : ℝ, inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0)
        (kernelL2Integrand k (f : ProbeL2) s) := by
    rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0]
    change inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0)
      (kernelL2Operator k hk (f : ProbeL2)) = _
    rw [kernelL2Operator_apply]
    exact (integral_inner (𝕜 := ℂ) (kernelL2Integrand_integrable k hk (f : ProbeL2))
      (CCM.nativeCausalExponentialPolynomialL2 z hz 0)).symm
  have hpoint (s : ℝ) :
      inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0)
        (kernelL2Integrand k (f : ProbeL2) s) =
      (Complex.exp (-z * (s : ℂ)) * (k s : ℂ)) *
        CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
    by_cases hs : 0 ≤ s
    · let delayed : CausalProbeL2 :=
        ⟨CCM.nativeCompletionL2Delay s (f : ProbeL2),
          CCM.nativeCompletionL2Delay_causal hs (f : ProbeL2) f.property⟩
      have hd := CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0 delayed
      change inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0)
        (CCM.nativeCompletionL2Delay s (f : ProbeL2)) =
        CCM.nativeCausalLaplaceMoment z 0
          (CCM.nativeCompletionL2Delay s (f : ProbeL2)) at hd
      rw [kernelL2Integrand, OPICAFollowup.causalFilterL2Integrand,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, hd,
        CCM.nativeCausalLaplaceMoment_delay z hz 0 f s]
      simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
        Nat.sub_self, pow_zero, Nat.cast_one, one_mul, mul_one,
        RCLike.ofReal_eq_complex_ofReal]
      ring
    · rw [kernelL2Integrand, OPICAFollowup.causalFilterL2Integrand,
        hc s (lt_of_not_ge hs), zero_smul, inner_zero_right, Complex.ofReal_zero,
        mul_zero, zero_mul]
  rw [hi, integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_mul_const]
  rfl

theorem probeTarget_laplace_eq_physical (z : ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (probeTarget : ProbeL2) = probeLaplace probeV z := by
  apply integral_congr_ae
  filter_upwards [probeTarget_coeFn] with t ht
  simp only [pow_zero, one_mul, ht]

theorem probeCompletedSource_laplace_eq_physical (z : ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (probeCompletedSource : ProbeL2) =
      probeLaplace probeW z := by
  apply integral_congr_ae
  filter_upwards [probeCompletedSource_coeFn] with t ht
  simp only [pow_zero, one_mul, ht]

theorem probeV_laplace {z : ℂ} (hz : 0 ≤ z.re) :
    probeLaplace probeV z = CCM.nativeCompletionRationalMultiplier z * JPlus z := by
  have hc := CCM.nativeCausalComplexDamping_integrable hz probeC_integrable probeC_zero_of_neg
  have hj := CCM.nativeCausalComplexDamping_integrable hz jPlus_integrable
    (fun _ ht => jPlus_zero_of_neg ht)
  have hp := OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t => (probeC t : ℂ)) (fun t => (jPlus t : ℂ)) z hc hj
  change (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
    (∫ s : ℝ, (probeC s : ℂ) * (jPlus (t - s) : ℂ))) = _
  rw [hp.2]
  change (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (CCM.nativeCompletionCorrection t : ℂ)) *
    JPlus z = _
  rw [CCM.nativeCompletionCorrection_complexLaplace (by linarith)]

theorem probeW_laplace_actual {z : ℂ} (hz : 0 ≤ z.re) :
    probeLaplace probeW z = CCM.nativePositiveCompletionLaplace z * JPlus z := by
  have hc := CCM.nativeCausalComplexDamping_integrable hz
    CCM.nativePositiveCompletion_integrable (fun _ ht => CCM.nativePositiveCompletion_eq_zero_of_neg ht)
  have hj := CCM.nativeCausalComplexDamping_integrable hz jPlus_integrable
    (fun _ ht => jPlus_zero_of_neg ht)
  exact (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t => (CCM.nativePositiveCompletion t : ℂ)) (fun t => (jPlus t : ℂ)) z hc hj).2

theorem probeW_laplace {z : ℂ} (hz : 0 < z.re) (hne : z ≠ 1 / 2) :
    probeLaplace probeW z =
      CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2) * JPlus z := by
  have hc := CCM.nativeCausalComplexDamping_integrable hz.le
    CCM.nativePositiveCompletion_integrable (fun _ ht => CCM.nativePositiveCompletion_eq_zero_of_neg ht)
  have hj := CCM.nativeCausalComplexDamping_integrable hz.le jPlus_integrable
    (fun _ ht => jPlus_zero_of_neg ht)
  have hp := OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t => (CCM.nativePositiveCompletion t : ℂ)) (fun t => (jPlus t : ℂ)) z hc hj
  change (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
    (∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) * (jPlus (t - s) : ℂ))) = _
  rw [hp.2, CCM.nativePositiveCompletion_complexLaplace hz hne]
  rfl

theorem probeW_laplace_half : probeLaplace probeW (1 / 2 : ℂ) = 0 := by
  have hc := CCM.nativeCausalComplexDamping_integrable (w := (1 / 2 : ℂ)) (by norm_num)
    CCM.nativePositiveCompletion_integrable (fun _ ht => CCM.nativePositiveCompletion_eq_zero_of_neg ht)
  have hj := CCM.nativeCausalComplexDamping_integrable (w := (1 / 2 : ℂ)) (by norm_num)
    jPlus_integrable (fun _ ht => jPlus_zero_of_neg ht)
  have hp := OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t => (CCM.nativePositiveCompletion t : ℂ)) (fun t => (jPlus t : ℂ)) (1 / 2 : ℂ) hc hj
  change (∫ t : ℝ, Complex.exp (-(1 / 2 : ℂ) * (t : ℂ)) *
    (∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) * (jPlus (t - s) : ℂ))) = _
  rw [hp.2]
  change CCM.nativePositiveCompletionLaplace (1 / 2 : ℂ) * JPlus (1 / 2 : ℂ) = _
  rw [CCM.nativePositiveCompletion_complexLaplace_half, JPlus_half, mul_zero]

theorem JPlus_zero : JPlus 0 = (1 / 16 : ℂ) := by
  simp only [JPlus, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [_root_.integral_complex_ofReal, jPlus_integral]
  norm_num

theorem probeV_integral : (∫ t : ℝ, probeV t) = (-1 / 24 : ℂ) := by
  have h := probeV_laplace (z := 0) (by norm_num)
  norm_num [probeLaplace, CCM.nativeCompletionRationalMultiplier, JPlus_zero] at h ⊢
  exact h

theorem probeTarget_ne_zero : probeTarget ≠ 0 := by
  intro hz
  have hrep : probeV =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) := by
    have h := probeTarget_coeFn
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ))
  have hzero : (∫ t : ℝ, probeV t) = 0 := by
    rw [integral_congr_ae hrep, integral_zero]
  rw [probeV_integral] at hzero
  norm_num at hzero

theorem native_probe_transforms :
    probeC = CCM.nativeRationalCausalKernel ∧
    probeOperator = CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) ∧
    (probeTarget : ProbeL2) =ᵐ[volume] probeV ∧
    (probeCompletedSource : ProbeL2) =ᵐ[volume] probeW ∧
    Integrable probeV ∧ Integrable probeW ∧
    MemLp probeV 2 volume ∧ MemLp probeW 2 volume ∧
    (∀ t : ℝ, t < 0 → probeV t = 0) ∧
    (∀ t : ℝ, t < 0 → probeW t = 0) ∧
    (∀ z : ℂ, 0 ≤ z.re → probeLaplace probeV z =
      CCM.nativeCompletionRationalMultiplier z * JPlus z) ∧
    (∀ z : ℂ, 0 ≤ z.re → probeLaplace probeW z =
      CCM.nativePositiveCompletionLaplace z * JPlus z) ∧
    (∀ z : ℂ, 0 < z.re → z ≠ 1 / 2 → probeLaplace probeW z =
      CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2) * JPlus z) ∧
    probeLaplace probeW (1 / 2 : ℂ) = 0 ∧
    (∫ t : ℝ, probeV t) = (-1 / 24 : ℂ) ∧ probeTarget ≠ 0 := by
  exact ⟨probeC_eq_nativeRationalKernel, rfl, probeTarget_coeFn, probeCompletedSource_coeFn,
    probeV_integrable, probeW_integrable, probeV_memLp, probeW_memLp,
    fun _ ht => probeV_zero_of_neg ht, fun _ ht => probeW_zero_of_neg ht,
    fun _ hz => probeV_laplace hz, fun _ hz => probeW_laplace_actual hz,
    fun _ hz hne => probeW_laplace hz hne, probeW_laplace_half,
    probeV_integral, probeTarget_ne_zero⟩

/-- Nonnegative causal delays, still using the full-line isometric translation. -/
def probeDelay (t : ℝ) (ht : 0 ≤ t) : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  ContinuousLinearMap.codRestrict
    ((CCM.nativeCompletionL2Delay t).toContinuousLinearMap.domRestrict
      CCM.nativeCompletionCausalL2) CCM.nativeCompletionCausalL2
    (fun f => CCM.nativeCompletionL2Delay_causal ht (f : ProbeL2) f.property)

theorem probeDelay_coe_apply (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    (probeDelay t ht f : ProbeL2) = CCM.nativeCompletionL2Delay t (f : ProbeL2) := rfl

theorem probeDelay_norm (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    ‖probeDelay t ht f‖ = ‖f‖ := CCM.nativeCompletionL2Delay_norm t (f : ProbeL2)

theorem probeL2Delay_comm (s t : ℝ) (f : ProbeL2) :
    CCM.nativeCompletionL2Delay s (CCM.nativeCompletionL2Delay t f) =
      CCM.nativeCompletionL2Delay t (CCM.nativeCompletionL2Delay s f) := by
  apply Lp.ext
  have hst := (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq
    (CCM.nativeCompletionL2Delay_coeFn t f)
  have hts := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae_eq
    (CCM.nativeCompletionL2Delay_coeFn s f)
  filter_upwards [CCM.nativeCompletionL2Delay_coeFn s (CCM.nativeCompletionL2Delay t f),
    CCM.nativeCompletionL2Delay_coeFn t (CCM.nativeCompletionL2Delay s f), hst, hts]
    with x hx hy hxy hyx
  dsimp only [Function.comp_def] at hxy hyx
  rw [hx, hy, hxy, hyx]
  congr 1
  ring

theorem probeOperator_delay (t : ℝ) (ht : 0 ≤ t) (f : CausalProbeL2) :
    probeOperator (probeDelay t ht f) = probeDelay t ht (probeOperator f) := by
  apply Subtype.ext
  change CCM.nativeDampedCompletionL2Operator 0 (le_rfl)
      (CCM.nativeCompletionL2Delay t (f : ProbeL2)) =
    CCM.nativeCompletionL2Delay t
      (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) (f : ProbeL2))
  rw [CCM.nativeDampedCompletionL2Operator_apply,
    CCM.nativeDampedCompletionL2Operator_apply,
    ← (CCM.nativeCompletionL2Delay t).integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with s
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  rw [probeL2Delay_comm]

theorem probe_log_nonneg {n : ℕ} (hn : n ≠ 0) : 0 ≤ Real.log (n : ℝ) :=
  Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- The index zero convention is explicit and is never a dictionary column. -/
def probeInput (n : ℕ) : CausalProbeL2 :=
  if hn : n = 0 then 0 else
    (CCM.nativeIntegerCoefficient n : ℂ) •
      probeDelay (Real.log n) (probe_log_nonneg hn) probeSource

def probeColumn (n : ℕ) : CausalProbeL2 := probeOperator (probeInput n)

theorem probeColumn_eq_delay {n : ℕ} (hn : n ≠ 0) :
    probeColumn n = (CCM.nativeIntegerCoefficient n : ℂ) •
      probeDelay (Real.log n) (probe_log_nonneg hn) probeCompletedSource := by
  simp only [probeColumn, probeInput, dif_neg hn, map_smul]
  rw [probeOperator_delay]
  rfl

theorem probeInput_coeFn {n : ℕ} (hn : n ≠ 0) :
    (probeInput n : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      (CCM.nativeIntegerCoefficient n : ℂ) * (jPlus (t - Real.log n) : ℂ) := by
  simp only [probeInput, dif_neg hn]
  change ((CCM.nativeIntegerCoefficient n : ℂ) •
    CCM.nativeCompletionL2Delay (Real.log n) (probeSource : ProbeL2)) =ᵐ[volume] _
  have hshift := (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae_eq
    probeSource_coeFn
  filter_upwards [Lp.coeFn_smul (CCM.nativeIntegerCoefficient n : ℂ)
      (CCM.nativeCompletionL2Delay (Real.log n) (probeSource : ProbeL2)),
    CCM.nativeCompletionL2Delay_coeFn (Real.log n) (probeSource : ProbeL2), hshift]
    with t hsmul hdelay hsource
  dsimp only [Function.comp_def] at hsource
  rw [hsmul, Pi.smul_apply, hdelay, hsource]
  rfl

theorem probeColumn_coeFn {n : ℕ} (hn : n ≠ 0) :
    (probeColumn n : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n) := by
  rw [probeColumn_eq_delay hn]
  change ((CCM.nativeIntegerCoefficient n : ℂ) •
    CCM.nativeCompletionL2Delay (Real.log n) (probeCompletedSource : ProbeL2)) =ᵐ[volume] _
  have hshift := (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae_eq
    probeCompletedSource_coeFn
  filter_upwards [Lp.coeFn_smul (CCM.nativeIntegerCoefficient n : ℂ)
      (CCM.nativeCompletionL2Delay (Real.log n) (probeCompletedSource : ProbeL2)),
    CCM.nativeCompletionL2Delay_coeFn (Real.log n) (probeCompletedSource : ProbeL2), hshift]
    with t hsmul hdelay hsource
  dsimp only [Function.comp_def] at hsource
  rw [hsmul, Pi.smul_apply, hdelay, hsource]
  rfl

theorem probeInput_zero : probeInput 0 = 0 := by simp [probeInput]

theorem probeColumn_zero : probeColumn 0 = 0 := by
  simp [probeColumn, probeInput_zero]

theorem probeColumn_laplace (z : ℂ) (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    CCM.nativeCausalLaplaceMoment z 0 (probeColumn n : ProbeL2) =
      (CCM.nativeIntegerCoefficient n : ℂ) * Complex.exp (-z * (Real.log n : ℂ)) *
        probeLaplace probeW z := by
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0,
    probeColumn_eq_delay hn]
  have hsmul : inner ℂ (CCM.nativeCausalExponentialWitness z hz 0)
      ((CCM.nativeIntegerCoefficient n : ℂ) •
        probeDelay (Real.log n) (probe_log_nonneg hn) probeCompletedSource) =
      (CCM.nativeIntegerCoefficient n : ℂ) *
        inner ℂ (CCM.nativeCausalExponentialWitness z hz 0)
          (probeDelay (Real.log n) (probe_log_nonneg hn) probeCompletedSource) :=
    inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2) _ _ _
  rw [hsmul,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment]
  change _ * CCM.nativeCausalLaplaceMoment z 0
    (CCM.nativeCompletionL2Delay (Real.log n) (probeCompletedSource : ProbeL2)) = _
  rw [CCM.nativeCausalLaplaceMoment_delay z hz 0 probeCompletedSource (Real.log n)]
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.sub_self,
    pow_zero, Nat.cast_one, one_mul, mul_one]
  rw [probeCompletedSource_laplace_eq_physical]
  ring

def probeFiniteInput {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  ∑ i : Fin N, x i • probeInput (i.val + 1)

def probeFiniteOutput {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  ∑ i : Fin N, x i • probeColumn (i.val + 1)

def probeResidual {N : ℕ} (x : Fin N → ℂ) : CausalProbeL2 :=
  probeTarget - probeFiniteOutput x

theorem probeFiniteOutput_eq_operator {N : ℕ} (x : Fin N → ℂ) :
    probeFiniteOutput x = probeOperator (probeFiniteInput x) := by
  simp [probeFiniteOutput, probeFiniteInput, probeColumn]

theorem probeFiniteOutput_mem_range {N : ℕ} (x : Fin N → ℂ) :
    probeFiniteOutput x ∈ Set.range probeOperator :=
  ⟨probeFiniteInput x, (probeFiniteOutput_eq_operator x).symm⟩

theorem probe_rational_multiplier_ne_zero (rho : zetaZeroConfig.carrier) :
    CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) ≠ 0 := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hnum : (rho : ℂ) - 1 / 2 - 1 / 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.2]
  have hd1 : (rho : ℂ) - 1 / 2 + 1 / 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.1]
  have hd2 : (rho : ℂ) - 1 / 2 + 3 / 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.1]
  exact div_ne_zero hnum (mul_ne_zero hd1 hd2)

theorem probe_kernel_moment_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    CCM.nativeCompletionKernelLaplaceMoment 0 ((rho : ℂ) - 1 / 2) 0 = 0 := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  have hne : (rho : ℂ) - 1 / 2 ≠ (1 / 2 : ℂ) := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.2]
  have heq : CCM.nativeCompletionKernelLaplaceMoment 0 ((rho : ℂ) - 1 / 2) 0 =
      CCM.nativePositiveCompletionLaplace ((rho : ℂ) - 1 / 2) := by
    unfold CCM.nativeCompletionKernelLaplaceMoment CCM.nativePositiveCompletionLaplace
    apply integral_congr_ae
    filter_upwards with t
    simp [CCM.nativeDampedCompletionKernel, mul_comm]
  rw [heq]
  change (∫ t : ℝ, Complex.exp (-((rho : ℂ) - 1 / 2) * (t : ℂ)) *
    (CCM.nativePositiveCompletion t : ℂ)) = 0
  rw [CCM.nativePositiveCompletion_complexLaplace hp hne]
  simpa only [sub_add_cancel, hrho.1, mul_zero]

theorem probe_laplace_annihilates_range (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0
      (probeOperator f : ProbeL2) = 0 := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0]
  apply CCM.nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  exact probe_kernel_moment_zero rho hright

theorem probe_laplace_annihilates_rangeClosure (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {f : CausalProbeL2}
    (hf : f ∈ closure (Set.range probeOperator)) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0 (f : ProbeL2) = 0 := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0]
  apply CCM.nativeCausalExponentialWitness_annihilates_rangeClosure_of_kernel_moments
    0 (le_rfl) _ hp 0 _ hf
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  exact probe_kernel_moment_zero rho hright

theorem probeTarget_laplace_ne_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0 (probeTarget : ProbeL2) ≠ 0 := by
  rw [probeTarget_laplace_eq_physical,
    probeV_laplace (by simp only [Complex.sub_re]; norm_num; linarith)]
  exact mul_ne_zero (probe_rational_multiplier_ne_zero rho)
    (JPlus_ne_zero_at_off_line_zero rho (ne_of_gt hright))

theorem probeTarget_not_mem_rangeClosure (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    probeTarget ∉ closure (Set.range probeOperator) := by
  intro hf
  exact probeTarget_laplace_ne_zero rho hright
    (probe_laplace_annihilates_rangeClosure rho hright hf)

theorem probeLaplaceWitness_norm_sq (z : ℂ) (hz : 0 < z.re) :
    ‖CCM.nativeCausalExponentialWitness z hz 0‖ ^ 2 = 1 / (2 * z.re) := by
  have heq : (CCM.nativeCausalExponentialWitness z hz 0 : ProbeL2) =
      OPICAFollowup.monicLaguerreTailL2 0 z 0 hz := by
    apply Lp.ext
    filter_upwards [CCM.nativeCausalExponentialPolynomialL2_coeFn z hz 0,
      (OPICAFollowup.monicLaguerreTail_memLp 0 z 0 hz).coeFn_toLp] with t ht hs
    change CCM.nativeCausalExponentialPolynomialL2 z hz 0 t = _
    change CCM.nativeCausalExponentialPolynomialL2 z hz 0 t =
      OPICAFollowup.monicLaguerreTailL2 0 z 0 hz t
    rw [ht]
    change CCM.nativeCausalExponentialPolynomial z 0 t =
      (OPICAFollowup.monicLaguerreTail_memLp 0 z 0 hz).toLp
        (OPICAFollowup.monicLaguerreTail 0 z 0) t
    rw [hs]
    by_cases hnonneg : 0 ≤ t
    · simp [CCM.nativeCausalExponentialPolynomial, CCM.nativeExponentialPolynomialProfile,
        OPICAFollowup.monicLaguerreTail, OPICAFollowup.monicLaguerre, hnonneg]
    · simp [CCM.nativeCausalExponentialPolynomial,
        OPICAFollowup.monicLaguerreTail, hnonneg]
  have hnorm := (OPICAFollowup.laguerre_tail_norm 1 (by omega) z hz 0).2.2.2.2.1
  change ‖(CCM.nativeCausalExponentialWitness z hz 0 : ProbeL2)‖ ^ 2 = _
  rw [heq]
  simpa using hnorm

theorem probeLaplaceWitness_normalization (z : ℂ) (hz : 0 < z.re) :
    Real.sqrt (2 * z.re) * ‖CCM.nativeCausalExponentialWitness z hz 0‖ = 1 := by
  have hp : 0 < 2 * z.re := by positivity
  have hnorm := probeLaplaceWitness_norm_sq z hz
  have hs := Real.sq_sqrt hp.le
  have heq : (Real.sqrt (2 * z.re) *
      ‖CCM.nativeCausalExponentialWitness z hz 0‖) ^ 2 = 1 := by
    rw [mul_pow, hs, hnorm]
    field_simp
  have hnonneg : 0 ≤ Real.sqrt (2 * z.re) *
      ‖CCM.nativeCausalExponentialWitness z hz 0‖ := by positivity
  nlinarith

/-- The exact bounded evaluation functional on every actual causal L2 input. -/
theorem probe_laplace_evaluation_bound (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    Real.sqrt (2 * z.re) * ‖CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2)‖ ≤ ‖f‖ := by
  have hi := norm_inner_le_norm (𝕜 := ℂ) (CCM.nativeCausalExponentialWitness z hz 0) f
  rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment] at hi
  have h := mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg (2 * z.re))
  simpa only [← mul_assoc, probeLaplaceWitness_normalization z hz, one_mul] using h

theorem probe_zero_separation_rangeClosure (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {g : CausalProbeL2}
    (hg : g ∈ closure (Set.range probeOperator)) :
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖probeTarget - g‖ := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  have hm : CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0
      ((probeTarget - g : CausalProbeL2) : ProbeL2) =
      CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2) := by
    rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0,
      inner_sub_right, CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      probe_laplace_annihilates_rangeClosure rho hright hg, sub_zero,
      probeTarget_laplace_eq_physical, probeV_laplace hp.le]
  have hb := probe_laplace_evaluation_bound _ hp (probeTarget - g)
  rwa [hm] at hb

/-- Zeroth order separates the target at every right zero, whatever its multiplicity. -/
theorem native_probe_zero_separation (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    (0 < Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖) ∧
    (∀ f : CausalProbeL2,
      Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
        ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
          JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖probeTarget - probeOperator f‖) ∧
    (∀ g : CausalProbeL2, g ∈ closure (Set.range probeOperator) →
      Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
        ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
          JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖probeTarget - g‖) := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  have hv : CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
      JPlus ((rho : ℂ) - 1 / 2) ≠ 0 :=
    mul_ne_zero (probe_rational_multiplier_ne_zero rho)
      (JPlus_ne_zero_at_off_line_zero rho (ne_of_gt hright))
  refine ⟨mul_pos (Real.sqrt_pos.2 (by positivity)) (norm_pos_iff.2 hv), ?_, ?_⟩
  · intro f
    exact probe_zero_separation_rangeClosure rho hright (subset_closure ⟨f, rfl⟩)
  · intro g hg
    exact probe_zero_separation_rangeClosure rho hright hg

/-- Conditional only: the target's range-closure membership is the OPEN premise. -/
theorem rh_of_native_probe_range
    (h : probeTarget ∈ closure (Set.range probeOperator)) : RiemannHypothesis := by
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
    exact probeTarget_not_mem_rangeClosure rhor hr h
  · exact probeTarget_not_mem_rangeClosure rho hright h

end Zeta23.OPICARound2
