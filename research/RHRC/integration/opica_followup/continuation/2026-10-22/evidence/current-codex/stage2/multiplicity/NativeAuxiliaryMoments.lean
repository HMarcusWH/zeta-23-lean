import Mathlib.Analysis.Convolution
import Zeta23.OPICAFollowup.MultiplicityTail
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! External candidate: actual signed-kernel L2 convolution foundation.
No primary moment/residual/memory root is declared by this supporting prefix. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Zeta23.OPICAFollowup
open Zeta23.CCM

def causalFilterL2Integrand (c : ℝ → ℝ) (f : NativeCompletionL2) (s : ℝ) :
    NativeCompletionL2 := c s • nativeCompletionL2Delay s f

theorem causalFilterL2Integrand_norm (c : ℝ → ℝ) (f : NativeCompletionL2) (s : ℝ) :
    ‖causalFilterL2Integrand c f s‖ = ‖c s‖ * ‖f‖ := by
  rw [causalFilterL2Integrand,norm_smul,nativeCompletionL2Delay_norm]

theorem causalFilterL2Integrand_integrable (c : ℝ → ℝ) (hc : Integrable c)
    (f : NativeCompletionL2) : Integrable (causalFilterL2Integrand c f) := by
  have hm : AEStronglyMeasurable (causalFilterL2Integrand c f) :=
    hc.aestronglyMeasurable.smul (nativeCompletionL2Delay_continuous f).aestronglyMeasurable
  apply (hc.norm.mul_const ‖f‖).mono' hm
  exact Eventually.of_forall fun s => (causalFilterL2Integrand_norm c f s).le

def causalFilterL2Value (c : ℝ → ℝ) (f : NativeCompletionL2) : NativeCompletionL2 :=
  ∫ s : ℝ, causalFilterL2Integrand c f s

theorem causalFilterL2Value_norm_le (c : ℝ → ℝ) (f : NativeCompletionL2) :
    ‖causalFilterL2Value c f‖ ≤ (∫ s : ℝ, ‖c s‖) * ‖f‖ := by
  unfold causalFilterL2Value
  calc
    _ ≤ ∫ s : ℝ, ‖causalFilterL2Integrand c f s‖ := norm_integral_le_integral_norm _
    _ = _ := by simp_rw [causalFilterL2Integrand_norm]; rw [integral_mul_const]

theorem causalFilterL2Integrand_causal (c : ℝ → ℝ)
    (hc0 : ∀ s < 0, c s = 0) (f : nativeCompletionCausalL2) (s : ℝ) :
    causalFilterL2Integrand c (f : NativeCompletionL2) s ∈ nativeCompletionCausalL2 := by
  by_cases hs : 0 ≤ s
  · have hd := nativeCompletionL2Delay_causal hs (f : NativeCompletionL2) f.property
    change ∀ᵐ x : ℝ, x < 0 → causalFilterL2Integrand c (f : NativeCompletionL2) s x = 0
    filter_upwards [Lp.coeFn_smul (c s) (nativeCompletionL2Delay s (f : NativeCompletionL2)),hd]
      with x hx hdx
    intro hneg
    rw [causalFilterL2Integrand,hx,Pi.smul_apply,hdx hneg,smul_zero]
  · rw [causalFilterL2Integrand,hc0 s (lt_of_not_ge hs),zero_smul]
    exact nativeCompletionCausalL2.zero_mem

theorem causalFilterL2Value_causal (c : ℝ → ℝ)
    (hc0 : ∀ s < 0, c s = 0) (f : nativeCompletionCausalL2) :
    causalFilterL2Value c (f : NativeCompletionL2) ∈ nativeCompletionCausalL2 := by
  let lifted : ℝ → nativeCompletionCausalL2 := fun s =>
    ⟨causalFilterL2Integrand c (f : NativeCompletionL2) s,causalFilterL2Integrand_causal c hc0 f s⟩
  let total : nativeCompletionCausalL2 := ∫ s : ℝ, lifted s
  have hi := (nativeCompletionCausalL2.subtypeₗᵢ).integral_comp_comm (μ := volume) lifted
  change (∫ s : ℝ,causalFilterL2Integrand c (f : NativeCompletionL2) s)=
    (total : NativeCompletionL2) at hi
  unfold causalFilterL2Value
  rw [hi]
  exact total.property

theorem auxCompletionFilter_complex_memLp_two (k : ℕ) :
    MemLp (fun t : ℝ => (auxCompletionFilter k t : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (auxCompletionFilter k t : ℂ)) volume :=
    (auxCompletionFilter_measurable k).complex_ofReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  let K : ℝ := ((k+2:ℕ):ℝ)/(Nat.factorial (k+1):ℝ)
  let a : ℝ := (k:ℝ)+3/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hdom : Integrable ((Ici (0:ℝ)).indicator
      (fun t : ℝ => K^2*Real.exp (-2*a*t))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -2*a < 0) 0).const_mul _))
        |>.integrable_indicator measurableSet_Ici
  apply hdom.mono' (hm.norm.pow 2)
  filter_upwards with t
  simp only [Pi.pow_apply]
  by_cases ht : t ∈ Ici (0:ℝ)
  · rw [indicator_of_mem ht,Real.norm_of_nonneg (sq_nonneg _),Complex.norm_real,Real.norm_eq_abs]
    have hb : |auxCompletionFilter k t| ≤ K*Real.exp (-a*t) :=
      auxCompletionFilter_abs_bound k ht
    apply (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans_eq
    rw [mul_pow,←Real.exp_nat_mul]
    congr 2
    ring
  · rw [indicator_of_notMem ht,auxCompletionFilter_zero_before k (lt_of_not_ge ht)]
    simp

theorem auxiliaryDrive_complex_memLp_two (d : ℕ) :
    MemLp (fun t : ℝ => (integerDriveFamily d t : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (integerDriveFamily d t : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (integerDriveFamily_contDiff d).continuous).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using integerDriveFamily_sq_integrable d

def auxiliaryDriveCausalVector (d : ℕ) : nativeCompletionCausalL2 :=
  ⟨(auxiliaryDrive_complex_memLp_two d).toLp (fun t : ℝ => (integerDriveFamily d t : ℂ)),by
    filter_upwards [(auxiliaryDrive_complex_memLp_two d).coeFn_toLp] with t ht
    intro hneg
    rw [ht,integerDriveFamily_zero_before d (hneg.trans nativeCausalGap_pos),Complex.ofReal_zero]⟩

def nativeAuxiliaryStableVector (k d : ℕ) : nativeCompletionCausalL2 :=
  ⟨causalFilterL2Value (auxCompletionFilter k) (auxiliaryDriveCausalVector d : NativeCompletionL2),
    causalFilterL2Value_causal (auxCompletionFilter k)
      (fun _ hs => auxCompletionFilter_zero_before k hs) (auxiliaryDriveCausalVector d)⟩

theorem nativeAuxiliaryStableIntegrand_integrable (k d : ℕ) :
    Integrable (causalFilterL2Integrand (auxCompletionFilter k)
      (auxiliaryDriveCausalVector d : NativeCompletionL2)) :=
  causalFilterL2Integrand_integrable _ (auxCompletionFilter_integrable k) _

theorem nativeAuxiliaryStableVector_norm_le (k d : ℕ) :
    ‖nativeAuxiliaryStableVector k d‖ ≤
      (∫ s : ℝ, ‖auxCompletionFilter k s‖) * ‖auxiliaryDriveCausalVector d‖ := by
  exact causalFilterL2Value_norm_le _ _

theorem nativeAuxiliaryStableVector_factorial_bound (k d : ℕ) :
    ‖nativeAuxiliaryStableVector k d‖ ≤
      (2/(Nat.factorial (k+1):ℝ)) * ‖auxiliaryDriveCausalVector d‖ :=
  (nativeAuxiliaryStableVector_norm_le k d).trans
    (mul_le_mul_of_nonneg_right (auxCompletionFilter_L1_bound k) (norm_nonneg _))

def causalFilterPointwise (c : ℝ → ℝ) (f : NativeCompletionL2) (x : ℝ) : ℂ :=
  ∫ s : ℝ, (c s : ℂ) * f (x-s)

theorem causalFilterPointwise_integrable (c : ℝ → ℝ) (hc : Measurable c)
    (hc2 : MemLp (fun s : ℝ => (c s : ℂ)) 2 volume) (f : NativeCompletionL2) (x : ℝ) :
    Integrable (fun s : ℝ => (c s : ℂ) * f (x-s)) := by
  have hker : Integrable (fun s : ℝ => ‖(c s : ℂ)‖^2) :=
    (memLp_two_iff_integrable_sq_norm hc.complex_ofReal.aestronglyMeasurable).mp hc2
  have hf : Integrable (fun s : ℝ => ‖f (x-s)‖^2) :=
    (integrable_comp_sub_left (fun s : ℝ => ‖f s‖^2) x).mpr
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
  have hm : StronglyMeasurable (fun s : ℝ => (c s : ℂ)*f (x-s)) :=
    hc.complex_ofReal.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable (measurable_const.sub measurable_id))
  apply ((hker.add hf).div_const 2).mono' hm.aestronglyMeasurable
  filter_upwards with s
  change ‖(c s : ℂ)*f (x-s)‖ ≤ (‖(c s : ℂ)‖^2+‖f (x-s)‖^2)/2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖(c s : ℂ)‖-‖f (x-s)‖)]

theorem causalFilterPointwise_integral_norm_le (c : ℝ → ℝ) (hc : Measurable c)
    (hc2 : MemLp (fun s : ℝ => (c s : ℂ)) 2 volume) (f : NativeCompletionL2) (x : ℝ) :
    (∫ s : ℝ, ‖(c s : ℂ)*f (x-s)‖) ≤
      ((∫ s : ℝ, ‖(c s : ℂ)‖^2)+∫ s : ℝ, ‖f s‖^2)/2 := by
  have hker : Integrable (fun s : ℝ => ‖(c s : ℂ)‖^2) :=
    (memLp_two_iff_integrable_sq_norm hc.complex_ofReal.aestronglyMeasurable).mp hc2
  have hf : Integrable (fun s : ℝ => ‖f (x-s)‖^2) :=
    (integrable_comp_sub_left (fun s : ℝ => ‖f s‖^2) x).mpr
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
  calc
    _ ≤ ∫ s : ℝ, (‖(c s : ℂ)‖^2+‖f (x-s)‖^2)/2 := by
      apply integral_mono (causalFilterPointwise_integrable c hc hc2 f x).norm
        ((hker.add hf).div_const 2)
      intro s
      change ‖(c s : ℂ)*f (x-s)‖ ≤ (‖(c s : ℂ)‖^2+‖f (x-s)‖^2)/2
      rw [norm_mul]
      nlinarith [sq_nonneg (‖(c s : ℂ)‖-‖f (x-s)‖)]
    _ = _ := by
      rw [integral_div,integral_add hker hf,
        integral_sub_left_eq_self (fun s : ℝ => ‖f s‖^2) volume x]

theorem causalFilterPointwise_integrable_prod_on_finite_set (c : ℝ → ℝ) (hc : Measurable c)
    (hc2 : MemLp (fun s : ℝ => (c s : ℂ)) 2 volume) (f : NativeCompletionL2)
    (S : Set ℝ) (hS : volume S < ∞) :
    Integrable (fun p : ℝ×ℝ => (c p.2 : ℂ)*f (p.1-p.2))
      ((volume.restrict S).prod volume) := by
  let F : ℝ×ℝ → ℂ := fun p => (c p.2 : ℂ)*f (p.1-p.2)
  have hk : Measurable (fun p : ℝ×ℝ => (c p.2 : ℂ)) :=
    hc.complex_ofReal.comp measurable_snd
  have hf : StronglyMeasurable (fun p : ℝ×ℝ => f (p.1-p.2)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_fst.sub measurable_snd)
  have hm : StronglyMeasurable F := hk.stronglyMeasurable.mul hf
  have hmae : AEStronglyMeasurable F ((volume.restrict S).prod volume) := hm.aestronglyMeasurable
  apply (integrable_prod_iff hmae).mpr
  constructor
  · exact Eventually.of_forall (causalFilterPointwise_integrable c hc hc2 f)
  · let C : ℝ := ((∫ s : ℝ, ‖(c s : ℂ)‖^2)+∫ s : ℝ, ‖f s‖^2)/2
    have hinner : AEStronglyMeasurable (fun x : ℝ => ∫ s : ℝ, ‖F (x,s)‖)
        (volume.restrict S) := hmae.norm.integral_prod_right'
    apply (integrableOn_const (μ := volume) (s := S) (C := C) hS.ne).mono' hinner
    filter_upwards with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact causalFilterPointwise_integral_norm_le c hc hc2 f x

theorem causalFilterL2Integrand_inner_indicator (c : ℝ → ℝ) (f : NativeCompletionL2)
    (S : Set ℝ) (hS : MeasurableSet S) (hfinite : volume S ≠ ∞) (s : ℝ) :
    inner ℂ (indicatorConstLp 2 hS hfinite (1:ℂ)) (causalFilterL2Integrand c f s)=
      ∫ x : ℝ in S, (c s : ℂ)*f (x-s) := by
  rw [L2.inner_indicatorConstLp_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (c s) (nativeCompletionL2Delay s f)),
    ae_restrict_of_ae (nativeCompletionL2Delay_coeFn s f)] with x hx hd
  change (c s • nativeCompletionL2Delay s f) x = _
  rw [hx,Pi.smul_apply,hd,RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul,
    RCLike.ofReal_eq_complex_ofReal]

theorem causalFilterL2Value_setIntegral_pointwise (c : ℝ → ℝ) (hc : Measurable c)
    (hc1 : Integrable c) (hc2 : MemLp (fun s : ℝ => (c s : ℂ)) 2 volume)
    (f : NativeCompletionL2) (S : Set ℝ) (hS : MeasurableSet S) (hfinite : volume S < ∞) :
    (∫ x : ℝ in S, causalFilterL2Value c f x)=∫ x : ℝ in S,causalFilterPointwise c f x := by
  rw [←L2.inner_indicatorConstLp_one hS hfinite.ne,causalFilterL2Value]
  change inner ℂ (indicatorConstLp 2 hS hfinite.ne (1:ℂ))
    (∫ s : ℝ,causalFilterL2Integrand c f s)=_
  rw [←integral_inner (𝕜 := ℂ) (causalFilterL2Integrand_integrable c hc1 f)]
  simp_rw [causalFilterL2Integrand_inner_indicator c f S hS hfinite.ne]
  exact (integral_integral_swap
    (causalFilterPointwise_integrable_prod_on_finite_set c hc hc2 f S hfinite)).symm

theorem causalFilterL2Value_coe_pointwise (c : ℝ → ℝ) (hc : Measurable c)
    (hc1 : Integrable c) (hc2 : MemLp (fun s : ℝ => (c s : ℂ)) 2 volume)
    (f : NativeCompletionL2) : causalFilterL2Value c f =ᵐ[volume] causalFilterPointwise c f := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S _ hS
    exact integrableOn_Lp_of_measure_ne_top (causalFilterL2Value c f) (by norm_num) hS.ne
  · intro S _ hS
    exact (causalFilterPointwise_integrable_prod_on_finite_set c hc hc2 f S hS).integral_prod_left
  · exact causalFilterL2Value_setIntegral_pointwise c hc hc1 hc2 f

def nativeAuxiliaryInput (k d : ℕ) (t : ℝ) : ℂ :=
  ∫ s : ℝ,(auxCompletionFilter k s : ℂ)*(integerDriveFamily d (t-s) : ℂ)

theorem auxiliaryDriveCausalVector_coe (d : ℕ) :
    (auxiliaryDriveCausalVector d : NativeCompletionL2) =ᵐ[volume]
      fun t : ℝ => (integerDriveFamily d t : ℂ) :=
  (auxiliaryDrive_complex_memLp_two d).coeFn_toLp

theorem nativeAuxiliaryStableVector_coe_input (k d : ℕ) :
    (nativeAuxiliaryStableVector k d : NativeCompletionL2) =ᵐ[volume] nativeAuxiliaryInput k d := by
  have hg := causalFilterL2Value_coe_pointwise (auxCompletionFilter k)
    (auxCompletionFilter_measurable k) (auxCompletionFilter_integrable k)
    (auxCompletionFilter_complex_memLp_two k) (auxiliaryDriveCausalVector d : NativeCompletionL2)
  apply hg.trans
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  have hd := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq
    (auxiliaryDriveCausalVector_coe d)
  filter_upwards [hd] with s hs
  exact congrArg (fun x : ℂ => (auxCompletionFilter k s : ℂ)*x) hs

theorem nativeAuxiliaryInput_memLp_two (k d : ℕ) : MemLp (nativeAuxiliaryInput k d) 2 volume :=
  MemLp.ae_eq (nativeAuxiliaryStableVector_coe_input k d)
    (Lp.memLp (nativeAuxiliaryStableVector k d : NativeCompletionL2))

theorem nativeAuxiliaryInput_zero_before (k d : ℕ) {t : ℝ} (ht : t < 0) :
    nativeAuxiliaryInput k d t=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with s
  change (auxCompletionFilter k s : ℂ)*(integerDriveFamily d (t-s) : ℂ)=0
  by_cases hs : s < 0
  · rw [auxCompletionFilter_zero_before k hs,Complex.ofReal_zero,zero_mul]
  · rw [integerDriveFamily_zero_before d (by linarith [nativeCausalGap_pos]),
      Complex.ofReal_zero,mul_zero]


/-! Actual physical auxiliary input: safe-domain transform and connected
continuation. The integral is not identified with a raw totalized expression
at the removable elementary point. -/

open scoped Convolution

theorem dampedConvolution_integrable_laplace (f g : ℝ → ℂ) (z : ℂ)
    (hf : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*f t))
    (hg : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*g t)) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,f s*g (t-s))) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,f s*g (t-s)))=
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*f t)*
        (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*g t) := by
  let df : ℝ → ℂ := fun t => Complex.exp (-z*(t:ℂ))*f t
  let dg : ℝ → ℂ := fun t => Complex.exp (-z*(t:ℂ))*g t
  have heq : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,f s*g (t-s)))=
      df ⋆[ContinuousLinearMap.mul ℂ ℂ] dg := by
    funext t
    rw [convolution_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    dsimp [df,dg]
    have hexp : Complex.exp (-z*(t:ℂ))=
        Complex.exp (-z*(s:ℂ))*Complex.exp (-z*((t-s:ℝ):ℂ)) := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [heq]
  exact ⟨hf.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hg,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg⟩

def nativeAuxiliaryInputLaplace (k d : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,Complex.exp (-z*(t:ℂ))*nativeAuxiliaryInput k d t

def nativeAuxiliaryInputContinuation (k d : ℕ) (z : ℂ) : ℂ :=
  auxRationalFactor k z*forwardKernelEntireContinuation d 0 z

theorem nativeAuxiliaryInput_initial_laplace (k d : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*nativeAuxiliaryInput k d t) ∧
      nativeAuxiliaryInputLaplace k d z=
        -auxRationalFactor k z*sourceFamilyLaplace d z*deriv riemannZeta (z+1/2) := by
  have hc := auxCompletionFilter_integrable_laplace k (z := z) (by
    linarith [Nat.cast_nonneg (α := ℝ) k])
  have hu := integerDriveFamily_integrable_laplace d hz
  have hconv := dampedConvolution_integrable_laplace
    (fun t => (auxCompletionFilter k t:ℂ)) (fun t => (integerDriveFamily d t:ℂ)) z hc.1 hu.1
  refine ⟨hconv.1,?_⟩
  change (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,
    (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=_
  rw [hconv.2,hc.2,hu.2]
  ring

theorem auxRationalFactor_analytic_right (k : ℕ) {z : ℂ} (hz : 0<z.re) :
    AnalyticAt ℂ (auxRationalFactor k) z := by
  unfold auxRationalFactor
  exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w-1/2) z).div (by fun_prop)
    (auxDenominator_ne_zero k z (by
    dsimp [auxCompletionAlpha]
    linarith [Nat.cast_nonneg (α := ℝ) k]))

theorem nativeAuxiliaryInputContinuation_analytic_right (k d : ℕ) {z : ℂ}
    (hz : 0<z.re) : AnalyticAt ℂ (nativeAuxiliaryInputContinuation k d) z :=
  (auxRationalFactor_analytic_right k hz).mul (forwardKernelEntireContinuation_analyticAt d 0 z)

theorem nativeAuxiliaryInputLaplace_eq_causalMoment (k d : ℕ) (z : ℂ) :
    nativeAuxiliaryInputLaplace k d z=nativeCausalLaplaceMoment z 0
      (nativeAuxiliaryStableVector k d:NativeCompletionL2) := by
  apply integral_congr_ae
  filter_upwards [nativeAuxiliaryStableVector_coe_input k d] with t ht
  simp only [pow_zero,one_mul,ht]

theorem nativeAuxiliaryInputLaplace_analytic_right (k d : ℕ) {z : ℂ} (hz : 0<z.re) :
    AnalyticAt ℂ (nativeAuxiliaryInputLaplace k d) z := by
  have he : nativeAuxiliaryInputLaplace k d=
      fun w => nativeCausalLaplaceMoment w 0 (nativeAuxiliaryStableVector k d:NativeCompletionL2) :=
    funext (nativeAuxiliaryInputLaplace_eq_causalMoment k d)
  rw [he]
  exact nativeCausalLaplaceMoment_analyticAt z hz 0 _

theorem nativeAuxiliaryInputLaplace_eq_continuation (k d : ℕ) {z : ℂ} (hz : 0<z.re) :
    nativeAuxiliaryInputLaplace k d z=nativeAuxiliaryInputContinuation k d z := by
  let U : Set ℂ := {w | 0<w.re}
  have ha : AnalyticOnNhd ℂ (nativeAuxiliaryInputLaplace k d) U :=
    fun _ hw => nativeAuxiliaryInputLaplace_analytic_right k d hw
  have hb : AnalyticOnNhd ℂ (nativeAuxiliaryInputContinuation k d) U :=
    fun _ hw => nativeAuxiliaryInputContinuation_analytic_right k d hw
  have he : nativeAuxiliaryInputLaplace k d =ᶠ[𝓝 (1:ℂ)] nativeAuxiliaryInputContinuation k d := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1:ℂ)∈{w:ℂ | 1/2<w.re})] with w hw
    have hne : w≠(1/2:ℂ) := by intro h; subst w; norm_num at hw
    rw [(nativeAuxiliaryInput_initial_laplace k d hw).2,nativeAuxiliaryInputContinuation,
      forwardKernelEntireContinuation_agrees d 0 (Nat.zero_le _) hne,
      forwardKernelTransformGerm,pow_zero,mul_one]
    ring
  exact (ha.eqOn_of_preconnected_of_eventuallyEq hb
    (convex_halfSpace_re_gt 0).isPreconnected (by dsimp [U]; norm_num : (1:ℂ)∈U) he) hz

def nativeAuxiliaryMoment (k d : ℕ) (p : ℂ) (j : ℕ) : ℂ :=
  ∫ t : ℝ,(t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeAuxiliaryInput k d t

theorem nativeAuxiliaryMoment_integrable (k d j : ℕ) {p : ℂ} (hp : 0<p.re) :
    Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeAuxiliaryInput k d t) := by
  apply (nativeCausalLaplaceMoment_integrable p hp j (nativeAuxiliaryStableVector k d)).congr
  filter_upwards [nativeAuxiliaryStableVector_coe_input k d] with t ht
  rw [ht]

theorem nativeAuxiliaryMoment_eq_causalMoment (k d j : ℕ) (p : ℂ) :
    nativeAuxiliaryMoment k d p j=nativeCausalLaplaceMoment p j
      (nativeAuxiliaryStableVector k d:NativeCompletionL2) := by
  apply integral_congr_ae
  filter_upwards [nativeAuxiliaryStableVector_coe_input k d] with t ht
  rw [ht]

#print axioms nativeAuxiliaryInput_initial_laplace
#print axioms nativeAuxiliaryInputLaplace_eq_continuation
#print axioms nativeAuxiliaryMoment_integrable

end Zeta23.OPICAFollowup
