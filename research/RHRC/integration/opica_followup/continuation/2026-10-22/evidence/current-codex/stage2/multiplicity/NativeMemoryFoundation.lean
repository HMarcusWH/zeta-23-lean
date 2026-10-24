import Zeta23.CCM.NativeCompletionEquation
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


open Zeta23.ExceptionalZero

theorem auxiliary_centered_zero_ne_half (rho : zetaZeroConfig.carrier) :
    (rho:ℂ)-1/2≠(1/2:ℂ) := by
  intro h
  apply rho.property.not_trivial.2
  linear_combination h

def nativeAuxiliaryInputMultiplier (k d : ℕ) (z : ℂ) : ℂ :=
  -(auxRationalFactor k z*sourceFamilyLaplace d z)*deriv riemannZeta (z+1/2)

theorem nativeAuxiliaryInputLaplace_eventuallyEq_multiplier (k d : ℕ) {p : ℂ}
    (hp : 0<p.re) (hne : p≠1/2) :
    nativeAuxiliaryInputLaplace k d =ᶠ[𝓝 p] nativeAuxiliaryInputMultiplier k d := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp,
    eventually_ne_nhds hne] with z hz hzne
  rw [nativeAuxiliaryInputLaplace_eq_continuation k d hz,nativeAuxiliaryInputContinuation,
    forwardKernelEntireContinuation_agrees d 0 (Nat.zero_le _) hzne,
    forwardKernelTransformGerm,pow_zero,mul_one,nativeAuxiliaryInputMultiplier]
  ring

theorem auxiliary_iteratedDeriv_mul_vanishing {g h : ℂ → ℂ} {p : ℂ} (j : ℕ)
    (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hzero : ∀ i≤j,iteratedDeriv i h p=0) :
    iteratedDeriv j (fun z => g z*h z) p=0 := by
  rw [iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt]
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero (j-i) (Nat.sub_le _ _),mul_zero]

theorem auxiliary_iteratedDeriv_mul_leading {g h : ℂ → ℂ} {p : ℂ} (j : ℕ)
    (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hzero : ∀ i<j,iteratedDeriv i h p=0) :
    iteratedDeriv j (fun z => g z*h z) p=g p*iteratedDeriv j h p := by
  rw [iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt,Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right,Nat.cast_one,iteratedDeriv_zero,one_mul,tsub_zero]
  · intro i hi hine
    have hile := Finset.mem_range.mp hi
    rw [hzero (j-i) (by omega),mul_zero]
  · simp only [Finset.mem_range,Nat.zero_lt_succ,not_true_eq_false,false_implies]

theorem auxiliary_shiftedZetaDeriv_analytic (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta (z+1/2)) ((rho:ℂ)-1/2) := by
  have hz : AnalyticAt ℂ (deriv riemannZeta) ((rho:ℂ)-1/2+1/2) := by
    simpa only [sub_add_cancel] using
      (riemannZeta_analyticOnNhd_compl_one _ rho.property.not_trivial.2).deriv
  exact hz.comp (f := fun z : ℂ => z+1/2) (x := (rho:ℂ)-1/2) (by fun_prop)

theorem auxiliary_shiftedZetaDeriv_iterated (rho : zetaZeroConfig.carrier) (j : ℕ) :
    iteratedDeriv j (fun z : ℂ => deriv riemannZeta (z+1/2)) ((rho:ℂ)-1/2)=
      iteratedDeriv (j+1) riemannZeta (rho:ℂ) := by
  simp only [iteratedDeriv_comp_add_const,sub_add_cancel,←iteratedDeriv_succ']

theorem auxiliary_zeta_deriv_vanishes_below (rho : zetaZeroConfig.carrier) {j : ℕ}
    (hj : j<zeroMult (rho:ℂ)) : iteratedDeriv j riemannZeta (rho:ℂ)=0 := by
  have ha := riemannZeta_analyticOnNhd_compl_one (rho:ℂ) rho.property.not_trivial.2
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mp
    (nativeZeroMultiplicity_order rho)).1 j hj

theorem nativeAuxiliaryInputMultiplier_lowJet (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {j : ℕ} (hj : j<zeroMult (rho:ℂ)-1) :
    iteratedDeriv j (nativeAuxiliaryInputMultiplier k d) ((rho:ℂ)-1/2)=0 := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  apply auxiliary_iteratedDeriv_mul_vanishing j
    (((auxRationalFactor_analytic_right k hp).mul (sourceFamilyLaplace_analyticAt d _)).neg)
    (auxiliary_shiftedZetaDeriv_analytic rho)
  intro i hi
  rw [auxiliary_shiftedZetaDeriv_iterated]
  exact auxiliary_zeta_deriv_vanishes_below rho (by omega)

theorem nativeAuxiliaryInputMultiplier_topJet (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    iteratedDeriv (zeroMult (rho:ℂ)-1) (nativeAuxiliaryInputMultiplier k d) ((rho:ℂ)-1/2)=
      -(auxRationalFactor k ((rho:ℂ)-1/2)*sourceFamilyLaplace d ((rho:ℂ)-1/2))*
        iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ) := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hm : 1≤zeroMult (rho:ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  change iteratedDeriv (zeroMult (rho:ℂ)-1) (fun z : ℂ =>
    -(auxRationalFactor k z*sourceFamilyLaplace d z)*deriv riemannZeta (z+1/2)) _=_
  rw [auxiliary_iteratedDeriv_mul_leading
    (g := fun z : ℂ => -(auxRationalFactor k z*sourceFamilyLaplace d z))
    (h := fun z : ℂ => deriv riemannZeta (z+1/2)) (zeroMult (rho:ℂ)-1)
    (((auxRationalFactor_analytic_right k hp).mul (sourceFamilyLaplace_analyticAt d _)).neg)
    (auxiliary_shiftedZetaDeriv_analytic rho)]
  · rw [auxiliary_shiftedZetaDeriv_iterated,show zeroMult (rho:ℂ)-1+1=zeroMult (rho:ℂ) by omega]
  · intro i hi
    rw [auxiliary_shiftedZetaDeriv_iterated]
    exact auxiliary_zeta_deriv_vanishes_below rho (by omega)

theorem nativeAuxiliaryMoment_derivative (k d j : ℕ) {p : ℂ} (hp : 0<p.re) :
    iteratedDeriv j (nativeAuxiliaryInputLaplace k d) p=
      (-1:ℂ)^j*nativeAuxiliaryMoment k d p j := by
  have he : nativeAuxiliaryInputLaplace k d=
      fun w => nativeCausalLaplaceMoment w 0 (nativeAuxiliaryStableVector k d:NativeCompletionL2) :=
    funext (nativeAuxiliaryInputLaplace_eq_causalMoment k d)
  rw [he,nativeCausalLaplaceMoment_iteratedDeriv p hp j,
    nativeAuxiliaryMoment_eq_causalMoment]

theorem nativeAuxiliaryMoment_vanishes_below (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {j : ℕ} (hj : j<zeroMult (rho:ℂ)-1) :
    nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) j=0 := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hd := (nativeAuxiliaryInputLaplace_eventuallyEq_multiplier k d hp
    (auxiliary_centered_zero_ne_half rho)).iteratedDeriv_eq j
  rw [nativeAuxiliaryMoment_derivative k d j hp,nativeAuxiliaryInputMultiplier_lowJet k d rho hright hj] at hd
  exact (mul_eq_zero.mp hd).resolve_left (pow_ne_zero _ (by norm_num))

theorem nativeAuxiliaryMoment_top_value (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1)=
      (-1:ℂ)^zeroMult (rho:ℂ)*auxRationalFactor k ((rho:ℂ)-1/2)*
        sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ) := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hm : 1≤zeroMult (rho:ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  have hd := (nativeAuxiliaryInputLaplace_eventuallyEq_multiplier k d hp
    (auxiliary_centered_zero_ne_half rho)).iteratedDeriv_eq (zeroMult (rho:ℂ)-1)
  rw [nativeAuxiliaryMoment_derivative k d _ hp,nativeAuxiliaryInputMultiplier_topJet k d rho hright] at hd
  have hphase : (-1:ℂ)^zeroMult (rho:ℂ)=-((-1:ℂ)^(zeroMult (rho:ℂ)-1)) := by
    calc
      (-1:ℂ)^zeroMult (rho:ℂ)=(-1:ℂ)^(zeroMult (rho:ℂ)-1+1) := by
        congr 1
        omega
      _ = _ := by rw [pow_succ]; ring
  have hcancel : (-1:ℂ)^(zeroMult (rho:ℂ)-1)*(-1:ℂ)^(zeroMult (rho:ℂ)-1)=1 := by
    rw [←mul_pow]
    norm_num
  calc
    _ = (-1:ℂ)^(zeroMult (rho:ℂ)-1)*
        ((-1:ℂ)^(zeroMult (rho:ℂ)-1)*nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1)) := by
      rw [←mul_assoc,hcancel,one_mul]
    _ = _ := by rw [hd,hphase]; ring


theorem nativeAuxiliaryInput_integrand_integrable (k d : ℕ) (t : ℝ) :
    Integrable (fun s : ℝ => (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) := by
  apply (causalFilterPointwise_integrable (auxCompletionFilter k)
    (auxCompletionFilter_measurable k) (auxCompletionFilter_complex_memLp_two k)
    (auxiliaryDriveCausalVector d:NativeCompletionL2) t).congr
  have hd := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq
    (auxiliaryDriveCausalVector_coe d)
  filter_upwards [hd] with s hs
  exact congrArg (fun x : ℂ => (auxCompletionFilter k s:ℂ)*x) hs

/-- The actual integer-prime arithmetic compatibility is used here, before
any global Hilbert-space or range assertion about the prime field. -/
theorem nativeAuxiliaryInput_completedPrime (k d : ℕ) (t : ℝ) :
    (∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(primeFieldFamily d (t-s):ℂ))=
      nativeAuxiliaryInput k d t := by
  have hr : (∫ s : ℝ,auxCompletionKernel k s*primeFieldFamily d (t-s))=
      ∫ s : ℝ,auxCompletionFilter k s*integerDriveFamily d (t-s) := by
    unfold auxCompletionKernel
    rw [nativeIntegerTranslate_causal_convolution_comm (auxCompletionFilter_integrable k)
      (fun _ hs => auxCompletionFilter_zero_before k hs)
      (primeFieldFamily_contDiff d).continuous
      (fun _ hs => primeFieldFamily_zero_before d (hs.trans nativeCausalGap_pos))]
    apply integral_congr_ae
    filter_upwards with s
    rw [show nativeIntegerTranslateAction (primeFieldFamily d) (t-s)=
        integerDriveFamily d (t-s) from
      nativeIntegerTranslateAction_primeField_eq_integerDriveField (sourceFamily_supported d) (t-s)]
  simpa only [nativeAuxiliaryInput,←Complex.ofReal_mul,integral_complex_ofReal] using
    congrArg Complex.ofReal hr

theorem nativeAuxiliaryMoment_top_ne_zero (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1)≠0 := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hz := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (riemannZeta_analyticOnNhd_compl_one (rho:ℂ) rho.property.not_trivial.2)).mp
      (nativeZeroMultiplicity_order rho)).2
  rw [nativeAuxiliaryMoment_top_value k d rho hright]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (auxRationalFactor_ne_zero hp (auxiliary_centered_zero_ne_half rho) k))
      (sourceFamilyLaplace_ne_zero_at_right_zero d rho hright)) hz

/-- Full actual auxiliary moment packet. In particular the actual physical
completed input is constructed and identified; no moment, transform, source
factorization, stability, or prime-field L2 conclusion is supplied as data. -/
theorem native_auxiliary_top_moment (k d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    MemLp (nativeAuxiliaryInput k d) 2 volume ∧
    (nativeAuxiliaryStableVector k d:NativeCompletionL2)=ᵐ[volume] nativeAuxiliaryInput k d ∧
    (∀ t : ℝ,(∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(primeFieldFamily d (t-s):ℂ))=
      nativeAuxiliaryInput k d t) ∧
    ‖nativeAuxiliaryStableVector k d‖≤
      (∫ s : ℝ,‖auxCompletionFilter k s‖)*‖auxiliaryDriveCausalVector d‖ ∧
    (∀ j<zeroMult (rho:ℂ)-1,
      Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*nativeAuxiliaryInput k d t) ∧
      nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) j=0) ∧
    Integrable (fun t : ℝ => (t:ℂ)^(zeroMult (rho:ℂ)-1)*
      Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*nativeAuxiliaryInput k d t) ∧
    nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1)=
      (-1:ℂ)^zeroMult (rho:ℂ)*auxRationalFactor k ((rho:ℂ)-1/2)*
        sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ) ∧
    nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1)≠0 := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  exact ⟨nativeAuxiliaryInput_memLp_two k d,nativeAuxiliaryStableVector_coe_input k d,
    nativeAuxiliaryInput_completedPrime k d,nativeAuxiliaryStableVector_norm_le k d,
    fun j hj => ⟨nativeAuxiliaryMoment_integrable k d j hp,
      nativeAuxiliaryMoment_vanishes_below k d rho hright hj⟩,
    nativeAuxiliaryMoment_integrable k d _ hp,
    nativeAuxiliaryMoment_top_value k d rho hright,nativeAuxiliaryMoment_top_ne_zero k d rho hright⟩


/-! Actual finite-history objects. No global prime-field L2 membership. -/

def nativePrimeTruncation (d : ℕ) (T : ℝ) : ℝ → ℝ :=
  (Icc (0:ℝ) T).indicator (primeFieldFamily d)

def tailMemory (alpha : ℝ) (d : ℕ) (T : ℝ) : ℝ :=
  ∫ s : ℝ in Icc 0 T,Real.exp (-alpha*(T-s))*|primeFieldFamily d s|

theorem nativePrimeTruncation_complex_memLp_two (d : ℕ) (T : ℝ) :
    MemLp (fun t : ℝ => (nativePrimeTruncation d T t:ℂ)) 2 volume := by
  have hm : Measurable (fun t : ℝ => (nativePrimeTruncation d T t:ℂ)) :=
    (Complex.measurable_ofReal.comp
      ((primeFieldFamily_contDiff d).continuous.measurable.indicator measurableSet_Icc))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hc : Continuous (fun t : ℝ => ‖(primeFieldFamily d t:ℂ)‖^2) :=
    ((Complex.continuous_ofReal.comp (primeFieldFamily_contDiff d).continuous).norm).pow 2
  have hi : IntegrableOn (fun t : ℝ => ‖(primeFieldFamily d t:ℂ)‖^2) (Icc 0 T) :=
    hc.integrableOn_Icc
  apply (hi.integrable_indicator measurableSet_Icc).congr
  filter_upwards with t
  by_cases ht : t∈Icc (0:ℝ) T <;> simp [nativePrimeTruncation,ht]

def nativePrimeTruncationCausalVector (d : ℕ) (T : ℝ) : nativeCompletionCausalL2 :=
  ⟨(nativePrimeTruncation_complex_memLp_two d T).toLp
      (fun t : ℝ => (nativePrimeTruncation d T t:ℂ)),by
    filter_upwards [(nativePrimeTruncation_complex_memLp_two d T).coeFn_toLp] with t ht
    intro hneg
    rw [ht,nativePrimeTruncation,indicator_of_notMem (fun h => (not_le.mpr hneg) h.1),Complex.ofReal_zero]⟩

theorem nativePrimeTruncationCausalVector_coe (d : ℕ) (T : ℝ) :
    (nativePrimeTruncationCausalVector d T:NativeCompletionL2)=ᵐ[volume]
      fun t : ℝ => (nativePrimeTruncation d T t:ℂ) :=
  (nativePrimeTruncation_complex_memLp_two d T).coeFn_toLp

theorem nativePrimeTruncation_integrable_laplace (d : ℕ) (T : ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(nativePrimeTruncation d T t:ℂ)) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(primeFieldFamily d t:ℂ)) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).mul
      (Complex.continuous_ofReal.comp (primeFieldFamily_contDiff d).continuous)
  have hi : IntegrableOn
      (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(primeFieldFamily d t:ℂ)) (Icc 0 T) :=
    hc.integrableOn_Icc
  apply (hi.integrable_indicator measurableSet_Icc).congr
  filter_upwards with t
  by_cases ht : t∈Icc (0:ℝ) T <;> simp [nativePrimeTruncation,ht]

theorem auxCompletionKernel_integrable (k : ℕ) (hk : 1≤k) :
    Integrable (auxCompletionKernel k) := by
  have h := auxCompletionKernel_laplace_integrable k hk (z := 0) (by
    dsimp [auxCompletionAlpha]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) k])
  simpa using h.re

theorem auxCompletionKernel_complex_memLp_two (k : ℕ) (hk : 1≤k) :
    MemLp (fun t : ℝ => (auxCompletionKernel k t:ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (auxCompletionKernel k t:ℂ)) volume :=
    (auxCompletionKernel_measurable k).complex_ofReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  let A := auxCompletionBound k
  let a := auxCompletionAlpha k
  have ha : 0<a := by dsimp [a,auxCompletionAlpha]; positivity
  have hdom : Integrable ((Ici (0:ℝ)).indicator (fun t : ℝ => A^2*Real.exp (-2*a*t))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -2*a<0) 0).const_mul _))
        |>.integrable_indicator measurableSet_Ici
  apply hdom.mono' (hm.norm.pow 2)
  filter_upwards with t
  simp only [Pi.pow_apply]
  by_cases ht : t∈Ici (0:ℝ)
  · rw [indicator_of_mem ht,Real.norm_of_nonneg (sq_nonneg _),Complex.norm_real,Real.norm_eq_abs]
    have hb : |auxCompletionKernel k t|≤A*Real.exp (-a*t) := (aux_completion_uniform_decay k hk).2 t
    apply (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans_eq
    rw [mul_pow,←Real.exp_nat_mul]
    congr 2
    ring
  · rw [indicator_of_notMem ht,auxCompletionKernel_zero_before k (lt_of_not_ge ht)]
    simp

def nativeAuxiliaryTruncatedImage (k d : ℕ) (T t : ℝ) : ℂ :=
  ∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(nativePrimeTruncation d T (t-s):ℂ)

def nativeAuxiliaryTruncatedVector (k d : ℕ) (T : ℝ) : nativeCompletionCausalL2 :=
  ⟨causalFilterL2Value (auxCompletionKernel k) (nativePrimeTruncationCausalVector d T:NativeCompletionL2),
    causalFilterL2Value_causal (auxCompletionKernel k)
      (fun _ hs => auxCompletionKernel_zero_before k hs) (nativePrimeTruncationCausalVector d T)⟩

theorem nativeAuxiliaryTruncatedVector_coe (k d : ℕ) (T : ℝ) (hk : 1≤k) :
    (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2)=ᵐ[volume]
      nativeAuxiliaryTruncatedImage k d T := by
  have hg := causalFilterL2Value_coe_pointwise (auxCompletionKernel k)
    (auxCompletionKernel_measurable k) (auxCompletionKernel_integrable k hk)
    (auxCompletionKernel_complex_memLp_two k hk) (nativePrimeTruncationCausalVector d T:NativeCompletionL2)
  apply hg.trans
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  have hd := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq
    (nativePrimeTruncationCausalVector_coe d T)
  filter_upwards [hd] with s hs
  exact congrArg (fun x : ℂ => (auxCompletionKernel k s:ℂ)*x) hs

def nativeTruncatedResidual (k d : ℕ) (T t : ℝ) : ℂ :=
  nativeAuxiliaryInput k d t-nativeAuxiliaryTruncatedImage k d T t

def nativeTruncatedResidualVector (k d : ℕ) (T : ℝ) : nativeCompletionCausalL2 :=
  nativeAuxiliaryStableVector k d-nativeAuxiliaryTruncatedVector k d T

theorem nativeTruncatedResidualVector_coe (k d : ℕ) (T : ℝ) (hk : 1≤k) :
    (nativeTruncatedResidualVector k d T:NativeCompletionL2)=ᵐ[volume]
      nativeTruncatedResidual k d T := by
  filter_upwards [Lp.coeFn_sub (nativeAuxiliaryStableVector k d:NativeCompletionL2)
    (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2),
    nativeAuxiliaryStableVector_coe_input k d,nativeAuxiliaryTruncatedVector_coe k d T hk]
    with t hsub hy hf
  change ((nativeAuxiliaryStableVector k d:NativeCompletionL2)-
    (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2)) t=_
  rw [hsub,Pi.sub_apply,hy,hf]
  rfl

theorem nativeTruncatedResidual_memLp_two (k d : ℕ) (T : ℝ) (hk : 1≤k) :
    MemLp (nativeTruncatedResidual k d T) 2 volume :=
  MemLp.ae_eq (nativeTruncatedResidualVector_coe k d T hk)
    (Lp.memLp (nativeTruncatedResidualVector k d T:NativeCompletionL2))

theorem nativeTruncatedResidual_zero_before (k d : ℕ) (T : ℝ) {t : ℝ} (ht : t<T) :
    nativeTruncatedResidual k d T t=0 := by
  unfold nativeTruncatedResidual
  rw [←nativeAuxiliaryInput_completedPrime k d t,nativeAuxiliaryTruncatedImage]
  apply sub_eq_zero.mpr
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s<0
  · rw [auxCompletionKernel_zero_before k hs,Complex.ofReal_zero,zero_mul,zero_mul]
  · have he : nativePrimeTruncation d T (t-s)=primeFieldFamily d (t-s) := by
      unfold nativePrimeTruncation
      by_cases h0 : 0≤t-s
      · have hmem : t-s∈Icc (0:ℝ) T := ⟨h0,by linarith⟩
        exact indicator_of_mem hmem _
      · rw [indicator_of_notMem (fun h => h0 h.1),
          primeFieldFamily_zero_before d ((lt_of_not_ge h0).trans nativeCausalGap_pos)]
    rw [he]


def nativePrimeTruncationLaplace (d : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(nativePrimeTruncation d T t:ℂ)

def nativeAuxiliaryTruncatedLaplace (k d : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,Complex.exp (-z*(t:ℂ))*nativeAuxiliaryTruncatedImage k d T t

def nativeAuxiliaryTruncatedMoment (k d : ℕ) (T : ℝ) (p : ℂ) (j : ℕ) : ℂ :=
  ∫ t : ℝ,(t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeAuxiliaryTruncatedImage k d T t

def nativeTruncatedResidualMoment (k d : ℕ) (T : ℝ) (p : ℂ) (j : ℕ) : ℂ :=
  ∫ t : ℝ,(t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeTruncatedResidual k d T t

theorem nativePrimeTruncationLaplace_eq_causalMoment (d : ℕ) (T : ℝ) (z : ℂ) :
    nativePrimeTruncationLaplace d T z=nativeCausalLaplaceMoment z 0
      (nativePrimeTruncationCausalVector d T:NativeCompletionL2) := by
  apply integral_congr_ae
  filter_upwards [nativePrimeTruncationCausalVector_coe d T] with t ht
  simp only [pow_zero,one_mul,ht]

theorem nativePrimeTruncationLaplace_analytic_right (d : ℕ) (T : ℝ) {z : ℂ} (hz : 0<z.re) :
    AnalyticAt ℂ (nativePrimeTruncationLaplace d T) z := by
  have he : nativePrimeTruncationLaplace d T=fun w => nativeCausalLaplaceMoment w 0
      (nativePrimeTruncationCausalVector d T:NativeCompletionL2) :=
    funext (nativePrimeTruncationLaplace_eq_causalMoment d T)
  rw [he]
  exact nativeCausalLaplaceMoment_analyticAt z hz 0 _

theorem nativeAuxiliaryTruncatedLaplace_eq_product (k d : ℕ) (T : ℝ) (hk : 1≤k)
    {z : ℂ} (hz : 0<z.re) :
    nativeAuxiliaryTruncatedLaplace k d T z=
      auxCompletionLaplace k z*nativePrimeTruncationLaplace d T z := by
  have ha := auxCompletionKernel_laplace_integrable k hk (z := z) (by
    dsimp [auxCompletionAlpha]
    linarith [Nat.cast_nonneg (α := ℝ) k])
  exact (dampedConvolution_integrable_laplace
    (fun t => (auxCompletionKernel k t:ℂ))
    (fun t => (nativePrimeTruncation d T t:ℂ)) z ha
    (nativePrimeTruncation_integrable_laplace d T z)).2

theorem nativeAuxiliaryTruncatedMoment_integrable (k d j : ℕ) (T : ℝ) (hk : 1≤k)
    {p : ℂ} (hp : 0<p.re) :
    Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeAuxiliaryTruncatedImage k d T t) := by
  apply (nativeCausalLaplaceMoment_integrable p hp j (nativeAuxiliaryTruncatedVector k d T)).congr
  filter_upwards [nativeAuxiliaryTruncatedVector_coe k d T hk] with t ht
  rw [ht]

theorem nativeAuxiliaryTruncatedMoment_eq_causalMoment (k d j : ℕ) (T : ℝ) (hk : 1≤k) (p : ℂ) :
    nativeAuxiliaryTruncatedMoment k d T p j=nativeCausalLaplaceMoment p j
      (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2) := by
  apply integral_congr_ae
  filter_upwards [nativeAuxiliaryTruncatedVector_coe k d T hk] with t ht
  rw [ht]

theorem nativeAuxiliaryTruncatedMoment_derivative (k d j : ℕ) (T : ℝ) (hk : 1≤k)
    {p : ℂ} (hp : 0<p.re) :
    iteratedDeriv j (nativeAuxiliaryTruncatedLaplace k d T) p=
      (-1:ℂ)^j*nativeAuxiliaryTruncatedMoment k d T p j := by
  have he : nativeAuxiliaryTruncatedLaplace k d T=fun w => nativeCausalLaplaceMoment w 0
      (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2) := by
    funext w
    apply integral_congr_ae
    filter_upwards [nativeAuxiliaryTruncatedVector_coe k d T hk] with t ht
    simp only [pow_zero,one_mul,ht]
  rw [he,nativeCausalLaplaceMoment_iteratedDeriv p hp j,
    nativeAuxiliaryTruncatedMoment_eq_causalMoment k d j T hk]

theorem nativeAuxiliaryTruncatedLaplace_eventuallyEq (k d : ℕ) (T : ℝ) (hk : 1≤k)
    {p : ℂ} (hp : 0<p.re) (hne : p≠1/2) :
    nativeAuxiliaryTruncatedLaplace k d T =ᶠ[𝓝 p]
      fun z : ℂ => (auxRationalFactor k z*nativePrimeTruncationLaplace d T z)*riemannZeta (z+1/2) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp,
    eventually_ne_nhds hne] with z hz hzne
  have he := (aux_completion_actual_transform.2.2.1 k hk z (by
    dsimp [auxCompletionAlpha]
    linarith [Nat.cast_nonneg (α := ℝ) k])).2.2
  rw [nativeAuxiliaryTruncatedLaplace_eq_product k d T hk hz,he,
    auxCompletionFilledTransform_agrees k hzne]
  ring

theorem nativeAuxiliaryTruncatedMoment_vanishes (k d : ℕ) (T : ℝ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) {j : ℕ}
    (hj : j<zeroMult (rho:ℂ)) :
    nativeAuxiliaryTruncatedMoment k d T ((rho:ℂ)-1/2) j=0 := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hd := (nativeAuxiliaryTruncatedLaplace_eventuallyEq k d T hk hp
    (auxiliary_centered_zero_ne_half rho)).iteratedDeriv_eq j
  rw [nativeAuxiliaryTruncatedMoment_derivative k d j T hk hp] at hd
  have hz : iteratedDeriv j (fun z : ℂ =>
      (auxRationalFactor k z*nativePrimeTruncationLaplace d T z)*riemannZeta (z+1/2))
      ((rho:ℂ)-1/2)=0 := by
    apply auxiliary_iteratedDeriv_mul_vanishing j
      ((auxRationalFactor_analytic_right k hp).mul (nativePrimeTruncationLaplace_analytic_right d T hp))
      (shiftedZeta_actual_analyticAt rho)
    intro i hi
    simp only [iteratedDeriv_comp_add_const,sub_add_cancel]
    exact auxiliary_zeta_deriv_vanishes_below rho (by omega)
  rw [hz] at hd
  exact (mul_eq_zero.mp hd).resolve_left (pow_ne_zero _ (by norm_num))

theorem nativeTruncatedResidualMoment_eq_auxiliary (k d : ℕ) (T : ℝ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) {j : ℕ}
    (hj : j<zeroMult (rho:ℂ)) :
    nativeTruncatedResidualMoment k d T ((rho:ℂ)-1/2) j=
      nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) j := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  unfold nativeTruncatedResidualMoment nativeTruncatedResidual
  simp_rw [mul_sub]
  rw [integral_sub (nativeAuxiliaryMoment_integrable k d j hp)
    (nativeAuxiliaryTruncatedMoment_integrable k d j T hk hp)]
  change nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) j-
    nativeAuxiliaryTruncatedMoment k d T ((rho:ℂ)-1/2) j=_
  rw [nativeAuxiliaryTruncatedMoment_vanishes k d T hk rho hright hj,sub_zero]


set_option backward.isDefEq.respectTransparency.types false
open Polynomial

def scaledMonicLaguerrePolynomial (n : ℕ) (a T : ℝ) : Polynomial ℝ :=
  C ((a^n)⁻¹)*(monicLaguerre n).comp (C a*(X-C T))

theorem scaledMonicLaguerrePolynomial_eval (n : ℕ) (a T t : ℝ) :
    (scaledMonicLaguerrePolynomial n a T).eval t=
      (a^n)⁻¹*(monicLaguerre n).eval (a*(t-T)) := by
  simp only [scaledMonicLaguerrePolynomial,eval_mul,eval_C,eval_comp,eval_sub,eval_X]

theorem scaledMonicLaguerrePolynomial_natDegree (n : ℕ) {a : ℝ} (ha : a≠0) (T : ℝ) :
    (scaledMonicLaguerrePolynomial n a T).natDegree=n := by
  have hL : (monicLaguerre n).natDegree=n := le_antisymm (monicLaguerre_natDegree_le n)
    (le_natDegree_of_ne_zero (by rw [monicLaguerre_top_coeff]; norm_num))
  unfold scaledMonicLaguerrePolynomial
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero n ha)),natDegree_comp,hL,
    natDegree_C_mul ha,natDegree_X_sub_C,Nat.mul_one]

theorem scaledMonicLaguerrePolynomial_topCoeff (n : ℕ) {a : ℝ} (ha : a≠0) (T : ℝ) :
    (scaledMonicLaguerrePolynomial n a T).coeff n=1 := by
  have hL : (monicLaguerre n).natDegree=n := le_antisymm (monicLaguerre_natDegree_le n)
    (le_natDegree_of_ne_zero (by rw [monicLaguerre_top_coeff]; norm_num))
  have hq : (C a*(X-C T):Polynomial ℝ).natDegree=1 := by
    rw [natDegree_C_mul ha,natDegree_X_sub_C]
  have hlead : (C a*(X-C T):Polynomial ℝ).leadingCoeff=a := by
    rw [leadingCoeff_mul,leadingCoeff_C,(monic_X_sub_C T).leadingCoeff, mul_one]
  have hcomp : ((monicLaguerre n).comp (C a*(X-C T))).coeff n=a^n := by
    have hh := coeff_comp_degree_mul_degree (p := monicLaguerre n) (q := C a*(X-C T))
      (by rw [hq]; norm_num)
    rw [hL,hq,Nat.mul_one,(monicLaguerre_monic n).leadingCoeff,hlead,one_mul] at hh
    exact hh
  rw [scaledMonicLaguerrePolynomial,coeff_C_mul,hcomp,inv_mul_cancel₀ (pow_ne_zero n ha)]

theorem polynomialMoment_eq_top (P : Polynomial ℝ) (n : ℕ) (p : ℂ) (f : ℝ → ℂ)
    (hP : P.natDegree≤n) (hc : P.coeff n=1)
    (hI : ∀ j≤n,Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-p*(t:ℂ))*f t))
    (hzero : ∀ j<n,(∫ t : ℝ,(t:ℂ)^j*Complex.exp (-p*(t:ℂ))*f t)=0) :
    (∫ t : ℝ,((P.eval t:ℝ):ℂ)*Complex.exp (-p*(t:ℂ))*f t)=
      ∫ t : ℝ,(t:ℂ)^n*Complex.exp (-p*(t:ℂ))*f t := by
  classical
  have he : (fun t : ℝ => ((P.eval t:ℝ):ℂ)*Complex.exp (-p*(t:ℂ))*f t)=
      fun (t : ℝ) => ∑ j∈Finset.range (n+1),(P.coeff j:ℂ)*
        ((t:ℂ)^j*Complex.exp (-p*(t:ℂ))*f t) := by
    funext t
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    push_cast
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,integral_finsetSum _ (fun j hj =>
    (hI j (by have h := Finset.mem_range.mp hj; omega)).const_mul (P.coeff j:ℂ))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single n]
  · rw [hc,Complex.ofReal_one,one_mul]
  · intro j hj hjn
    have hjle := Finset.mem_range.mp hj
    rw [hzero j (by omega),mul_zero]
  · simp

theorem nativeTruncatedResidualMoment_integrable (k d j : ℕ) (T : ℝ) (hk : 1≤k)
    {p : ℂ} (hp : 0<p.re) :
    Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-p*(t:ℂ))*nativeTruncatedResidual k d T t) := by
  apply (nativeCausalLaplaceMoment_integrable p hp j (nativeTruncatedResidualVector k d T)).congr
  filter_upwards [nativeTruncatedResidualVector_coe k d T hk] with t ht
  rw [ht]

theorem nativeResidual_laguerre_inner (k d : ℕ) (T : ℝ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    inner ℂ (monicLaguerreTailL2 (zeroMult (rho:ℂ)-1) ((rho:ℂ)-1/2) T (by
      simp only [Complex.sub_re]; norm_num; linarith))
      (nativeTruncatedResidualVector k d T:NativeCompletionL2)=
      nativeAuxiliaryMoment k d ((rho:ℂ)-1/2) (zeroMult (rho:ℂ)-1) := by
  let p : ℂ := (rho:ℂ)-1/2
  let n : ℕ := zeroMult (rho:ℂ)-1
  have hp : 0<p.re := by
    change 0<((rho:ℂ)-1/2).re
    simp only [Complex.sub_re]; norm_num; linarith
  have hm : 1≤zeroMult (rho:ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  let Q := scaledMonicLaguerrePolynomial n (2*p.re) T
  have ha : 2*p.re≠0 := ne_of_gt (by linarith)
  have hinner : inner ℂ (monicLaguerreTailL2 n p T hp)
      (nativeTruncatedResidualVector k d T:NativeCompletionL2)=
      ∫ t : ℝ,((Q.eval t:ℝ):ℂ)*Complex.exp (-p*(t:ℂ))*nativeTruncatedResidual k d T t := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(monicLaguerreTail_memLp n p T hp).coeFn_toLp,
      nativeTruncatedResidualVector_coe k d T hk] with t hpsi hres
    change inner ℂ (monicLaguerreTailL2 n p T hp t)
      ((nativeTruncatedResidualVector k d T:NativeCompletionL2) t)=_
    dsimp only [monicLaguerreTailL2]
    rw [hpsi,hres]
    by_cases ht : T≤t
    · have hmem : t∈Ici T := ht
      rw [monicLaguerreTail,indicator_of_mem hmem,RCLike.inner_apply']
      simp only [map_mul,Complex.conj_ofReal,←Complex.exp_conj,map_neg,starRingEnd_self_apply]
      rw [show Q.eval t=((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)) from
        scaledMonicLaguerrePolynomial_eval n (2*p.re) T t]
    · rw [nativeTruncatedResidual_zero_before k d T (lt_of_not_ge ht),inner_zero_right,mul_zero]
  have hpoly : (∫ t : ℝ,((Q.eval t:ℝ):ℂ)*Complex.exp (-p*(t:ℂ))*nativeTruncatedResidual k d T t)=
      nativeTruncatedResidualMoment k d T p n := by
    apply polynomialMoment_eq_top Q n p (nativeTruncatedResidual k d T)
      (le_of_eq (scaledMonicLaguerrePolynomial_natDegree n ha T))
      (scaledMonicLaguerrePolynomial_topCoeff n ha T)
    · intro j _
      exact nativeTruncatedResidualMoment_integrable k d j T hk hp
    · intro j hj
      change nativeTruncatedResidualMoment k d T p j=0
      rw [nativeTruncatedResidualMoment_eq_auxiliary k d T hk rho hright (by dsimp [n] at hj; omega)]
      exact nativeAuxiliaryMoment_vanishes_below k d rho hright hj
  exact hinner.trans (hpoly.trans
    (nativeTruncatedResidualMoment_eq_auxiliary k d T hk rho hright (by dsimp [n]; omega)))


def nativeMultiplicityTailConstant (d : ℕ) (rho : zetaZeroConfig.carrier) : ℝ :=
  let p : ℂ := (rho:ℂ)-1/2
  (2*p.re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
    ‖sourceFamilyLaplace d p*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
      ((zeroMult (rho:ℂ)-1).factorial:ℝ)

theorem nativeMultiplicityTailConstant_pos (d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) : 0<nativeMultiplicityTailConstant d rho := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hz := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (riemannZeta_analyticOnNhd_compl_one (rho:ℂ) rho.property.not_trivial.2)).mp
      (nativeZeroMultiplicity_order rho)).2
  have hn := norm_pos_iff.mpr
    (mul_ne_zero (sourceFamilyLaplace_ne_zero_at_right_zero d rho hright) hz)
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hn) (by positivity)

theorem nativeResidual_tail_lower_bound (k d : ℕ) (T : ℝ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
      Real.exp (((rho:ℂ)-1/2).re*T)≤
        ‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖ := by
  let p : ℂ := (rho:ℂ)-1/2
  let m := zeroMult (rho:ℂ)
  have hp : 0<p.re := by
    change 0<((rho:ℂ)-1/2).re
    simp only [Complex.sub_re]; norm_num; linarith
  have hm : 1≤m := zetaZeroConfig.one_le_mult _ rho.property
  let B : ℝ := Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2)
  rcases laguerre_tail_norm m hm p hp T with ⟨_,_,_,_,_,hpsi⟩
  change ‖monicLaguerreTailL2 (m-1) p T hp‖=B at hpsi
  have hB : 0<B := by dsimp [B]; positivity
  have hC := norm_inner_le_norm (𝕜 := ℂ) (monicLaguerreTailL2 (m-1) p T hp)
    (nativeTruncatedResidualVector k d T:NativeCompletionL2)
  rw [nativeResidual_laguerre_inner k d T hk rho hright,hpsi] at hC
  have hn : ‖nativeAuxiliaryMoment k d p (m-1)‖=
      ‖auxRationalFactor k p‖*‖sourceFamilyLaplace d p*iteratedDeriv m riemannZeta (rho:ℂ)‖ := by
    rw [nativeAuxiliaryMoment_top_value k d rho hright]
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    ring
  have hL : (2*p.re)^((m:ℝ)-1/2)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
  have hf : ((m-1).factorial:ℝ)≠0 := by positivity
  have hscale : (nativeMultiplicityTailConstant d rho*‖auxRationalFactor k p‖*
      Real.exp (p.re*T))*B=‖nativeAuxiliaryMoment k d p (m-1)‖ := by
    rw [hn]
    change (((2*p.re)^((m:ℝ)-1/2)*
      ‖sourceFamilyLaplace d p*iteratedDeriv m riemannZeta (rho:ℂ)‖/((m-1).factorial:ℝ))*
        ‖auxRationalFactor k p‖*Real.exp (p.re*T))*
          (Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2))=_
    rw [show -p.re*T=-(p.re*T) by ring,Real.exp_neg]
    field_simp [hL,hf,Real.exp_ne_zero]
  apply (mul_le_mul_iff_of_pos_left hB).mp
  calc
    B*(nativeMultiplicityTailConstant d rho*‖auxRationalFactor k p‖*Real.exp (p.re*T))=
        ‖nativeAuxiliaryMoment k d p (m-1)‖ := (mul_comm _ _).trans hscale
    _ ≤ B*‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖ := hC

/-- The literal finite-history residual has genuine L2 membership and tail
support, and its norm satisfies the paper constant for every multiplicity.
The source's global square-integrability is not a premise. -/
theorem native_auxiliary_tail_residual_lower (k d : ℕ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) (T : ℝ) :
    0<nativeMultiplicityTailConstant d rho ∧
    MemLp (nativeTruncatedResidual k d T) 2 volume ∧
    (nativeTruncatedResidualVector k d T:NativeCompletionL2)=ᵐ[volume] nativeTruncatedResidual k d T ∧
    (∀ t<T,nativeTruncatedResidual k d T t=0) ∧
    nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
      Real.exp (((rho:ℂ)-1/2).re*T)≤
        ‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖ :=
  ⟨nativeMultiplicityTailConstant_pos d rho hright,nativeTruncatedResidual_memLp_two k d T hk,
    nativeTruncatedResidualVector_coe k d T hk,
    fun _ ht => nativeTruncatedResidual_zero_before k d T ht,
    nativeResidual_tail_lower_bound k d T hk rho hright⟩


def nativeTailRestriction (T : ℝ) (f : NativeCompletionL2) : NativeCompletionL2 :=
  (MemLp.indicator measurableSet_Ici (Lp.memLp f)).toLp ((Ici T).indicator f)

theorem nativeTailRestriction_coe (T : ℝ) (f : NativeCompletionL2) :
    nativeTailRestriction T f=ᵐ[volume] (Ici T).indicator f :=
  (MemLp.indicator measurableSet_Ici (Lp.memLp f)).coeFn_toLp

theorem nativeTailRestriction_norm_le (T : ℝ) (f : NativeCompletionL2) :
    ‖nativeTailRestriction T f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [nativeTailRestriction_coe T f] with t ht
  rw [ht]
  by_cases hmem : t∈Ici T
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem,norm_zero]
    exact norm_nonneg _

theorem tailMemory_nonneg (alpha : ℝ) (d : ℕ) (T : ℝ) : 0≤tailMemory alpha d T :=
  integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)

theorem nativeAuxiliaryTruncatedImage_memory_bound (k d : ℕ) (T t : ℝ) (hk : 1≤k) :
    ‖nativeAuxiliaryTruncatedImage k d T t‖≤auxCompletionBound k*
      Real.exp (-auxCompletionAlpha k*(t-T))*tailMemory (auxCompletionAlpha k) d T := by
  let A := auxCompletionBound k
  let a := auxCompletionAlpha k
  let C := A*Real.exp (-a*(t-T))
  have hA : 0<A := auxCompletionBound_pos k hk
  have he : nativeAuxiliaryTruncatedImage k d T t=
      ∫ u : ℝ in Icc 0 T,(auxCompletionKernel k (t-u):ℂ)*(primeFieldFamily d u:ℂ) := by
    unfold nativeAuxiliaryTruncatedImage
    calc
      (∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(nativePrimeTruncation d T (t-s):ℂ))=
          ∫ u : ℝ,(auxCompletionKernel k (t-u):ℂ)*(nativePrimeTruncation d T u:ℂ) := by
        have hh := integral_sub_left_eq_self
          (fun s : ℝ => (auxCompletionKernel k s:ℂ)*(nativePrimeTruncation d T (t-s):ℂ)) volume t
        have hsub (u : ℝ) : t-(t-u)=u := by ring
        simpa only [hsub] using hh.symm
      _ = _ := by
        rw [←integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with u
        by_cases hu : u∈Icc (0:ℝ) T
        · rw [nativePrimeTruncation,indicator_of_mem hu,indicator_of_mem hu]
        · rw [nativePrimeTruncation,indicator_of_notMem hu,Complex.ofReal_zero,mul_zero,indicator_of_notMem hu]
  let dom : ℝ → ℝ := fun u => C*(Real.exp (-a*(T-u))*|primeFieldFamily d u|)
  have hdomc : Continuous dom := continuous_const.mul
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-a*(T-u)))).mul
      (primeFieldFamily_contDiff d).continuous.abs)
  have hdom : IntegrableOn dom (Icc 0 T) :=
    hdomc.integrableOn_Icc
  have hb (u : ℝ) : ‖(auxCompletionKernel k (t-u):ℂ)*(primeFieldFamily d u:ℂ)‖≤dom u := by
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_right ((aux_completion_uniform_decay k hk).2 (t-u)) (abs_nonneg _)).trans_eq
    have hexp : Real.exp (-a*(t-u))=Real.exp (-a*(t-T))*Real.exp (-a*(T-u)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    change A*Real.exp (-a*(t-u))*|primeFieldFamily d u|=dom u
    rw [hexp]
    dsimp [dom,C]
    ring
  have hm : AEStronglyMeasurable (fun u : ℝ =>
      (auxCompletionKernel k (t-u):ℂ)*(primeFieldFamily d u:ℂ)) (volume.restrict (Icc 0 T)) :=
    ((auxCompletionKernel_measurable k).complex_ofReal.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.restrict.mul
        (Complex.continuous_ofReal.comp (primeFieldFamily_contDiff d).continuous).aestronglyMeasurable.restrict
  have hi : IntegrableOn (fun u : ℝ => (auxCompletionKernel k (t-u):ℂ)*(primeFieldFamily d u:ℂ))
      (Icc 0 T) := hdom.mono' hm (Eventually.of_forall hb)
  rw [he]
  calc
    _ ≤ ∫ u : ℝ in Icc 0 T,‖(auxCompletionKernel k (t-u):ℂ)*(primeFieldFamily d u:ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Icc 0 T,dom u := integral_mono hi.norm hdom hb
    _ = _ := by rw [show dom=(fun u : ℝ => C*(Real.exp (-a*(T-u))*|primeFieldFamily d u|)) from rfl,
      integral_const_mul]; rfl

def nativeTailExponentialVector (a T c : ℝ) (ha : 0<a) : NativeCompletionL2 :=
  ((c*Real.exp (a*T):ℝ):ℂ) • monicLaguerreTailL2 0 (a:ℂ) T ha

theorem nativeTailExponentialVector_coe (a T c : ℝ) (ha : 0<a) :
    nativeTailExponentialVector a T c ha=ᵐ[volume]
      (Ici T).indicator (fun t : ℝ => ((c*Real.exp (-a*(t-T)):ℝ):ℂ)) := by
  filter_upwards [Lp.coeFn_smul ((c*Real.exp (a*T):ℝ):ℂ)
    (monicLaguerreTailL2 0 (a:ℂ) T ha),
    (monicLaguerreTail_memLp 0 (a:ℂ) T ha).coeFn_toLp] with t hsmul hpsi
  change (((c*Real.exp (a*T):ℝ):ℂ) • monicLaguerreTailL2 0 (a:ℂ) T ha) t=_
  rw [hsmul,Pi.smul_apply,smul_eq_mul]
  dsimp only [monicLaguerreTailL2]
  rw [hpsi]
  by_cases ht : t∈Ici T
  · rw [monicLaguerreTail,indicator_of_mem ht,indicator_of_mem ht]
    have hr : c*Real.exp (a*T)*Real.exp (-a*t)=c*Real.exp (-a*(t-T)) := by
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    simpa [monicLaguerre,Complex.ofReal_exp] using congrArg Complex.ofReal hr
  · rw [monicLaguerreTail,indicator_of_notMem ht,indicator_of_notMem ht,mul_zero]

theorem nativeTailExponentialVector_norm (a T c : ℝ) (ha : 0<a) (hc : 0≤c) :
    ‖nativeTailExponentialVector a T c ha‖=c/Real.sqrt (2*a) := by
  rcases laguerre_tail_norm 1 (by omega) (a:ℂ) ha T with ⟨_,_,_,_,_,hpsi⟩
  norm_num only [Nat.cast_one,Nat.sub_self,Nat.factorial_zero,Complex.ofReal_re,mul_one] at hpsi
  rw [nativeTailExponentialVector,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hc (Real.exp_nonneg _)),hpsi]
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
  rw [Real.rpow_one_half,show -a*T=-(a*T) by ring,Real.exp_neg]
  have hs : Real.sqrt (2*a)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  field_simp [hs,Real.exp_ne_zero] <;> ring

#print axioms nativeAuxiliaryTruncatedImage_memory_bound
#print axioms nativeTailExponentialVector_norm

end Zeta23.OPICAFollowup
