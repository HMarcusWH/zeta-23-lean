import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Zeta23.OPICARound2.ClassicalAdapter
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Fourier.Convolution
import Zeta23.OPICAFollowup.LogFourierSobolev
import Zeta23.OPICAFollowup.NativeFilters
import Zeta23.OPICARound2.CausalProbe
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A generic positive-kernel countermodel. None of these kernels is identified
with the native arithmetic floor kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate Convolution

namespace Zeta23.OPICARound2

def syntheticExponential (t : ℝ) : ℝ := if 0≤t then Real.exp (-t) else 0

def syntheticMinusKernel (t : ℝ) : ℝ :=
  (syntheticExponential t+(3/2)*syntheticExponential (t-1))/4

def syntheticPlusKernel (t : ℝ) : ℝ :=
  ((3/2)*syntheticExponential t+syntheticExponential (t-1))/4

theorem synthetic_exponential_nonneg (t : ℝ) : 0≤syntheticExponential t := by
  unfold syntheticExponential
  split_ifs <;> positivity

theorem synthetic_exponential_integrable : Integrable syntheticExponential := by
  have he : syntheticExponential=(Ici (0:ℝ)).indicator (fun t : ℝ => Real.exp (-t)) := by
    ext t
    simp [syntheticExponential,indicator_apply]
  rw [he]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)

theorem synthetic_exponential_integral : (∫ t : ℝ,syntheticExponential t)=1 := by
  have he : syntheticExponential=(Ici (0:ℝ)).indicator (fun t : ℝ => Real.exp (-t)) := by
    ext t
    simp [syntheticExponential,indicator_apply]
  rw [he,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  simpa using integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)

theorem synthetic_exponential_zero_negative (t : ℝ) (ht : t<0) :
    syntheticExponential t=0 := by simp [syntheticExponential,not_le.mpr ht]

theorem synthetic_twins_nonneg (t : ℝ) :
    0≤syntheticMinusKernel t ∧ 0≤syntheticPlusKernel t := by
  unfold syntheticMinusKernel syntheticPlusKernel
  constructor <;> positivity [synthetic_exponential_nonneg t,synthetic_exponential_nonneg (t-1)]

theorem synthetic_minus_integrable : Integrable syntheticMinusKernel :=
  (synthetic_exponential_integrable.add
    ((synthetic_exponential_integrable.comp_sub_right 1).const_mul (3/2))).div_const 4

theorem synthetic_plus_integrable : Integrable syntheticPlusKernel :=
  ((synthetic_exponential_integrable.const_mul (3/2)).add
    (synthetic_exponential_integrable.comp_sub_right 1)).div_const 4

theorem synthetic_twins_mass :
    (∫ t : ℝ,syntheticMinusKernel t)=(5/8:ℝ) ∧
    (∫ t : ℝ,syntheticPlusKernel t)=(5/8:ℝ) := by
  have hs : (∫ t : ℝ,syntheticExponential (t-1))=1 :=
    (integral_sub_right_eq_self syntheticExponential 1 (μ:=(volume:Measure ℝ))).trans
      synthetic_exponential_integral
  constructor
  · rw [show syntheticMinusKernel=(fun t =>
      (syntheticExponential t+(3/2)*syntheticExponential (t-1))/4) from rfl,
      integral_div,integral_add synthetic_exponential_integrable
        ((synthetic_exponential_integrable.comp_sub_right 1).const_mul (3/2)),
      integral_const_mul,synthetic_exponential_integral,hs]
    norm_num
  · rw [show syntheticPlusKernel=(fun t =>
      ((3/2)*syntheticExponential t+syntheticExponential (t-1))/4) from rfl,
      integral_div,integral_add (synthetic_exponential_integrable.const_mul (3/2))
        (synthetic_exponential_integrable.comp_sub_right 1),
      integral_const_mul,synthetic_exponential_integral,hs]
    norm_num

theorem synthetic_minus_zero_negative (t : ℝ) (ht : t<0) :
    syntheticMinusKernel t=0 := by
  rw [syntheticMinusKernel,synthetic_exponential_zero_negative t ht,
    synthetic_exponential_zero_negative (t-1) (by linarith)]
  norm_num

theorem synthetic_plus_zero_negative (t : ℝ) (ht : t<0) :
    syntheticPlusKernel t=0 := by
  rw [syntheticPlusKernel,synthetic_exponential_zero_negative t ht,
    synthetic_exponential_zero_negative (t-1) (by linarith)]
  norm_num

theorem synthetic_twins_dominating_exponential (t : ℝ) :
    syntheticMinusKernel t≤Real.exp (-t/2) ∧ syntheticPlusKernel t≤Real.exp (-t/2) := by
  have hhalf : (3/2:ℝ)<Real.exp (1/2) := by
    have he : Real.exp (1/2)^2=Real.exp 1 := by
      rw [pow_two,←Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_gt_d9,Real.exp_pos (1/2)]
  by_cases ht : t<0
  · rw [synthetic_minus_zero_negative t ht,synthetic_plus_zero_negative t ht]
    exact ⟨(Real.exp_pos _).le,(Real.exp_pos _).le⟩
  have ht0 : 0≤t := le_of_not_gt ht
  by_cases ht1 : t<1
  · rw [syntheticMinusKernel,syntheticPlusKernel,
      synthetic_exponential_zero_negative (t-1) (by linarith)]
    have he : syntheticExponential t=Real.exp (-t) := by simp [syntheticExponential,ht0]
    rw [he]
    have hb : Real.exp (-t)≤Real.exp (-t/2) := Real.exp_le_exp.mpr (by linarith)
    constructor <;> nlinarith [Real.exp_pos (-t)]
  · have ht1' : 1≤t := le_of_not_gt ht1
    have hshift : Real.exp (-(t-1))=Real.exp 1*Real.exp (-t) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have he : syntheticExponential t=Real.exp (-t) := by simp [syntheticExponential,ht0]
    have he1 : syntheticExponential (t-1)=Real.exp (-(t-1)) := by
      simp [syntheticExponential,show 0≤t-1 by linarith]
    have hmajor : (3/2:ℝ)≤Real.exp (t/2) := hhalf.le.trans
      (Real.exp_le_exp.mpr (by linarith))
    have hminus : ((1:ℝ)+(3/2)*Real.exp 1)/4≤Real.exp (t/2) := by
      linarith [Real.exp_one_lt_three]
    have hplus : ((3/2:ℝ)+Real.exp 1)/4≤Real.exp (t/2) := by
      linarith [Real.exp_one_lt_three]
    have hprod : Real.exp (t/2)*Real.exp (-t)=Real.exp (-t/2) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [syntheticMinusKernel,syntheticPlusKernel,he,he1,hshift]
    constructor
    · calc
        _ = ((1+(3/2)*Real.exp 1)/4)*Real.exp (-t) := by ring
        _ ≤ Real.exp (t/2)*Real.exp (-t) := mul_le_mul_of_nonneg_right hminus (Real.exp_nonneg _)
        _ = _ := hprod
    · calc
        _ = (((3/2)+Real.exp 1)/4)*Real.exp (-t) := by ring
        _ ≤ Real.exp (t/2)*Real.exp (-t) := mul_le_mul_of_nonneg_right hplus (Real.exp_nonneg _)
        _ = _ := hprod

def syntheticE : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator syntheticExponential synthetic_exponential_integrable
    synthetic_exponential_zero_negative

def syntheticMinusOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator syntheticMinusKernel synthetic_minus_integrable synthetic_minus_zero_negative

def syntheticPlusOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator syntheticPlusKernel synthetic_plus_integrable synthetic_plus_zero_negative

theorem synthetic_twins_contractions :
    ‖syntheticMinusOperator‖≤(5/8:ℝ) ∧ ‖syntheticPlusOperator‖≤(5/8:ℝ) := by
  constructor
  · have hn : (∫ t : ℝ,‖syntheticMinusKernel t‖)=(5/8:ℝ) := by
      simp_rw [Real.norm_of_nonneg (synthetic_twins_nonneg _).1]
      exact synthetic_twins_mass.1
    exact (causalKernelOperator_norm_le syntheticMinusKernel synthetic_minus_integrable
      synthetic_minus_zero_negative).trans_eq hn
  · have hn : (∫ t : ℝ,‖syntheticPlusKernel t‖)=(5/8:ℝ) := by
      simp_rw [Real.norm_of_nonneg (synthetic_twins_nonneg _).2]
      exact synthetic_twins_mass.2
    exact (causalKernelOperator_norm_le syntheticPlusKernel synthetic_plus_integrable
      synthetic_plus_zero_negative).trans_eq hn

def syntheticMinusMultiplier (z : ℂ) : ℂ :=
  (1+(3/2)*Complex.exp (-z))/(4*(z+1))
def syntheticPlusMultiplier (z : ℂ) : ℂ :=
  ((3/2)+Complex.exp (-z))/(4*(z+1))

theorem synthetic_delay_add (s t : ℝ) (f : ProbeL2) :
    CCM.nativeCompletionL2Delay s (CCM.nativeCompletionL2Delay t f)=
      CCM.nativeCompletionL2Delay (s+t) f := by
  apply Lp.ext
  have hs := (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq
    (CCM.nativeCompletionL2Delay_coeFn t f)
  filter_upwards [CCM.nativeCompletionL2Delay_coeFn s (CCM.nativeCompletionL2Delay t f),
    CCM.nativeCompletionL2Delay_coeFn (s+t) f,hs] with x hx hy hst
  dsimp only [Function.comp_def] at hst
  rw [hx,hy,hst]
  congr 1
  ring

theorem synthetic_shifted_kernel_value (f : ProbeL2) :
    kernelL2Operator (fun t => syntheticExponential (t-1))
      (synthetic_exponential_integrable.comp_sub_right 1) f =
    CCM.nativeCompletionL2Delay 1 (kernelL2Operator syntheticExponential
      synthetic_exponential_integrable f) := by
  rw [kernelL2Operator_apply,kernelL2Operator_apply,
    ←(CCM.nativeCompletionL2Delay 1).integral_comp_comm]
  have hpoint (t : ℝ) : syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t f=
      (fun s : ℝ => CCM.nativeCompletionL2Delay 1
        (syntheticExponential s • CCM.nativeCompletionL2Delay s f)) (t-1) := by
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,synthetic_delay_add]
    congr 2
    ring
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  exact integral_sub_right_eq_self
    (fun s : ℝ => CCM.nativeCompletionL2Delay 1
      (syntheticExponential s • CCM.nativeCompletionL2Delay s f)) 1 (μ:=(volume:Measure ℝ))

theorem synthetic_twins_operator_formulas (f : CausalProbeL2) :
    syntheticMinusOperator f=(1/4:ℝ) •
      (syntheticE f+(3/2:ℝ) • probeDelay 1 (by norm_num) (syntheticE f)) ∧
    syntheticPlusOperator f=(1/4:ℝ) •
      ((3/2:ℝ) • syntheticE f+probeDelay 1 (by norm_num) (syntheticE f)) := by
  have hE := kernelL2Integrand_integrable syntheticExponential synthetic_exponential_integrable (f:ProbeL2)
  have hD := kernelL2Integrand_integrable (fun t => syntheticExponential (t-1))
    (synthetic_exponential_integrable.comp_sub_right 1) (f:ProbeL2)
  change Integrable (fun t : ℝ => syntheticExponential t • CCM.nativeCompletionL2Delay t (f:ProbeL2)) at hE
  change Integrable (fun t : ℝ => syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t (f:ProbeL2)) at hD
  have hEr : Integrable (fun t : ℝ => (3/2:ℝ) •
      (syntheticExponential t • CCM.nativeCompletionL2Delay t (f:ProbeL2))) :=
    Integrable.smul (3/2:ℝ) hE
  have hDr : Integrable (fun t : ℝ => (3/2:ℝ) •
      (syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t (f:ProbeL2))) :=
    Integrable.smul (3/2:ℝ) hD
  have hminus : kernelL2Operator syntheticMinusKernel synthetic_minus_integrable (f:ProbeL2)=
      (1/4:ℝ) • (kernelL2Operator syntheticExponential synthetic_exponential_integrable (f:ProbeL2)+
        (3/2:ℝ) • kernelL2Operator (fun t => syntheticExponential (t-1))
          (synthetic_exponential_integrable.comp_sub_right 1) (f:ProbeL2)) := by
    simp only [kernelL2Operator_apply]
    have hp (t : ℝ) : syntheticMinusKernel t • CCM.nativeCompletionL2Delay t (f:ProbeL2)=
        (1/4:ℝ) • (syntheticExponential t • CCM.nativeCompletionL2Delay t (f:ProbeL2)+
          (3/2:ℝ) • (syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t (f:ProbeL2))) := by
      rw [syntheticMinusKernel]
      module
    rw [integral_congr_ae (Eventually.of_forall hp),integral_smul,
      integral_add hE hDr,integral_smul]
  have hplus : kernelL2Operator syntheticPlusKernel synthetic_plus_integrable (f:ProbeL2)=
      (1/4:ℝ) • ((3/2:ℝ) • kernelL2Operator syntheticExponential synthetic_exponential_integrable (f:ProbeL2)+
        kernelL2Operator (fun t => syntheticExponential (t-1))
          (synthetic_exponential_integrable.comp_sub_right 1) (f:ProbeL2)) := by
    simp only [kernelL2Operator_apply]
    have hp (t : ℝ) : syntheticPlusKernel t • CCM.nativeCompletionL2Delay t (f:ProbeL2)=
        (1/4:ℝ) • ((3/2:ℝ) • (syntheticExponential t • CCM.nativeCompletionL2Delay t (f:ProbeL2))+
          syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t (f:ProbeL2)) := by
      rw [syntheticPlusKernel]
      module
    rw [integral_congr_ae (Eventually.of_forall hp),integral_smul,
      integral_add hEr hD,integral_smul]
  rw [synthetic_shifted_kernel_value] at hminus hplus
  constructor
  · apply Subtype.ext
    exact hminus
  · apply Subtype.ext
    exact hplus

theorem synthetic_twins_equal_norm (f : CausalProbeL2) :
    ‖syntheticMinusOperator f‖=‖syntheticPlusOperator f‖ := by
  rw [(synthetic_twins_operator_formulas f).1,(synthetic_twins_operator_formulas f).2,
    norm_smul,norm_smul]
  apply congrArg (fun s : ℝ => ‖(1/4:ℝ)‖*s)
  let u := syntheticE f
  let v := probeDelay 1 (by norm_num) u
  have hnorm : ‖v‖=‖u‖ := probeDelay_norm 1 (by norm_num) u
  have h1 := @norm_add_sq ℂ CausalProbeL2 _ _ _ u ((3/2:ℂ) • v)
  have h2 := @norm_add_sq ℂ CausalProbeL2 _ _ _ ((3/2:ℂ) • u) v
  rw [inner_smul_right (𝕜:=ℂ) u v (3/2:ℂ)] at h1
  rw [inner_smul_left (𝕜:=ℂ) u v (3/2:ℂ)] at h2
  have hconj : starRingEnd ℂ (3/2:ℂ)=(3/2:ℂ) := by
    change star (3/2:ℂ)=(3/2:ℂ)
    norm_num
  rw [hconj] at h2
  simp only [norm_smul] at h1 h2
  norm_num [Complex.mul_re,Complex.mul_im] at h1 h2
  have he : ‖u+(3/2:ℂ) • v‖=‖(3/2:ℂ) • u+v‖ := by
    change ‖(u:ProbeL2)+(3/2:ℂ) • (v:ProbeL2)‖=‖(3/2:ℂ) • (u:ProbeL2)+(v:ProbeL2)‖
    change ‖(v:ProbeL2)‖=‖(u:ProbeL2)‖ at hnorm
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      _ = ‖(u:ProbeL2)‖^2+2*((3/2)*(inner ℂ (u:ProbeL2) (v:ProbeL2)).re)+((3/2)*‖(v:ProbeL2)‖)^2 := h1
      _ = ((3/2)*‖(u:ProbeL2)‖)^2+2*((3/2)*(inner ℂ (u:ProbeL2) (v:ProbeL2)).re)+‖(v:ProbeL2)‖^2 := by rw [hnorm]; ring
      _ = _ := h2.symm
  simpa [u,v,RCLike.real_smul_eq_coe_smul (K:=ℂ)] using he
theorem synthetic_twins_equal_power :
    (ContinuousLinearMap.adjoint syntheticMinusOperator).comp syntheticMinusOperator=
      (ContinuousLinearMap.adjoint syntheticPlusOperator).comp syntheticPlusOperator := by
  have hlin : ((ContinuousLinearMap.adjoint syntheticMinusOperator).comp syntheticMinusOperator).toLinearMap=
      ((ContinuousLinearMap.adjoint syntheticPlusOperator).comp syntheticPlusOperator).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro f
    change inner ℂ ((ContinuousLinearMap.adjoint syntheticMinusOperator) (syntheticMinusOperator f)) f=
      inner ℂ ((ContinuousLinearMap.adjoint syntheticPlusOperator) (syntheticPlusOperator f)) f
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,synthetic_twins_equal_norm]
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : CausalProbeL2→ₗ[ℂ] CausalProbeL2 => T f) hlin



theorem synthetic_exponential_laplace {z : ℂ} (hz : 0≤z.re) :
    probeLaplace (fun t => (syntheticExponential t:ℂ)) z=1/(z+1) := by
  have hp (t : ℝ) : (syntheticExponential t:ℂ)=
      OPICAFollowup.NativeCausalL1Kernel.exponential 1 (by norm_num) t := by
    simp only [syntheticExponential,OPICAFollowup.NativeCausalL1Kernel.exponential]
    split_ifs <;> simp [Complex.ofReal_exp]
  simpa only [probeLaplace,hp,OPICAFollowup.NativeCausalL1Kernel.laplace,Complex.ofReal_one] using
    OPICAFollowup.NativeCausalL1Kernel.exponential_laplace 1 (by norm_num) hz

theorem synthetic_shift_laplace {z : ℂ} (hz : 0≤z.re) :
    probeLaplace (fun t => (syntheticExponential (t-1):ℂ)) z=
      Complex.exp (-z)/(z+1) := by
  have he (t : ℝ) : Complex.exp (-z*(t:ℂ))*(syntheticExponential (t-1):ℂ)=
      (Complex.exp (-z)* (Complex.exp (-z*((t-1:ℝ):ℂ))*
        (syntheticExponential (t-1):ℂ))) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold probeLaplace
  rw [integral_congr_ae (Eventually.of_forall he),integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(syntheticExponential t:ℂ)) (1:ℝ)]
  change Complex.exp (-z)*probeLaplace (fun t => (syntheticExponential t:ℂ)) z=_
  rw [synthetic_exponential_laplace hz]
  ring

theorem synthetic_twins_laplace {z : ℂ} (hz : 0≤z.re) :
    probeLaplace (fun t => (syntheticMinusKernel t:ℂ)) z=syntheticMinusMultiplier z ∧
    probeLaplace (fun t => (syntheticPlusKernel t:ℂ)) z=syntheticPlusMultiplier z := by
  have hi := CCM.nativeCausalComplexDamping_integrable hz
    synthetic_exponential_integrable synthetic_exponential_zero_negative
  have his := CCM.nativeCausalComplexDamping_integrable hz
    (synthetic_exponential_integrable.comp_sub_right 1)
    (fun t ht => synthetic_exponential_zero_negative (t-1) (by linarith))
  change Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(syntheticExponential t:ℂ)) at hi
  change Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(syntheticExponential (t-1):ℂ)) at his
  have hden : z+1≠0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hm : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(syntheticMinusKernel t:ℂ))=
      fun t : ℝ => (Complex.exp (-z*(t:ℂ))*(syntheticExponential t:ℂ)+
        (3/2:ℂ)*(Complex.exp (-z*(t:ℂ))*(syntheticExponential (t-1):ℂ)))/4 := by
    funext t
    simp only [syntheticMinusKernel]
    push_cast
    ring
  have hp : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(syntheticPlusKernel t:ℂ))=
      fun t : ℝ => ((3/2:ℂ)*(Complex.exp (-z*(t:ℂ))*(syntheticExponential t:ℂ))+
        Complex.exp (-z*(t:ℂ))*(syntheticExponential (t-1):ℂ))/4 := by
    funext t
    simp only [syntheticPlusKernel]
    push_cast
    ring
  constructor
  · unfold probeLaplace
    rw [hm,integral_div,integral_add hi (his.const_mul _),integral_const_mul]
    change (probeLaplace (fun t => (syntheticExponential t:ℂ)) z+
      (3/2:ℂ)*probeLaplace (fun t => (syntheticExponential (t-1):ℂ)) z)/4=_
    rw [synthetic_exponential_laplace hz,synthetic_shift_laplace hz]
    simp only [syntheticMinusMultiplier]
    field_simp
    <;> ring
  · unfold probeLaplace
    rw [hp,integral_div,integral_add (hi.const_mul _) his,integral_const_mul]
    change ((3/2:ℂ)*probeLaplace (fun t => (syntheticExponential t:ℂ)) z+
      probeLaplace (fun t => (syntheticExponential (t-1):ℂ)) z)/4=_
    rw [synthetic_exponential_laplace hz,synthetic_shift_laplace hz]
    simp only [syntheticPlusMultiplier]
    field_simp
    <;> ring

def syntheticRightZero (k : ℤ) : ℂ :=
  (Real.log (3/2):ℂ)+(2*(k:ℂ)+1)*Real.pi*Complex.I

theorem synthetic_right_zero_re (k : ℤ) :
    (syntheticRightZero k).re=Real.log (3/2) := by
  simp [syntheticRightZero,Complex.mul_re,Complex.mul_im]

theorem synthetic_right_zero_positive (k : ℤ) : 0<(syntheticRightZero k).re := by
  rw [synthetic_right_zero_re]
  exact Real.log_pos (by norm_num)

theorem synthetic_right_zero_exp (k : ℤ) :
    Complex.exp (-(syntheticRightZero k))=-(2/3:ℂ) := by
  have hphase : Complex.exp (-((2*(k:ℂ)+1)*Real.pi*Complex.I))=-1 := by
    rw [show -((2*(k:ℂ)+1)*Real.pi*Complex.I)=
      (-2*(k:ℂ))*Real.pi*Complex.I+(-Real.pi*Complex.I) by ring,
      Complex.exp_add]
    have hper : Complex.exp ((-2*(k:ℂ))*Real.pi*Complex.I)=1 := by
      rw [show (-2*(k:ℂ))*Real.pi*Complex.I=
        (-(k:ℂ))*(2*Real.pi*Complex.I) by ring]
      simpa only [Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-k)
    rw [hper,one_mul,show -↑Real.pi*Complex.I=-(↑Real.pi*Complex.I) by ring,Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  simp only [syntheticRightZero,neg_add,Complex.exp_add]
  rw [hphase,Complex.exp_neg,← Complex.ofReal_exp,Real.exp_log (by norm_num : (0:ℝ)<3/2)]
  norm_num

theorem synthetic_minus_right_zeros (k : ℤ) :
    syntheticMinusMultiplier (syntheticRightZero k)=0 := by
  simp [syntheticMinusMultiplier,synthetic_right_zero_exp]

theorem synthetic_minus_range_annihilated (k : ℤ) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment (syntheticRightZero k) 0
      (syntheticMinusOperator f:ProbeL2)=0 := by
  rw [syntheticMinusOperator,
    causalKernelOperator_laplace _ synthetic_minus_integrable
      synthetic_minus_zero_negative _
      (synthetic_right_zero_positive k),
    (synthetic_twins_laplace (synthetic_right_zero_positive k).le).1,
    synthetic_minus_right_zeros,zero_mul]

theorem synthetic_boundary_power (xi : ℝ) :
    ‖syntheticMinusMultiplier ((xi:ℂ)*Complex.I)‖^2=
      (13+12*Real.cos xi)/(64*(1+xi^2)) ∧
    ‖syntheticPlusMultiplier ((xi:ℂ)*Complex.I)‖^2=
      (13+12*Real.cos xi)/(64*(1+xi^2)) := by
  have heR : (Complex.exp (-((xi:ℂ)*Complex.I))).re=Real.cos xi := by
    simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have heI : (Complex.exp (-((xi:ℂ)*Complex.I))).im= -Real.sin xi := by
    simp [Complex.exp_im,Complex.mul_re,Complex.mul_im]
  have hn1 : Complex.normSq (1+(3/2:ℂ)*Complex.exp (-((xi:ℂ)*Complex.I)))=
      (13/4:ℝ)+3*Real.cos xi := by
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,heR,heI]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq xi]
  have hn2 : Complex.normSq ((3/2:ℂ)+Complex.exp (-((xi:ℂ)*Complex.I)))=
      (13/4:ℝ)+3*Real.cos xi := by
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,heR,heI]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq xi]
  have hd : Complex.normSq (4*((xi:ℂ)*Complex.I+1))=16*(1+xi^2) := by
    simp [Complex.normSq_mul,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    <;> ring
  constructor
  · rw [syntheticMinusMultiplier,Complex.sq_norm,Complex.normSq_div,hn1,hd]
    field_simp
    <;> ring
  · rw [syntheticPlusMultiplier,Complex.sq_norm,Complex.normSq_div,hn2,hd]
    field_simp
    <;> ring




theorem synthetic_exponential_measurable : Measurable syntheticExponential := by
  unfold syntheticExponential
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem synthetic_exponential_memLp : MemLp (fun t : ℝ => (syntheticExponential t:ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (syntheticExponential t:ℂ)) volume :=
    synthetic_exponential_measurable.complex_ofReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply synthetic_exponential_integrable.norm.mono' (hm.norm.pow 2)
  filter_upwards with t
  change ‖‖(syntheticExponential t:ℂ)‖^2‖≤‖syntheticExponential t‖
  rw [Real.norm_of_nonneg (sq_nonneg _),Complex.norm_real,Real.norm_eq_abs]
  have hbound : |syntheticExponential t|≤1 := by
    unfold syntheticExponential
    split_ifs with ht
    · rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith)
    · norm_num
  nlinarith [abs_nonneg (syntheticExponential t)]

def syntheticDoubleKernel (t : ℝ) : ℝ := 2*syntheticExponential t
theorem syntheticDoubleKernel_integrable : Integrable syntheticDoubleKernel :=
  synthetic_exponential_integrable.const_mul 2
theorem syntheticDoubleKernel_measurable : Measurable syntheticDoubleKernel :=
  synthetic_exponential_measurable.const_mul 2
theorem syntheticDoubleKernel_memLp : MemLp (fun t : ℝ => (syntheticDoubleKernel t:ℂ)) 2 volume := by
  convert synthetic_exponential_memLp.const_mul (2:ℂ) using 1
  ext t
  simp [syntheticDoubleKernel]
def syntheticAllPassMultiplier (z : ℂ) : ℂ := (z-1)/(z+1)
def syntheticAllPassOperator : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  ContinuousLinearMap.id ℂ CausalProbeL2-
    causalKernelOperator syntheticDoubleKernel syntheticDoubleKernel_integrable
      (by intro t ht; simp [syntheticDoubleKernel,synthetic_exponential_zero_negative t ht])

theorem syntheticAllPassMultiplier_boundary_norm (tau : ℝ) :
    ‖syntheticAllPassMultiplier ((tau:ℂ)*Complex.I)‖=1 := by
  unfold syntheticAllPassMultiplier
  rw [norm_div]
  have he : ‖(tau:ℂ)*Complex.I-1‖=‖(tau:ℂ)*Complex.I+1‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  rw [he,div_self]
  apply norm_ne_zero_iff.mpr
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem syntheticDoubleKernel_laplace (z : ℂ) (hz : 0≤z.re) :
    probeLaplace (fun t => (syntheticDoubleKernel t:ℂ)) z=2/(z+1) := by
  have hp (t : ℝ) : (syntheticDoubleKernel t:ℂ)=
      2*OPICAFollowup.NativeCausalL1Kernel.exponential 1 (by norm_num) t := by
    simp only [syntheticDoubleKernel,syntheticExponential,
      OPICAFollowup.NativeCausalL1Kernel.exponential]
    split_ifs <;> simp [Complex.ofReal_exp]
  unfold probeLaplace
  simp_rw [hp,mul_left_comm _ (2:ℂ)]
  rw [integral_const_mul]
  change 2*(OPICAFollowup.NativeCausalL1Kernel.exponential 1 (by norm_num)).laplace z=_
  rw [OPICAFollowup.NativeCausalL1Kernel.exponential_laplace 1 (by norm_num) hz]
  push_cast
  ring

def syntheticFullAllPassOperator : ProbeL2 →L[ℂ] ProbeL2 :=
  ContinuousLinearMap.id ℂ ProbeL2 -
    kernelL2Operator syntheticDoubleKernel syntheticDoubleKernel_integrable

def syntheticFullAllPassPhysical (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t - ∫ s : ℝ, (syntheticDoubleKernel s : ℂ) * f (t - s)

theorem syntheticFullAllPassPhysical_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (syntheticFullAllPassPhysical f) :=
  hf.sub (syntheticDoubleKernel_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hf)

theorem syntheticFullAllPassOperator_coeFn (f : ProbeL2) :
    syntheticFullAllPassOperator f =ᵐ[volume] syntheticFullAllPassPhysical f := by
  have hk := kernelL2Operator_coeFn_pointwise syntheticDoubleKernel syntheticDoubleKernel_integrable
    syntheticDoubleKernel_measurable syntheticDoubleKernel_memLp f
  filter_upwards [Lp.coeFn_sub f (kernelL2Operator syntheticDoubleKernel syntheticDoubleKernel_integrable f),
    hk] with t ht hkt
  change (f - kernelL2Operator syntheticDoubleKernel syntheticDoubleKernel_integrable f) t = _
  rw [ht]
  change f t - kernelL2Operator syntheticDoubleKernel syntheticDoubleKernel_integrable f t = _
  rw [hkt]
  rfl

theorem syntheticFullAllPassOperator_coeFn_of_representative (f : ProbeL2) (g : ℝ → ℂ)
    (hfg : f =ᵐ[volume] g) :
    syntheticFullAllPassOperator f =ᵐ[volume] syntheticFullAllPassPhysical g := by
  apply (syntheticFullAllPassOperator_coeFn f).trans
  filter_upwards [hfg] with t ht
  rw [syntheticFullAllPassPhysical, syntheticFullAllPassPhysical, ht]
  congr 1
  apply integral_congr_ae
  exact ((volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq hfg).mono
    fun s hs => congrArg (fun z : ℂ => (syntheticDoubleKernel s : ℂ) * z) hs

theorem syntheticDoubleKernel_logFourier (tau : ℝ) :
    OPICAFollowup.logFourier (fun t => (syntheticDoubleKernel t : ℂ)) tau =
      2 / ((tau : ℂ) * Complex.I + 1) := by
  have h := syntheticDoubleKernel_laplace ((tau : ℂ) * Complex.I) (by simp)
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

theorem syntheticFullAllPassPhysical_logFourier {f : ℝ → ℂ} (hf : Integrable f) (tau : ℝ) :
    OPICAFollowup.logFourier (syntheticFullAllPassPhysical f) tau =
      syntheticAllPassMultiplier ((tau : ℂ) * Complex.I) * OPICAFollowup.logFourier f tau := by
  let conv : ℝ → ℂ := (fun t => (syntheticDoubleKernel t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hconv : Integrable conv := syntheticDoubleKernel_integrable.ofReal.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hf
  have hsub : OPICAFollowup.logFourier (syntheticFullAllPassPhysical f) tau =
      OPICAFollowup.logFourier f tau - OPICAFollowup.logFourier conv tau := by
    unfold OPICAFollowup.logFourier syntheticFullAllPassPhysical
    simp_rw [mul_sub]
    change (∫ t : ℝ, Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t -
      Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * conv t) = _
    rw [integral_sub (logFourier_integrand_integrable hf tau)
      (logFourier_integrand_integrable hconv tau)]
  have hkD : Integrable (fun t : ℝ => Complex.exp (-((tau : ℂ) * Complex.I) * (t : ℂ)) *
      (syntheticDoubleKernel t : ℂ)) := by
    rw [imaginaryDamping_eq]
    exact logFourier_integrand_integrable syntheticDoubleKernel_integrable.ofReal tau
  have hfD : Integrable (fun t : ℝ => Complex.exp (-((tau : ℂ) * Complex.I) * (t : ℂ)) * f t) := by
    rw [imaginaryDamping_eq]
    exact logFourier_integrand_integrable hf tau
  have hconvFT := (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t : ℝ => (syntheticDoubleKernel t : ℂ)) f ((tau : ℂ) * Complex.I) hkD hfD).2
  change probeLaplace conv ((tau : ℂ) * Complex.I) =
    probeLaplace (fun t : ℝ => (syntheticDoubleKernel t : ℂ)) ((tau : ℂ) * Complex.I) *
      probeLaplace f ((tau : ℂ) * Complex.I) at hconvFT
  simp_rw [probeLaplace_imaginary] at hconvFT
  rw [hsub, hconvFT, syntheticDoubleKernel_logFourier]
  have hne : (tau : ℂ) * Complex.I + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hid : 1 - 2 / ((tau : ℂ) * Complex.I + 1) =
      syntheticAllPassMultiplier ((tau : ℂ) * Complex.I) := by
    unfold syntheticAllPassMultiplier
    apply (eq_div_iff hne).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
    ring
  rw [← hid]
  ring

set_option maxHeartbeats 200000 in
private theorem syntheticFullAllPassOperator_norm_schwartz (phi : SchwartzMap ℝ ℂ) :
    ‖syntheticFullAllPassOperator (phi.toLp 2 (volume : Measure ℝ))‖ =
      ‖phi.toLp 2 (volume : Measure ℝ)‖ := by
  let f : ProbeL2 := phi.toLp 2 (volume : Measure ℝ)
  have hphi : (f : ℝ → ℂ) =ᵐ[volume] phi := phi.coeFn_toLp 2 (volume : Measure ℝ)
  have hae : (syntheticFullAllPassOperator f : ℝ → ℂ) =ᵐ[volume] syntheticFullAllPassPhysical phi :=
    syntheticFullAllPassOperator_coeFn_of_representative f phi hphi
  have hf2 : MemLp (syntheticFullAllPassPhysical phi) 2 volume :=
    MemLp.ae_eq hae (Lp.memLp (syntheticFullAllPassOperator f))
  have hfp := OPICAFollowup.logFourier_plancherel
    (syntheticFullAllPassPhysical_integrable phi.integrable) hf2
  have hpp := OPICAFollowup.logFourier_plancherel phi.integrable (phi.memLp 2 volume)
  have hfreq (tau : ℝ) :
      ‖OPICAFollowup.logFourier (syntheticFullAllPassPhysical phi) tau‖ ^ 2 =
        ‖OPICAFollowup.logFourier phi tau‖ ^ 2 := by
    rw [syntheticFullAllPassPhysical_logFourier phi.integrable tau, norm_mul,
      syntheticAllPassMultiplier_boundary_norm, one_mul]
  have henergy : (∫ t : ℝ, ‖syntheticFullAllPassPhysical phi t‖ ^ 2) =
      ∫ t : ℝ, ‖phi t‖ ^ 2 := by
    rw [hfp.2, hpp.2]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hfreq)
  have hs : ‖syntheticFullAllPassOperator f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [OPICAFollowup.L2_norm_sq_eq_integral, OPICAFollowup.L2_norm_sq_eq_integral]
    calc
      _ = ∫ t : ℝ, ‖syntheticFullAllPassPhysical phi t‖ ^ 2 :=
        integral_congr_ae (hae.mono fun t ht => by rw [ht])
      _ = ∫ t : ℝ, ‖phi t‖ ^ 2 := henergy
      _ = _ := integral_congr_ae (hphi.mono fun t ht => by rw [ht])
  change ‖syntheticFullAllPassOperator f‖ = ‖f‖
  nlinarith [norm_nonneg (syntheticFullAllPassOperator f), norm_nonneg f]

/-- Actual full-line norm preservation, established first on Schwartz inputs
by convolution and Plancherel, then on all L2 inputs by density. -/
theorem syntheticFullAllPassOperator_norm (f : ProbeL2) : ‖syntheticFullAllPassOperator f‖ = ‖f‖ := by
  apply DenseRange.induction_on (p := fun f : ProbeL2 => ‖syntheticFullAllPassOperator f‖ = ‖f‖)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq syntheticFullAllPassOperator.continuous.norm continuous_norm
  · intro phi
    exact syntheticFullAllPassOperator_norm_schwartz phi

/-- Restriction preserves the actual causal norm; it does not turn the proper
causal range into the whole causal space. -/
theorem syntheticAllPassOperator_norm (f : CausalProbeL2) : ‖syntheticAllPassOperator f‖ = ‖f‖ := by
  change ‖(syntheticAllPassOperator f : ProbeL2)‖ = ‖(f : ProbeL2)‖
  exact syntheticFullAllPassOperator_norm (f : ProbeL2)




def syntheticUnstableLambda : ℂ := syntheticRightZero 4

def syntheticUnstableInput (t : ℝ) : ℂ :=
  if 0≤t then Complex.exp (syntheticUnstableLambda*(t:ℂ)) else 0

def syntheticCompactForcing (t : ℝ) : ℂ :=
  (Ico (0:ℝ) 1).indicator (fun t => (1/4:ℂ)*Complex.exp (syntheticUnstableLambda*(t:ℂ))) t

theorem syntheticUnstableLambda_exp : Complex.exp syntheticUnstableLambda=-(3/2:ℂ) := by
  have he := synthetic_right_zero_exp 4
  rw [Complex.exp_neg] at he
  change (Complex.exp syntheticUnstableLambda)⁻¹=-(2/3:ℂ) at he
  apply inv_injective
  rw [he]
  norm_num

theorem syntheticForcing_measurable : Measurable syntheticCompactForcing := by
  unfold syntheticCompactForcing
  exact (by fun_prop : Measurable (fun t : ℝ => (1/4:ℂ)*Complex.exp (syntheticUnstableLambda*(t:ℂ)))).indicator measurableSet_Ico

theorem syntheticForcing_hasCompactSupport : HasCompactSupport syntheticCompactForcing := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  have hmem : t∈Ico (0:ℝ) 1 := by
    by_contra hn
    have he : syntheticCompactForcing t=0 := by
      rw [syntheticCompactForcing,indicator_of_notMem hn]
    exact ht he
  exact ⟨hmem.1,hmem.2.le⟩

theorem syntheticForcing_norm_bound (t : ℝ) :
    ‖syntheticCompactForcing t‖≤Real.exp (syntheticUnstableLambda.re)/4 := by
  by_cases ht : t∈Ico (0:ℝ) 1
  · rw [syntheticCompactForcing,indicator_of_mem ht,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    norm_num
    have hp := synthetic_right_zero_positive 4
    change 0<syntheticUnstableLambda.re at hp
    have hex := Real.exp_le_exp.mpr (mul_le_of_le_one_right hp.le ht.2.le)
    nlinarith
  · rw [syntheticCompactForcing,indicator_of_notMem ht,norm_zero]
    positivity

theorem syntheticForcing_memLp : MemLp syntheticCompactForcing 2 volume :=
  syntheticForcing_hasCompactSupport.memLp_of_bound
    syntheticForcing_measurable.aestronglyMeasurable
    (Real.exp syntheticUnstableLambda.re/4) (Eventually.of_forall syntheticForcing_norm_bound)

def syntheticForcingVector : CausalProbeL2 :=
  ⟨syntheticForcing_memLp.toLp syntheticCompactForcing,by
    filter_upwards [syntheticForcing_memLp.coeFn_toLp] with t ht hneg
    rw [ht,syntheticCompactForcing,indicator_of_notMem (show t∉Ico (0:ℝ) 1 by exact fun h => (not_le.mpr hneg) h.1)]⟩

theorem syntheticForcingVector_coe :
    (syntheticForcingVector:ProbeL2)=ᵐ[volume] syntheticCompactForcing :=
  syntheticForcing_memLp.coeFn_toLp

def syntheticStableOutput : CausalProbeL2 := syntheticE syntheticForcingVector

def syntheticStablePhysical (t : ℝ) : ℂ :=
  ∫ s : ℝ,(syntheticExponential s:ℂ)*syntheticCompactForcing (t-s)

theorem syntheticStableOutput_coe :
    (syntheticStableOutput:ProbeL2)=ᵐ[volume] syntheticStablePhysical := by
  have hk := kernelL2Operator_coeFn_pointwise syntheticExponential synthetic_exponential_integrable
    synthetic_exponential_measurable synthetic_exponential_memLp (syntheticForcingVector:ProbeL2)
  apply hk.trans
  filter_upwards with t
  apply integral_congr_ae
  have ht := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq
    syntheticForcingVector_coe
  filter_upwards [ht] with s hs
  dsimp only [Function.comp_def] at hs
  rw [hs]

theorem syntheticForcing_laplace :
    CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0 (syntheticForcingVector:ProbeL2)=(1/4:ℂ) := by
  unfold CCM.nativeCausalLaplaceMoment
  simp only [pow_zero,one_mul]
  have ha : (fun t : ℝ => Complex.exp (-syntheticUnstableLambda*(t:ℂ))*(syntheticForcingVector:ProbeL2) t)=ᵐ[volume]
      (Ico (0:ℝ) 1).indicator (fun _ => (1/4:ℂ)) := by
    filter_upwards [syntheticForcingVector_coe] with t ht
    rw [ht]
    by_cases hm : t∈Ico (0:ℝ) 1
    · rw [syntheticCompactForcing,indicator_of_mem hm,indicator_of_mem hm]
      rw [mul_left_comm,← Complex.exp_add]
      have he : -syntheticUnstableLambda*(t:ℂ)+syntheticUnstableLambda*(t:ℂ)=0 := by ring
      rw [he,Complex.exp_zero,mul_one]
    · rw [syntheticCompactForcing,indicator_of_notMem hm,indicator_of_notMem hm,mul_zero]
  rw [integral_congr_ae ha,integral_indicator measurableSet_Ico,setIntegral_const]
  norm_num [Real.volume_Ico]

theorem syntheticStableOutput_laplace :
    CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0 (syntheticStableOutput:ProbeL2)=
      (1/4:ℂ)/(syntheticUnstableLambda+1) := by
  have hp : 0<syntheticUnstableLambda.re := synthetic_right_zero_positive 4
  rw [syntheticStableOutput,syntheticE,causalKernelOperator_laplace _ synthetic_exponential_integrable
    synthetic_exponential_zero_negative syntheticUnstableLambda hp,
    synthetic_exponential_laplace hp.le,syntheticForcing_laplace]
  ring

theorem synthetic_minus_closure_annihilated (k : ℤ) {g : CausalProbeL2}
    (hg : g∈closure (Set.range syntheticMinusOperator)) :
    CCM.nativeCausalLaplaceMoment (syntheticRightZero k) 0 (g:ProbeL2)=0 := by
  let u := CCM.nativeCausalExponentialWitness (syntheticRightZero k) (synthetic_right_zero_positive k) 0
  have hclosed : IsClosed {g : CausalProbeL2 | inner ℂ u g=0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hsub : Set.range syntheticMinusOperator ⊆ {g : CausalProbeL2 | inner ℂ u g=0} := by
    rintro _ ⟨f,rfl⟩
    change inner ℂ (CCM.nativeCausalExponentialWitness _ _ 0) (syntheticMinusOperator f)=0
    rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment]
    exact synthetic_minus_range_annihilated k f
  have hh := closure_minimal hsub hclosed hg
  change inner ℂ (CCM.nativeCausalExponentialWitness _ _ 0) g=0 at hh
  rwa [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment] at hh

theorem synthetic_output_separation {g : CausalProbeL2}
    (hg : g∈closure (Set.range syntheticMinusOperator)) :
    Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      ‖syntheticStableOutput-g‖ := by
  have hp : 0<syntheticUnstableLambda.re := synthetic_right_zero_positive 4
  have hz := synthetic_minus_closure_annihilated 4 hg
  change CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0 (g:ProbeL2)=0 at hz
  have hb := probe_laplace_evaluation_bound syntheticUnstableLambda hp (syntheticStableOutput-g)
  have he : CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0
      ((syntheticStableOutput-g:CausalProbeL2):ProbeL2)=
      (1/4:ℂ)/(syntheticUnstableLambda+1) := by
    rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment syntheticUnstableLambda hp 0,
      inner_sub_right,CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      syntheticStableOutput_laplace,hz,sub_zero]
  rwa [he] at hb

theorem synthetic_output_separation_positive :
    0<Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ := by
  have hp := synthetic_right_zero_positive 4
  change 0<syntheticUnstableLambda.re at hp
  apply mul_pos (Real.sqrt_pos.mpr (by positivity))
  apply norm_pos_iff.mpr
  apply div_ne_zero (by norm_num)
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

theorem synthetic_output_not_mem_minus_closure :
    syntheticStableOutput∉closure (Set.range syntheticMinusOperator) := by
  intro hg
  have h := synthetic_output_separation hg
  rw [sub_self,norm_zero] at h
  exact (not_le_of_gt synthetic_output_separation_positive) h

theorem synthetic_unstable_input_not_memLp : ¬ MemLp syntheticUnstableInput 2 volume := by
  intro h
  have hOne : MemLp ((Ici (0:ℝ)).indicator (fun _ => (1:ℂ))) 2 volume := by
    apply h.mono ((measurable_const.indicator measurableSet_Ici).aestronglyMeasurable)
    filter_upwards with t
    by_cases ht : 0≤t
    · rw [indicator_of_mem (show t∈Ici (0:ℝ) from ht),syntheticUnstableInput,if_pos ht, norm_one,Complex.norm_exp]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg (synthetic_right_zero_positive 4).le ht
    · rw [indicator_of_notMem (show t∉Ici (0:ℝ) from ht),norm_zero]
      exact norm_nonneg _
  have hlt := hOne.2
  rw [eLpNorm_indicator_const measurableSet_Ici (by norm_num) (by norm_num)] at hlt
  norm_num [Real.volume_Ici] at hlt

theorem syntheticUnstableInput_measurable : Measurable syntheticUnstableInput := by
  unfold syntheticUnstableInput
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem syntheticCompactForcing_eq (t : ℝ) :
    syntheticCompactForcing t=(1/4:ℂ)*(syntheticUnstableInput t+(3/2:ℂ)*syntheticUnstableInput (t-1)) := by
  by_cases ht : t<0
  · simp [syntheticCompactForcing,syntheticUnstableInput,not_le.mpr ht,
      not_le.mpr (show t-1<0 by linarith)]
  by_cases ht1 : t<1
  · rw [syntheticCompactForcing,indicator_of_mem (show t∈Ico (0:ℝ) 1 from ⟨le_of_not_gt ht,ht1⟩)]
    simp [syntheticUnstableInput,le_of_not_gt ht,not_le.mpr (show t-1<0 by linarith)]
  · rw [syntheticCompactForcing,indicator_of_notMem (show t∉Ico (0:ℝ) 1 from fun h => ht1 h.2)]
    rw [syntheticUnstableInput,if_pos (le_of_not_gt ht),syntheticUnstableInput,
      if_pos (by linarith : 0≤t-1)]
    have he : Complex.exp (syntheticUnstableLambda*(t:ℂ))=
        Complex.exp syntheticUnstableLambda*Complex.exp (syntheticUnstableLambda*((t-1:ℝ):ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he,syntheticUnstableLambda_exp]
    ring

def syntheticLocalExponentialConvolution (t : ℝ) : ℂ :=
  ∫ s : ℝ,(syntheticExponential s:ℂ)*syntheticUnstableInput (t-s)

theorem syntheticLocalProduct_integrable (t : ℝ) :
    Integrable (fun s : ℝ => (syntheticExponential s:ℂ)*syntheticUnstableInput (t-s)) := by
  have hm : Measurable (fun s : ℝ => (syntheticExponential s:ℂ)*syntheticUnstableInput (t-s)) :=
    synthetic_exponential_measurable.complex_ofReal.mul
      (syntheticUnstableInput_measurable.comp (measurable_const.sub measurable_id))
  apply (synthetic_exponential_integrable.norm.mul_const
    (Real.exp (syntheticUnstableLambda.re*t))).mono' hm.aestronglyMeasurable
  filter_upwards with s
  by_cases hs : s<0
  · rw [synthetic_exponential_zero_negative s hs,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  by_cases hts : t-s<0
  · rw [syntheticUnstableInput,if_neg (not_le.mpr hts),mul_zero,norm_zero]
    positivity
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,syntheticUnstableInput,
    if_pos (le_of_not_gt hts),Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp := synthetic_right_zero_positive 4
  change 0<syntheticUnstableLambda.re at hp
  nlinarith

theorem syntheticLocalExponentialConvolution_neg {t : ℝ} (ht : t<0) :
    syntheticLocalExponentialConvolution t=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with s
  change (syntheticExponential s:ℂ)*syntheticUnstableInput (t-s)=0
  by_cases hs : s<0
  · rw [synthetic_exponential_zero_negative s hs,Complex.ofReal_zero,zero_mul]
  · rw [syntheticUnstableInput,if_neg (by linarith : ¬0≤t-s),mul_zero]

theorem syntheticLocalExponentialConvolution_formula {t : ℝ} (ht : 0≤t) :
    syntheticLocalExponentialConvolution t=
      (Complex.exp (syntheticUnstableLambda*(t:ℂ))-Complex.exp (-(t:ℂ)))/(syntheticUnstableLambda+1) := by
  have hp := synthetic_right_zero_positive 4
  change 0<syntheticUnstableLambda.re at hp
  have hden : syntheticUnstableLambda+1≠0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hfun : (fun s : ℝ => (syntheticExponential s:ℂ)*syntheticUnstableInput (t-s))=
      (Icc 0 t).indicator (fun s : ℝ => Complex.exp (syntheticUnstableLambda*(t:ℂ))*
        Complex.exp (-(syntheticUnstableLambda+1)*(s:ℂ))) := by
    funext s
    by_cases hs : s∈Icc 0 t
    · rw [indicator_of_mem hs,syntheticExponential,if_pos hs.1,
        syntheticUnstableInput,if_pos (by linarith [hs.2] : 0≤t-s),Complex.ofReal_exp,
        ← Complex.exp_add,← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem hs]
      by_cases hs0 : s<0
      · rw [synthetic_exponential_zero_negative s hs0,Complex.ofReal_zero,zero_mul]
      · rw [syntheticUnstableInput,if_neg (by intro h; exact hs ⟨le_of_not_gt hs0,by linarith⟩),mul_zero]
  unfold syntheticLocalExponentialConvolution
  rw [hfun,integral_indicator measurableSet_Icc,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,integral_exp_mul_complex (neg_ne_zero.mpr hden)]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have he : Complex.exp (syntheticUnstableLambda*(t:ℂ))*
      Complex.exp (-(syntheticUnstableLambda+1)*(t:ℂ))=Complex.exp (-(t:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  field_simp
  rw [show -((t:ℂ)*(syntheticUnstableLambda+1))=-(syntheticUnstableLambda+1)*(t:ℂ) by ring,
    mul_sub,he]
  ring

theorem syntheticStablePhysical_eq_local_exponentials (t : ℝ) :
    syntheticStablePhysical t=(1/4:ℂ)*(syntheticLocalExponentialConvolution t+
      (3/2:ℂ)*syntheticLocalExponentialConvolution (t-1)) := by
  have hsecond : Integrable (fun s : ℝ => (syntheticExponential s:ℂ)*syntheticUnstableInput (t-s-1)) := by
    convert syntheticLocalProduct_integrable (t-1) using 1
    funext s
    congr 2
    ring
  have hp (s : ℝ) : (syntheticExponential s:ℂ)*syntheticCompactForcing (t-s)=
      (1/4:ℂ)*((syntheticExponential s:ℂ)*syntheticUnstableInput (t-s))+
      ((1/4:ℂ)*(3/2))*((syntheticExponential s:ℂ)*syntheticUnstableInput (t-s-1)) := by
    rw [syntheticCompactForcing_eq]
    ring
  unfold syntheticStablePhysical
  rw [integral_congr_ae (Eventually.of_forall hp),
    integral_add ((syntheticLocalProduct_integrable t).const_mul _) (hsecond.const_mul _),
    integral_const_mul,integral_const_mul]
  have he : (∫ s : ℝ,(syntheticExponential s:ℂ)*syntheticUnstableInput (t-s-1))=
      syntheticLocalExponentialConvolution (t-1) := by
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    ring
  rw [he]
  unfold syntheticLocalExponentialConvolution
  ring

def syntheticLocalCompletion (t : ℝ) : ℂ :=
  ∫ s : ℝ,(syntheticMinusKernel s:ℂ)*syntheticUnstableInput (t-s)

theorem syntheticLocalCompletion_eq_output (t : ℝ) :
    syntheticLocalCompletion t=syntheticStablePhysical t := by
  have hshift : Integrable (fun s : ℝ => (syntheticExponential (s-1):ℂ)*syntheticUnstableInput (t-s)) := by
    convert (syntheticLocalProduct_integrable (t-1)).comp_sub_right 1 using 1
    funext s
    congr 2
    ring
  have hp (s : ℝ) : (syntheticMinusKernel s:ℂ)*syntheticUnstableInput (t-s)=
      (1/4:ℂ)*((syntheticExponential s:ℂ)*syntheticUnstableInput (t-s))+
      ((1/4:ℂ)*(3/2))*((syntheticExponential (s-1):ℂ)*syntheticUnstableInput (t-s)) := by
    simp only [syntheticMinusKernel]
    push_cast
    ring
  rw [syntheticLocalCompletion,syntheticStablePhysical_eq_local_exponentials,
    integral_congr_ae (Eventually.of_forall hp),
    integral_add ((syntheticLocalProduct_integrable t).const_mul _) (hshift.const_mul _),
    integral_const_mul,integral_const_mul]
  have he : (∫ s : ℝ,(syntheticExponential (s-1):ℂ)*syntheticUnstableInput (t-s))=
      syntheticLocalExponentialConvolution (t-1) := by
    have h := integral_sub_right_eq_self
      (fun s : ℝ => (syntheticExponential s:ℂ)*syntheticUnstableInput ((t-1)-s)) (1:ℝ)
        (μ:=(volume:Measure ℝ))
    change _=∫ s : ℝ,(syntheticExponential s:ℂ)*syntheticUnstableInput ((t-1)-s)
    rw [← h]
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    ring
  rw [he]
  unfold syntheticLocalExponentialConvolution
  ring

theorem syntheticStablePhysical_first {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    syntheticStablePhysical t=(1/4:ℂ)*
      (Complex.exp (syntheticUnstableLambda*(t:ℂ))-Complex.exp (-(t:ℂ)))/(syntheticUnstableLambda+1) := by
  rw [syntheticStablePhysical_eq_local_exponentials,syntheticLocalExponentialConvolution_formula ht0,
    syntheticLocalExponentialConvolution_neg (by linarith : t-1<0),mul_zero,add_zero]
  ring

theorem syntheticStablePhysical_tail {t : ℝ} (ht : 1≤t) :
    syntheticStablePhysical t=-(1/4:ℂ)*(1+(3/2)*Complex.exp 1)*
      Complex.exp (-(t:ℂ))/(syntheticUnstableLambda+1) := by
  rw [syntheticStablePhysical_eq_local_exponentials,
    syntheticLocalExponentialConvolution_formula (by linarith : 0≤t),
    syntheticLocalExponentialConvolution_formula (by linarith : 0≤t-1)]
  have hx : Complex.exp (syntheticUnstableLambda*(t:ℂ))=
      -(3/2:ℂ)*Complex.exp (syntheticUnstableLambda*((t-1:ℝ):ℂ)) := by
    rw [← syntheticUnstableLambda_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he : Complex.exp (-((t-1:ℝ):ℂ))=Complex.exp (-(t:ℂ))*Complex.exp 1 := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hx,he]
  ring



theorem syntheticAllPassOperator_apply (f : CausalProbeL2) :
    syntheticAllPassOperator f=f-(2:ℂ) • syntheticE f := by
  apply Subtype.ext
  change (f:ProbeL2)-kernelL2Operator syntheticDoubleKernel syntheticDoubleKernel_integrable (f:ProbeL2)=
    (f:ProbeL2)-(2:ℂ) • kernelL2Operator syntheticExponential synthetic_exponential_integrable (f:ProbeL2)
  congr 1
  rw [kernelL2Operator_apply,kernelL2Operator_apply,← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [syntheticDoubleKernel,Complex.ofReal_mul,Complex.ofReal_ofNat,
    RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  module

theorem syntheticE_zero (f : CausalProbeL2) (hf : syntheticE f=0) : f=0 := by
  apply probeCausalLaplace_injective f
  intro z hz
  have he := causalKernelOperator_laplace syntheticExponential synthetic_exponential_integrable
    synthetic_exponential_zero_negative z hz f
  change CCM.nativeCausalLaplaceMoment z 0 (syntheticE f:ProbeL2)=_ at he
  rw [hf] at he
  have hz0 := CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0 (0:CausalProbeL2)
  simp only [inner_zero_right] at hz0
  rw [← hz0] at he
  have heq : (1/(z+1))*CCM.nativeCausalLaplaceMoment z 0 (f:ProbeL2)=0 := by
    rw [← synthetic_exponential_laplace hz.le]
    exact he.symm
  apply (mul_eq_zero.mp heq).resolve_left
  apply one_div_ne_zero
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

theorem syntheticE_denseRange : DenseRange syntheticE := by
  have ho : syntheticE.rangeᗮ=⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    have hi : inner ℂ (syntheticE f) f=0 :=
      (Submodule.mem_orthogonal syntheticE.range f).mp hf _ ⟨f,rfl⟩
    have hs := syntheticAllPassOperator_norm f
    rw [syntheticAllPassOperator_apply] at hs
    have hh := @norm_sub_sq ℂ CausalProbeL2 _ _ _ f ((2:ℂ) • syntheticE f)
    have hinner : inner ℂ f ((2:ℂ) • syntheticE f)=0 := by
      rw [inner_smul_right (𝕜:=ℂ) f (syntheticE f) (2:ℂ),inner_eq_zero_symm.mpr hi,mul_zero]
    rw [hinner,map_zero,mul_zero,sub_zero] at hh
    simp only [norm_smul] at hh
    norm_num at hh
    change ‖(f:ProbeL2)-(2:ℂ) • (syntheticE f:ProbeL2)‖=‖(f:ProbeL2)‖ at hs
    have hnorm : ‖(syntheticE f:ProbeL2)‖=0 := by
      nlinarith [congrArg (fun r : ℝ => r^2) hs,norm_nonneg (syntheticE f:ProbeL2)]
    apply syntheticE_zero f
    apply Subtype.ext
    exact norm_eq_zero.mp hnorm
  have htop : syntheticE.range.topologicalClosure=⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,ho,Submodule.bot_orthogonal_eq_top]
  change Dense (Set.range syntheticE)
  apply dense_iff_closure_eq.mpr
  exact congrArg (fun p : Submodule ℂ CausalProbeL2 => (p:Set CausalProbeL2)) htop

theorem syntheticE_delay (t : ℝ) (ht : 0≤t) (f : CausalProbeL2) :
    syntheticE (probeDelay t ht f)=probeDelay t ht (syntheticE f) := by
  apply Subtype.ext
  change kernelL2Operator syntheticExponential synthetic_exponential_integrable
    (CCM.nativeCompletionL2Delay t (f:ProbeL2))=
    CCM.nativeCompletionL2Delay t (kernelL2Operator syntheticExponential synthetic_exponential_integrable (f:ProbeL2))
  rw [kernelL2Operator_apply,kernelL2Operator_apply,
    ← (CCM.nativeCompletionL2Delay t).integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with s
  change syntheticExponential s • CCM.nativeCompletionL2Delay s
    (CCM.nativeCompletionL2Delay t (f:ProbeL2))=
    CCM.nativeCompletionL2Delay t (syntheticExponential s • CCM.nativeCompletionL2Delay s (f:ProbeL2))
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
  rw [probeL2Delay_comm]

def syntheticPlusFactor : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  (3/2:ℂ) • ContinuousLinearMap.id ℂ CausalProbeL2+probeDelay 1 (by norm_num)

theorem syntheticPlusFactor_isUnit : IsUnit syntheticPlusFactor := by
  let D := probeDelay 1 (by norm_num)
  have hD : ‖D‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    rw [probeDelay_norm,one_mul]
  have hsmall : ‖-(2/3:ℂ) • D‖<1 := by
    have hb : ‖-(2/3:ℂ) • D‖≤(2/3:ℝ) := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro f
      change ‖-(2/3:ℂ) • D f‖≤(2/3:ℝ)*‖f‖
      rw [norm_smul,probeDelay_norm]
      norm_num
    exact hb.trans_lt (by norm_num)
  have hunit : IsUnit (1+(2/3:ℂ) • D) := by
    have h := isUnit_one_sub_of_norm_lt_one (R:=CausalProbeL2 →L[ℂ] CausalProbeL2) hsmall
    have he : (1:CausalProbeL2 →L[ℂ] CausalProbeL2)-(-(2/3:ℂ) • D)=1+(2/3:ℂ) • D := by
      apply ContinuousLinearMap.ext
      intro f
      simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply]
      module
    rw [he] at h
    exact h
  have hscalar : IsUnit ((3/2:ℂ) • (1:CausalProbeL2 →L[ℂ] CausalProbeL2)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr (by norm_num : (3/2:ℂ)≠0)).map (algebraMap ℂ _)
  have he : syntheticPlusFactor=((3/2:ℂ) • (1:CausalProbeL2 →L[ℂ] CausalProbeL2))*(1+(2/3:ℂ) • D) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [syntheticPlusFactor,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply,map_add,map_smul]
    module
  rw [he]
  exact hscalar.mul hunit

theorem synthetic_plus_factorization (f : CausalProbeL2) :
    syntheticPlusOperator f=syntheticE ((1/4:ℂ) • syntheticPlusFactor f) := by
  rw [(synthetic_twins_operator_formulas f).2]
  simp only [syntheticPlusFactor,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_smul,map_add,syntheticE_delay]
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  norm_num

theorem synthetic_plus_range_eq : Set.range syntheticPlusOperator=Set.range syntheticE := by
  have hsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp syntheticPlusFactor_isUnit).2
  ext y
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨(1/4:ℂ) • syntheticPlusFactor f,(synthetic_plus_factorization f).symm⟩
  · rintro ⟨f,rfl⟩
    obtain ⟨g,hg⟩ := hsurj ((4:ℂ) • f)
    refine ⟨g,?_⟩
    rw [synthetic_plus_factorization,hg,smul_smul]
    norm_num

theorem synthetic_plus_dense_causal_range : DenseRange syntheticPlusOperator := by
  change Dense (Set.range syntheticPlusOperator)
  rw [synthetic_plus_range_eq]
  exact syntheticE_denseRange


theorem synthetic_output_mem_plus_range :
    syntheticStableOutput∈Set.range syntheticPlusOperator := by
  rw [synthetic_plus_range_eq]
  exact ⟨syntheticForcingVector,rfl⟩

theorem synthetic_causal_range_closures_differ :
    closure (Set.range syntheticMinusOperator)≠closure (Set.range syntheticPlusOperator) := by
  intro he
  have h := subset_closure synthetic_output_mem_plus_range
  rw [← he] at h
  exact synthetic_output_not_mem_minus_closure h

theorem synthetic_minus_not_dense_causal_range : ¬DenseRange syntheticMinusOperator := by
  intro hd
  exact synthetic_output_not_mem_minus_closure (hd syntheticStableOutput)


def syntheticFullE : ProbeL2 →L[ℂ] ProbeL2 :=
  kernelL2Operator syntheticExponential synthetic_exponential_integrable

theorem synthetic_full_delay_zero (f : ProbeL2) : CCM.nativeCompletionL2Delay 0 f=f := by
  apply Lp.ext
  filter_upwards [CCM.nativeCompletionL2Delay_coeFn 0 f] with t ht
  simpa using ht

theorem syntheticFullE_delay (t : ℝ) (f : ProbeL2) :
    syntheticFullE (CCM.nativeCompletionL2Delay t f)=
      CCM.nativeCompletionL2Delay t (syntheticFullE f) := by
  rw [syntheticFullE, kernelL2Operator_apply,kernelL2Operator_apply,
    ← (CCM.nativeCompletionL2Delay t).integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with s
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
  rw [probeL2Delay_comm]

theorem syntheticFullE_closure_contains_causal (f : CausalProbeL2) :
    (f:ProbeL2)∈closure (Set.range syntheticFullE) := by
  apply map_mem_closure (continuous_subtype_val) (syntheticE_denseRange f)
  rintro _ ⟨g,rfl⟩
  exact ⟨(g:ProbeL2),rfl⟩

theorem syntheticFullE_closure_delay (t : ℝ) {f : ProbeL2}
    (hf : f∈closure (Set.range syntheticFullE)) :
    CCM.nativeCompletionL2Delay t f∈closure (Set.range syntheticFullE) := by
  apply map_mem_closure (CCM.nativeCompletionL2Delay t).continuous hf
  rintro _ ⟨g,rfl⟩
  exact ⟨CCM.nativeCompletionL2Delay t g,syntheticFullE_delay t g⟩

theorem syntheticFullE_closure_compact (g : ℝ → ℂ) (hg : HasCompactSupport g)
    (hgm : MemLp g 2 volume) :
    hgm.toLp g∈closure (Set.range syntheticFullE) := by
  obtain ⟨b,hb⟩ := hg.isCompact.bddBelow
  let x : ProbeL2 := hgm.toLp g
  have hcausal : CCM.nativeCompletionL2Delay (-b) x∈CausalProbeL2 := by
    have hrep := (measurePreserving_sub_right volume (-b)).quasiMeasurePreserving.ae_eq hgm.coeFn_toLp
    filter_upwards [CCM.nativeCompletionL2Delay_coeFn (-b) x,hrep] with t ht ht' hneg
    dsimp only [Function.comp_def] at ht'
    rw [ht,ht']
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := hb hm
    linarith
  let y : CausalProbeL2 := ⟨CCM.nativeCompletionL2Delay (-b) x,hcausal⟩
  have hy := syntheticFullE_closure_contains_causal y
  have h := syntheticFullE_closure_delay b hy
  change CCM.nativeCompletionL2Delay b (CCM.nativeCompletionL2Delay (-b) x)∈_ at h
  rw [synthetic_delay_add,add_neg_cancel,synthetic_full_delay_zero] at h
  exact h

theorem syntheticFullE_denseRange : DenseRange syntheticFullE := by
  intro f
  have hclosed : IsClosed (closure (Set.range syntheticFullE)) := isClosed_closure
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro epsilon hepsilon
  have hf : MemLp (f:ℝ → ℂ) (ENNReal.ofReal (2:ℝ)) volume := by simpa using Lp.memLp f
  obtain ⟨g,hgc,herr,hgcont,hg2⟩ :=
    hf.exists_hasCompactSupport_integral_rpow_sub_le (by norm_num : (0:ℝ)<2)
      (sq_pos_of_pos (half_pos hepsilon))
  have hgm : MemLp g 2 volume := by simpa using hg2
  let G : ProbeL2 := hgm.toLp g
  have hG := syntheticFullE_closure_compact g hgc hgm
  refine ⟨G,hG,?_⟩
  rw [dist_eq_norm]
  have hsq : ‖f-G‖^2≤(epsilon/2)^2 := by
    rw [OPICAFollowup.L2_norm_sq_eq_integral]
    calc
      _ = ∫ t : ℝ,‖(f:ℝ → ℂ) t-g t‖^2 := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub f G,hgm.coeFn_toLp] with t ht ht'
        change ‖(f-G) t‖^2=_
        rw [ht]
        change ‖f t-G t‖^2=_
        rw [ht']
      _ ≤ _ := by simpa using herr
  nlinarith [norm_nonneg (f-G)]

#print axioms Zeta23.OPICARound2.syntheticFullE_denseRange
#print axioms Zeta23.OPICARound2.synthetic_causal_range_closures_differ
#print axioms Zeta23.OPICARound2.synthetic_output_separation
#print axioms Zeta23.OPICARound2.syntheticLocalCompletion_eq_output
def syntheticFullMinusOperator : ProbeL2 →L[ℂ] ProbeL2 :=
  kernelL2Operator syntheticMinusKernel synthetic_minus_integrable
def syntheticFullPlusOperator : ProbeL2 →L[ℂ] ProbeL2 :=
  kernelL2Operator syntheticPlusKernel synthetic_plus_integrable

theorem synthetic_full_twins_operator_formulas (f : ProbeL2) :
    syntheticFullMinusOperator f=(1/4:ℝ) •
      (syntheticFullE f+(3/2:ℝ) • CCM.nativeCompletionL2Delay 1 (syntheticFullE f)) ∧
    syntheticFullPlusOperator f=(1/4:ℝ) •
      ((3/2:ℝ) • syntheticFullE f+CCM.nativeCompletionL2Delay 1 (syntheticFullE f)) := by
  have hE := kernelL2Integrand_integrable syntheticExponential synthetic_exponential_integrable f
  have hD := kernelL2Integrand_integrable (fun t => syntheticExponential (t-1))
    (synthetic_exponential_integrable.comp_sub_right 1) f
  change Integrable (fun t : ℝ => syntheticExponential t • CCM.nativeCompletionL2Delay t f) at hE
  change Integrable (fun t : ℝ => syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t f) at hD
  have hEr : Integrable (fun t : ℝ => (3/2:ℝ) •
      (syntheticExponential t • CCM.nativeCompletionL2Delay t f)) :=
    Integrable.smul (3/2:ℝ) hE
  have hDr : Integrable (fun t : ℝ => (3/2:ℝ) •
      (syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t f)) :=
    Integrable.smul (3/2:ℝ) hD
  have hminus : kernelL2Operator syntheticMinusKernel synthetic_minus_integrable f=
      (1/4:ℝ) • (kernelL2Operator syntheticExponential synthetic_exponential_integrable f+
        (3/2:ℝ) • kernelL2Operator (fun t => syntheticExponential (t-1))
          (synthetic_exponential_integrable.comp_sub_right 1) f) := by
    simp only [kernelL2Operator_apply]
    have hp (t : ℝ) : syntheticMinusKernel t • CCM.nativeCompletionL2Delay t f=
        (1/4:ℝ) • (syntheticExponential t • CCM.nativeCompletionL2Delay t f+
          (3/2:ℝ) • (syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t f)) := by
      rw [syntheticMinusKernel]
      module
    rw [integral_congr_ae (Eventually.of_forall hp),integral_smul,
      integral_add hE hDr,integral_smul]
  have hplus : kernelL2Operator syntheticPlusKernel synthetic_plus_integrable f=
      (1/4:ℝ) • ((3/2:ℝ) • kernelL2Operator syntheticExponential synthetic_exponential_integrable f+
        kernelL2Operator (fun t => syntheticExponential (t-1))
          (synthetic_exponential_integrable.comp_sub_right 1) f) := by
    simp only [kernelL2Operator_apply]
    have hp (t : ℝ) : syntheticPlusKernel t • CCM.nativeCompletionL2Delay t f=
        (1/4:ℝ) • ((3/2:ℝ) • (syntheticExponential t • CCM.nativeCompletionL2Delay t f)+
          syntheticExponential (t-1) • CCM.nativeCompletionL2Delay t f) := by
      rw [syntheticPlusKernel]
      module
    rw [integral_congr_ae (Eventually.of_forall hp),integral_smul,
      integral_add hEr hD,integral_smul]
  rw [synthetic_shifted_kernel_value] at hminus hplus
  exact ⟨hminus,hplus⟩

def syntheticFullDelay (t : ℝ) : ProbeL2 →L[ℂ] ProbeL2 :=
  (CCM.nativeCompletionL2Delay t).toContinuousLinearMap

theorem syntheticFullDelay_mul (s t : ℝ) :
    syntheticFullDelay s*syntheticFullDelay t=syntheticFullDelay (s+t) := by
  apply ContinuousLinearMap.ext
  intro f
  exact synthetic_delay_add s t f

theorem syntheticFullDelay_zero : syntheticFullDelay 0=1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact synthetic_full_delay_zero f

theorem syntheticFullDelay_isUnit (t : ℝ) : IsUnit (syntheticFullDelay t) := by
  refine ⟨⟨syntheticFullDelay t,syntheticFullDelay (-t),?_,?_⟩,rfl⟩
  · rw [syntheticFullDelay_mul,add_neg_cancel,syntheticFullDelay_zero]
  · rw [syntheticFullDelay_mul,neg_add_cancel,syntheticFullDelay_zero]

theorem syntheticFullNeumann_isUnit (t : ℝ) :
    IsUnit ((1:ProbeL2 →L[ℂ] ProbeL2)+(2/3:ℂ) • syntheticFullDelay t) := by
  have hsmall : ‖-(2/3:ℂ) • syntheticFullDelay t‖<1 := by
    have hb : ‖-(2/3:ℂ) • syntheticFullDelay t‖≤(2/3:ℝ) := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro f
      change ‖-(2/3:ℂ) • CCM.nativeCompletionL2Delay t f‖≤(2/3:ℝ)*‖f‖
      rw [norm_smul,(CCM.nativeCompletionL2Delay t).norm_map]
      norm_num
    exact hb.trans_lt (by norm_num)
  have h := isUnit_one_sub_of_norm_lt_one (R:=ProbeL2 →L[ℂ] ProbeL2) hsmall
  have he : (1:ProbeL2 →L[ℂ] ProbeL2)-(-(2/3:ℂ) • syntheticFullDelay t)=
      1+(2/3:ℂ) • syntheticFullDelay t := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply]
    module
  rw [he] at h
  exact h

def syntheticFullPlusFactor : ProbeL2 →L[ℂ] ProbeL2 :=
  (3/2:ℂ) • (1:ProbeL2 →L[ℂ] ProbeL2)+syntheticFullDelay 1

def syntheticFullMinusFactor : ProbeL2 →L[ℂ] ProbeL2 :=
  (1:ProbeL2 →L[ℂ] ProbeL2)+(3/2:ℂ) • syntheticFullDelay 1

theorem syntheticFullScalar_isUnit : IsUnit ((3/2:ℂ) • (1:ProbeL2 →L[ℂ] ProbeL2)) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (3/2:ℂ)≠0)).map (algebraMap ℂ _)

theorem syntheticFullPlusFactor_isUnit : IsUnit syntheticFullPlusFactor := by
  have he : syntheticFullPlusFactor=((3/2:ℂ) • (1:ProbeL2 →L[ℂ] ProbeL2))*
      (1+(2/3:ℂ) • syntheticFullDelay 1) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [syntheticFullPlusFactor,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,ContinuousLinearMap.mul_apply,
      map_add,map_smul]
    module
  rw [he]
  exact syntheticFullScalar_isUnit.mul (syntheticFullNeumann_isUnit 1)

theorem syntheticFullMinusFactor_isUnit : IsUnit syntheticFullMinusFactor := by
  have he : syntheticFullMinusFactor=((3/2:ℂ) • (1:ProbeL2 →L[ℂ] ProbeL2))*
      syntheticFullDelay 1*(1+(2/3:ℂ) • syntheticFullDelay (-1)) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [syntheticFullMinusFactor,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,ContinuousLinearMap.mul_apply,
      map_add,map_smul]
    have hd : syntheticFullDelay 1 (syntheticFullDelay (-1) f)=f := by
      change CCM.nativeCompletionL2Delay 1 (CCM.nativeCompletionL2Delay (-1) f)=f
      rw [synthetic_delay_add,show (1:ℝ)+(-1)=0 by norm_num,synthetic_full_delay_zero]
    rw [hd]
    module
  rw [he]
  exact (syntheticFullScalar_isUnit.mul (syntheticFullDelay_isUnit 1)).mul
    (syntheticFullNeumann_isUnit (-1))

theorem syntheticFull_twins_factorization (f : ProbeL2) :
    syntheticFullMinusOperator f=syntheticFullE ((1/4:ℂ) • syntheticFullMinusFactor f) ∧
    syntheticFullPlusOperator f=syntheticFullE ((1/4:ℂ) • syntheticFullPlusFactor f) := by
  have hd : syntheticFullE ((CCM.nativeCompletionL2Delay 1).toContinuousLinearMap f)=
      CCM.nativeCompletionL2Delay 1 (syntheticFullE f) := syntheticFullE_delay 1 f
  constructor
  · rw [(synthetic_full_twins_operator_formulas f).1]
    simp only [syntheticFullMinusFactor,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,map_smul,map_add,syntheticFullDelay]
    rw [hd]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    norm_num
  · rw [(synthetic_full_twins_operator_formulas f).2]
    simp only [syntheticFullPlusFactor,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,map_smul,map_add,syntheticFullDelay]
    rw [hd]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    norm_num

theorem syntheticFull_twins_range_eq :
    Set.range syntheticFullMinusOperator=Set.range syntheticFullE ∧
    Set.range syntheticFullPlusOperator=Set.range syntheticFullE := by
  constructor
  · have hsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp syntheticFullMinusFactor_isUnit).2
    ext y
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨(1/4:ℂ) • syntheticFullMinusFactor f,(syntheticFull_twins_factorization f).1.symm⟩
    · rintro ⟨f,rfl⟩
      obtain ⟨g,hg⟩ := hsurj ((4:ℂ) • f)
      refine ⟨g,?_⟩
      rw [(syntheticFull_twins_factorization g).1,hg,smul_smul]
      norm_num
  · have hsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp syntheticFullPlusFactor_isUnit).2
    ext y
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨(1/4:ℂ) • syntheticFullPlusFactor f,(syntheticFull_twins_factorization f).2.symm⟩
    · rintro ⟨f,rfl⟩
      obtain ⟨g,hg⟩ := hsurj ((4:ℂ) • f)
      refine ⟨g,?_⟩
      rw [(syntheticFull_twins_factorization g).2,hg,smul_smul]
      norm_num

theorem synthetic_full_twins_dense_ranges :
    DenseRange syntheticFullMinusOperator ∧ DenseRange syntheticFullPlusOperator := by
  constructor
  · change Dense (Set.range syntheticFullMinusOperator)
    rw [syntheticFull_twins_range_eq.1]
    exact syntheticFullE_denseRange
  · change Dense (Set.range syntheticFullPlusOperator)
    rw [syntheticFull_twins_range_eq.2]
    exact syntheticFullE_denseRange

theorem synthetic_boundary_multipliers_nonzero (xi : ℝ) :
    syntheticMinusMultiplier ((xi:ℂ)*Complex.I)≠0 ∧ syntheticPlusMultiplier ((xi:ℂ)*Complex.I)≠0 := by
  have hp : 0<(13+12*Real.cos xi)/(64*(1+xi^2)) := by
    apply div_pos
    · nlinarith [Real.neg_one_le_cos xi]
    · positivity
  constructor
  · intro h
    have he := (synthetic_boundary_power xi).1
    rw [h,norm_zero,zero_pow (by norm_num)] at he
    linarith
  · intro h
    have he := (synthetic_boundary_power xi).2
    rw [h,norm_zero,zero_pow (by norm_num)] at he
    linarith


theorem syntheticStablePhysical_zero_negative {t : ℝ} (ht : t<0) :
    syntheticStablePhysical t=0 := by
  rw [syntheticStablePhysical_eq_local_exponentials,syntheticLocalExponentialConvolution_neg ht,
    syntheticLocalExponentialConvolution_neg (by linarith : t-1<0)]
  ring

def syntheticDampedKernel (epsilon t : ℝ) : ℝ :=
  Real.exp (-epsilon*t)*syntheticMinusKernel t

theorem syntheticDampedKernel_zero_negative (epsilon t : ℝ) (ht : t<0) :
    syntheticDampedKernel epsilon t=0 := by
  rw [syntheticDampedKernel,synthetic_minus_zero_negative t ht,mul_zero]

theorem syntheticDampedKernel_integrable (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    Integrable (syntheticDampedKernel epsilon) := by
  have hm : AEStronglyMeasurable (syntheticDampedKernel epsilon) volume :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-epsilon*t))).aestronglyMeasurable.mul
      synthetic_minus_integrable.aestronglyMeasurable
  apply synthetic_minus_integrable.norm.mono' hm
  filter_upwards with t
  by_cases ht : t<0
  · simp [syntheticDampedKernel_zero_negative epsilon t ht]
  rw [syntheticDampedKernel,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by nlinarith [le_of_not_gt ht]))

def syntheticDampedOperator (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator (syntheticDampedKernel epsilon)
    (syntheticDampedKernel_integrable epsilon hepsilon) (syntheticDampedKernel_zero_negative epsilon)

theorem syntheticDampedKernel_laplace (epsilon : ℝ) (hepsilon : 0≤epsilon)
    (z : ℂ) (hz : 0≤z.re) :
    probeLaplace (fun t => (syntheticDampedKernel epsilon t:ℂ)) z=
      syntheticMinusMultiplier (z+(epsilon:ℂ)) := by
  have he : probeLaplace (fun t => (syntheticDampedKernel epsilon t:ℂ)) z=
      probeLaplace (fun t => (syntheticMinusKernel t:ℂ)) (z+(epsilon:ℂ)) := by
    unfold probeLaplace
    apply integral_congr_ae
    filter_upwards with t
    simp only [syntheticDampedKernel,Complex.ofReal_mul,Complex.ofReal_exp]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  exact (synthetic_twins_laplace (by simp; linarith : 0≤(z+(epsilon:ℂ)).re)).1

def syntheticDampedInput (epsilon t : ℝ) : ℂ :=
  (Real.exp (-epsilon*t):ℂ)*syntheticUnstableInput t

def syntheticDampedPhysical (epsilon t : ℝ) : ℂ :=
  (Real.exp (-epsilon*t):ℂ)*syntheticStablePhysical t

theorem syntheticDampedPhysical_memLp (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    MemLp (syntheticDampedPhysical epsilon) 2 volume := by
  have hY : MemLp syntheticStablePhysical 2 volume :=
    MemLp.ae_eq syntheticStableOutput_coe (Lp.memLp (syntheticStableOutput:ProbeL2))
  have hm : AEStronglyMeasurable (syntheticDampedPhysical epsilon) volume :=
    ((by fun_prop : Continuous (fun t : ℝ => (Real.exp (-epsilon*t):ℂ))).aestronglyMeasurable).mul hY.1
  apply hY.mono hm
  filter_upwards with t
  by_cases ht : t<0
  · simp [syntheticDampedPhysical,syntheticStablePhysical_zero_negative ht]
  rw [syntheticDampedPhysical,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by nlinarith [le_of_not_gt ht]))

def syntheticDampedOutput (epsilon : ℝ) (hepsilon : 0≤epsilon) : CausalProbeL2 :=
  ⟨(syntheticDampedPhysical_memLp epsilon hepsilon).toLp (syntheticDampedPhysical epsilon),by
    filter_upwards [(syntheticDampedPhysical_memLp epsilon hepsilon).coeFn_toLp] with t ht hneg
    rw [ht,syntheticDampedPhysical,syntheticStablePhysical_zero_negative hneg,mul_zero]⟩

theorem syntheticDampedOutput_coe (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    (syntheticDampedOutput epsilon hepsilon:ProbeL2)=ᵐ[volume] syntheticDampedPhysical epsilon :=
  (syntheticDampedPhysical_memLp epsilon hepsilon).coeFn_toLp

theorem synthetic_damped_local_completion (epsilon t : ℝ) :
    (∫ s : ℝ,(syntheticDampedKernel epsilon s:ℂ)*syntheticDampedInput epsilon (t-s))=
      syntheticDampedPhysical epsilon t := by
  rw [syntheticDampedPhysical,← syntheticLocalCompletion_eq_output,syntheticLocalCompletion,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  simp only [syntheticDampedKernel,syntheticDampedInput,Complex.ofReal_mul]
  have he : Real.exp (-epsilon*s)*Real.exp (-epsilon*(t-s))=
      Real.exp (-epsilon*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((Real.exp (-epsilon*s)*Real.exp (-epsilon*(t-s)):ℝ):ℂ)*
      ((syntheticMinusKernel s:ℂ)*syntheticUnstableInput (t-s)) := by push_cast; ring
    _ = _ := by rw [he]

theorem syntheticDampedInput_formula (epsilon t : ℝ) (ht : 0≤t) :
    syntheticDampedInput epsilon t=Complex.exp ((syntheticUnstableLambda-(epsilon:ℂ))*(t:ℂ)) := by
  rw [syntheticDampedInput,syntheticUnstableInput,if_pos ht,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem synthetic_damped_input_not_memLp (epsilon : ℝ) (hepsilon : epsilon<syntheticUnstableLambda.re) :
    ¬MemLp (syntheticDampedInput epsilon) 2 volume := by
  intro h
  have hOne : MemLp ((Ici (0:ℝ)).indicator (fun _ => (1:ℂ))) 2 volume := by
    apply h.mono ((measurable_const.indicator measurableSet_Ici).aestronglyMeasurable)
    filter_upwards with t
    by_cases ht : 0≤t
    · rw [indicator_of_mem (show t∈Ici (0:ℝ) from ht),syntheticDampedInput_formula epsilon t ht,
        norm_one,Complex.norm_exp]
      simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg (sub_pos.mpr hepsilon).le ht
    · rw [indicator_of_notMem (show t∉Ici (0:ℝ) from ht),norm_zero]
      exact norm_nonneg _
  have hlt := hOne.2
  rw [eLpNorm_indicator_const measurableSet_Ici (by norm_num) (by norm_num)] at hlt
  norm_num [Real.volume_Ici] at hlt

theorem syntheticDampedOutput_laplace (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    CCM.nativeCausalLaplaceMoment (syntheticUnstableLambda-(epsilon:ℂ)) 0
      (syntheticDampedOutput epsilon hepsilon:ProbeL2)=
      (1/4:ℂ)/(syntheticUnstableLambda+1) := by
  rw [← syntheticStableOutput_laplace]
  unfold CCM.nativeCausalLaplaceMoment
  simp only [pow_zero,one_mul]
  apply integral_congr_ae
  filter_upwards [syntheticDampedOutput_coe epsilon hepsilon,syntheticStableOutput_coe] with t ht hy
  rw [ht,hy,syntheticDampedPhysical,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem synthetic_damped_range_annihilated (epsilon : ℝ) (hepsilon : 0≤epsilon)
    (hsmall : epsilon<syntheticUnstableLambda.re) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment (syntheticUnstableLambda-(epsilon:ℂ)) 0
      (syntheticDampedOperator epsilon hepsilon f:ProbeL2)=0 := by
  have hp : 0<(syntheticUnstableLambda-(epsilon:ℂ)).re := by simp; linarith
  have hz : syntheticMinusMultiplier syntheticUnstableLambda=0 := synthetic_minus_right_zeros 4
  rw [syntheticDampedOperator,causalKernelOperator_laplace _
    (syntheticDampedKernel_integrable epsilon hepsilon) (syntheticDampedKernel_zero_negative epsilon) _ hp,
    syntheticDampedKernel_laplace epsilon hepsilon _ hp.le,sub_add_cancel,
    hz,zero_mul]

theorem synthetic_damped_closure_annihilated (epsilon : ℝ) (hepsilon : 0≤epsilon)
    (hsmall : epsilon<syntheticUnstableLambda.re) {g : CausalProbeL2}
    (hg : g∈closure (Set.range (syntheticDampedOperator epsilon hepsilon))) :
    CCM.nativeCausalLaplaceMoment (syntheticUnstableLambda-(epsilon:ℂ)) 0 (g:ProbeL2)=0 := by
  have hp : 0<(syntheticUnstableLambda-(epsilon:ℂ)).re := by simp; linarith
  let u := CCM.nativeCausalExponentialWitness _ hp 0
  have hc : IsClosed {g : CausalProbeL2 | inner ℂ u g=0} := isClosed_eq (by fun_prop) continuous_const
  have hs : Set.range (syntheticDampedOperator epsilon hepsilon) ⊆ {g : CausalProbeL2 | inner ℂ u g=0} := by
    rintro _ ⟨f,rfl⟩
    change inner ℂ (CCM.nativeCausalExponentialWitness _ hp 0) (syntheticDampedOperator epsilon hepsilon f)=0
    rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment]
    exact synthetic_damped_range_annihilated epsilon hepsilon hsmall f
  have h := closure_minimal hs hc hg
  change inner ℂ (CCM.nativeCausalExponentialWitness _ hp 0) g=0 at h
  rwa [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment] at h

theorem synthetic_damped_output_separation (epsilon : ℝ) (hepsilon : 0≤epsilon)
    (hsmall : epsilon<syntheticUnstableLambda.re) {g : CausalProbeL2}
    (hg : g∈closure (Set.range (syntheticDampedOperator epsilon hepsilon))) :
    Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      ‖syntheticDampedOutput epsilon hepsilon-g‖ := by
  have hp : 0<(syntheticUnstableLambda-(epsilon:ℂ)).re := by simp; linarith
  have hb := probe_laplace_evaluation_bound _ hp (syntheticDampedOutput epsilon hepsilon-g)
  have hm : CCM.nativeCausalLaplaceMoment (syntheticUnstableLambda-(epsilon:ℂ)) 0
      ((syntheticDampedOutput epsilon hepsilon-g:CausalProbeL2):ProbeL2)=
      (1/4:ℂ)/(syntheticUnstableLambda+1) := by
    rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0,inner_sub_right,
      CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
      syntheticDampedOutput_laplace,synthetic_damped_closure_annihilated epsilon hepsilon hsmall hg,sub_zero]
  rw [hm] at hb
  simpa using hb

def syntheticFullEPhysical (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ,(syntheticExponential s:ℂ)*f (t-s)

theorem syntheticFullEPhysical_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (syntheticFullEPhysical f) :=
  synthetic_exponential_integrable.ofReal.integrable_convolution (L:=ContinuousLinearMap.mul ℂ ℂ) hf

theorem syntheticFullE_coeFn_of_representative (f : ProbeL2) (g : ℝ → ℂ)
    (hfg : f=ᵐ[volume] g) : syntheticFullE f=ᵐ[volume] syntheticFullEPhysical g := by
  have hk := kernelL2Operator_coeFn_pointwise syntheticExponential synthetic_exponential_integrable
    synthetic_exponential_measurable synthetic_exponential_memLp f
  apply hk.trans
  filter_upwards with t
  apply integral_congr_ae
  have h := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae_eq hfg
  filter_upwards [h] with s hs
  dsimp only [Function.comp_def] at hs
  rw [hs]

theorem syntheticFullEPhysical_logFourier {f : ℝ → ℂ} (hf : Integrable f) (tau : ℝ) :
    OPICAFollowup.logFourier (syntheticFullEPhysical f) tau=
      (1/((tau:ℂ)*Complex.I+1))*OPICAFollowup.logFourier f tau := by
  have hfun (g : ℝ → ℂ) :
      (fun t : ℝ => Complex.exp (-((tau:ℂ)*Complex.I)*(t:ℂ))*g t)=
      (fun t : ℝ => Complex.exp (-((tau*t:ℝ):ℂ)*Complex.I)*g t) := by
    funext t
    congr 2
    push_cast
    ring
  have hconvert (g : ℝ → ℂ) : probeLaplace g ((tau:ℂ)*Complex.I)=OPICAFollowup.logFourier g tau := by
    unfold probeLaplace OPICAFollowup.logFourier
    rw [hfun]
  have hk := CCM.nativeCausalComplexDamping_integrable (w:=(tau:ℂ)*Complex.I) (by simp)
    synthetic_exponential_integrable synthetic_exponential_zero_negative
  have hfd : Integrable (fun t : ℝ => Complex.exp (-((tau:ℂ)*Complex.I)*(t:ℂ))*f t) := by
    rw [hfun]
    exact probeFourierDamping_integrable hf tau
  have he := (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t => (syntheticExponential t:ℂ)) f ((tau:ℂ)*Complex.I) hk hfd).2
  change probeLaplace (syntheticFullEPhysical f) ((tau:ℂ)*Complex.I)=
    probeLaplace (fun t => (syntheticExponential t:ℂ)) ((tau:ℂ)*Complex.I)*
      probeLaplace f ((tau:ℂ)*Complex.I) at he
  rw [synthetic_exponential_laplace (by simp),hconvert,hconvert] at he
  exact he

theorem synthetic_exponential_derivative_inverse (phi : SchwartzMap ℝ ℂ) :
    syntheticFullE ((SchwartzMap.derivCLM ℂ ℂ phi+phi).toLp 2 (volume:Measure ℝ))=
      phi.toLp 2 (volume:Measure ℝ) := by
  let dphi : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ phi
  let f : SchwartzMap ℝ ℂ := dphi+phi
  let F : ProbeL2 := f.toLp 2 (volume:Measure ℝ)
  have hrep := syntheticFullE_coeFn_of_representative F f (f.coeFn_toLp 2 volume)
  have hE2 : MemLp (syntheticFullEPhysical f) 2 volume := MemLp.ae_eq hrep (Lp.memLp (syntheticFullE F))
  have hFT (tau : ℝ) : OPICAFollowup.logFourier (syntheticFullEPhysical f) tau=
      OPICAFollowup.logFourier phi tau := by
    rw [syntheticFullEPhysical_logFourier f.integrable tau]
    have hAdd : OPICAFollowup.logFourier f tau=
        OPICAFollowup.logFourier (fun t => deriv (phi:ℝ → ℂ) t) tau+
        OPICAFollowup.logFourier phi tau := by
      change (∫ t : ℝ,Complex.exp (-((tau*t:ℝ):ℂ)*Complex.I)*(dphi t+phi t))=_
      simp_rw [mul_add]
      rw [integral_add (probeFourierDamping_integrable dphi.integrable tau)
        (probeFourierDamping_integrable phi.integrable tau)]
      congr 1
    have hd : Integrable (deriv (phi:ℝ → ℂ)) := by
      apply dphi.integrable.congr
      exact Eventually.of_forall fun t => SchwartzMap.derivCLM_apply ℂ phi t
    rw [hAdd,OPICAFollowup.logFourier_deriv phi.integrable phi.differentiable hd tau]
    have hn : (tau:ℂ)*Complex.I+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
    field_simp
    <;> ring
  have heq := probeL1L2Fourier_ext (syntheticFullEPhysical f) phi
    (syntheticFullEPhysical_integrable f.integrable) phi.integrable hE2 (phi.memLp 2 volume) hFT
  apply Lp.ext
  filter_upwards [hrep,heq,phi.coeFn_toLp 2 volume] with t ht he hphi
  rw [ht,he,← hphi]

theorem syntheticUnstableLambda_literal : syntheticUnstableLambda=
    (Real.log (3/2):ℂ)+9*Real.pi*Complex.I := by
  simp only [syntheticUnstableLambda,syntheticRightZero]
  norm_num

theorem synthetic_output_distance :
    Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      Metric.infDist syntheticStableOutput (closure (Set.range syntheticMinusOperator)) := by
  apply (Metric.le_infDist (show (closure (Set.range syntheticMinusOperator)).Nonempty from
    ⟨0,subset_closure ⟨0,by simp⟩⟩)).mpr
  intro g hg
  simpa only [dist_eq_norm] using synthetic_output_separation hg

theorem synthetic_damped_output_distance (epsilon : ℝ) (hepsilon : 0≤epsilon)
    (hsmall : epsilon<syntheticUnstableLambda.re) :
    0<Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ ∧
    Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      Metric.infDist (syntheticDampedOutput epsilon hepsilon)
        (closure (Set.range (syntheticDampedOperator epsilon hepsilon))) := by
  constructor
  · apply mul_pos (Real.sqrt_pos.mpr (by linarith))
    have hp := synthetic_right_zero_positive 4
    change 0<syntheticUnstableLambda.re at hp
    apply norm_pos_iff.mpr
    apply div_ne_zero (by norm_num)
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  · apply (Metric.le_infDist (show (closure (Set.range (syntheticDampedOperator epsilon hepsilon))).Nonempty from
      ⟨0,subset_closure ⟨0,by simp⟩⟩)).mpr
    intro g hg
    simpa only [dist_eq_norm] using synthetic_damped_output_separation epsilon hepsilon hsmall hg

theorem synthetic_small_operator_inverse_control :
    IsUnit ((1:CausalProbeL2 →L[ℂ] CausalProbeL2)-syntheticMinusOperator) ∧
      ¬IsUnit syntheticMinusOperator := by
  constructor
  · apply isUnit_one_sub_of_norm_lt_one (R:=CausalProbeL2 →L[ℂ] CausalProbeL2)
    exact synthetic_twins_contractions.1.trans_lt (by norm_num)
  · intro hu
    have hs := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2
    exact synthetic_minus_not_dense_causal_range hs.denseRange

/-- The exact five-clause synthetic control. The native arithmetic operator is
not substituted anywhere in this statement. -/
theorem positive_equal_power_causal_twins :
    (∀ t : ℝ, 0≤syntheticMinusKernel t ∧ 0≤syntheticPlusKernel t ∧
      syntheticMinusKernel t≤Real.exp (-t/2) ∧ syntheticPlusKernel t≤Real.exp (-t/2)) ∧
    ((∫ t : ℝ,syntheticMinusKernel t)=(5/8:ℝ) ∧ (∫ t : ℝ,syntheticPlusKernel t)=(5/8:ℝ)) ∧
    (‖syntheticMinusOperator‖≤(5/8:ℝ) ∧ ‖syntheticPlusOperator‖≤(5/8:ℝ)) ∧
    (∀ z : ℂ, 0≤z.re →
      probeLaplace (fun t => (syntheticMinusKernel t:ℂ)) z=(1+(3/2:ℂ)*Complex.exp (-z))/(4*(z+1)) ∧
      probeLaplace (fun t => (syntheticPlusKernel t:ℂ)) z=((3/2:ℂ)+Complex.exp (-z))/(4*(z+1))) ∧
    (∀ xi : ℝ, ‖syntheticMinusMultiplier ((xi:ℂ)*Complex.I)‖^2=(13+12*Real.cos xi)/(64*(1+xi^2)) ∧
      ‖syntheticPlusMultiplier ((xi:ℂ)*Complex.I)‖^2=(13+12*Real.cos xi)/(64*(1+xi^2))) ∧
    ((ContinuousLinearMap.adjoint syntheticMinusOperator).comp syntheticMinusOperator=
      (ContinuousLinearMap.adjoint syntheticPlusOperator).comp syntheticPlusOperator) ∧
    (IsUnit syntheticPlusFactor ∧ ∀ phi : SchwartzMap ℝ ℂ,
      syntheticFullE ((SchwartzMap.derivCLM ℂ ℂ phi+phi).toLp 2 (volume:Measure ℝ))=
        phi.toLp 2 (volume:Measure ℝ)) ∧
    (DenseRange syntheticPlusOperator ∧ ¬DenseRange syntheticMinusOperator ∧
      closure (Set.range syntheticMinusOperator)≠closure (Set.range syntheticPlusOperator)) ∧
    (∀ k : ℤ, 0<(syntheticRightZero k).re ∧ syntheticMinusMultiplier (syntheticRightZero k)=0) ∧
    (¬MemLp syntheticUnstableInput 2 volume ∧
      (∀ t : ℝ, syntheticLocalCompletion t=syntheticStablePhysical t) ∧
      ((syntheticStableOutput:ProbeL2)=ᵐ[volume] syntheticStablePhysical) ∧
      syntheticUnstableLambda=(Real.log (3/2):ℂ)+9*Real.pi*Complex.I ∧
      (∀ t : ℝ, 0≤t → t<1 → syntheticStablePhysical t=(1/4:ℂ)*
        (Complex.exp (syntheticUnstableLambda*(t:ℂ))-Complex.exp (-(t:ℂ)))/(syntheticUnstableLambda+1)) ∧
      (∀ t : ℝ, 1≤t → syntheticStablePhysical t=-(1/4:ℂ)*(1+(3/2)*Complex.exp 1)*
        Complex.exp (-(t:ℂ))/(syntheticUnstableLambda+1)) ∧
      CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0 (syntheticStableOutput:ProbeL2)=
        (1/4:ℂ)/(syntheticUnstableLambda+1) ∧
      0<Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ ∧
      Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
        Metric.infDist syntheticStableOutput (closure (Set.range syntheticMinusOperator))) ∧
    ((∀ xi : ℝ, syntheticMinusMultiplier ((xi:ℂ)*Complex.I)≠0 ∧
      syntheticPlusMultiplier ((xi:ℂ)*Complex.I)≠0) ∧
      DenseRange syntheticFullMinusOperator ∧ DenseRange syntheticFullPlusOperator) ∧
    (∀ epsilon : ℝ, ∀ hepsilon : 0≤epsilon, epsilon<syntheticUnstableLambda.re →
      ¬MemLp (syntheticDampedInput epsilon) 2 volume ∧
      (∀ t : ℝ, (∫ s : ℝ,(syntheticDampedKernel epsilon s:ℂ)*syntheticDampedInput epsilon (t-s))=
        syntheticDampedPhysical epsilon t) ∧
      ((syntheticDampedOutput epsilon hepsilon:ProbeL2)=ᵐ[volume] syntheticDampedPhysical epsilon) ∧
      0<Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ ∧
      Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
        Metric.infDist (syntheticDampedOutput epsilon hepsilon)
          (closure (Set.range (syntheticDampedOperator epsilon hepsilon)))) := by
  refine ⟨?_,synthetic_twins_mass,synthetic_twins_contractions,?_,synthetic_boundary_power,
    synthetic_twins_equal_power,?_,?_,?_,?_,?_,?_⟩
  · intro t
    exact ⟨(synthetic_twins_nonneg t).1,(synthetic_twins_nonneg t).2,
      (synthetic_twins_dominating_exponential t).1,(synthetic_twins_dominating_exponential t).2⟩
  · intro z hz
    exact synthetic_twins_laplace hz
  · exact ⟨syntheticPlusFactor_isUnit,synthetic_exponential_derivative_inverse⟩
  · exact ⟨synthetic_plus_dense_causal_range,synthetic_minus_not_dense_causal_range,
      synthetic_causal_range_closures_differ⟩
  · intro k
    exact ⟨synthetic_right_zero_positive k,synthetic_minus_right_zeros k⟩
  · exact ⟨synthetic_unstable_input_not_memLp,syntheticLocalCompletion_eq_output,
      syntheticStableOutput_coe,syntheticUnstableLambda_literal,
      fun _ h0 h1 => syntheticStablePhysical_first h0 h1,
      fun _ h => syntheticStablePhysical_tail h,syntheticStableOutput_laplace,
      synthetic_output_separation_positive,synthetic_output_distance⟩
  · exact ⟨synthetic_boundary_multipliers_nonzero,synthetic_full_twins_dense_ranges⟩
  · intro epsilon hepsilon hsmall
    exact ⟨synthetic_damped_input_not_memLp epsilon hsmall,synthetic_damped_local_completion epsilon,
      syntheticDampedOutput_coe epsilon hepsilon,
      (synthetic_damped_output_distance epsilon hepsilon hsmall).1,
      (synthetic_damped_output_distance epsilon hepsilon hsmall).2⟩

#print axioms Zeta23.OPICARound2.positive_equal_power_causal_twins

end Zeta23.OPICARound2
