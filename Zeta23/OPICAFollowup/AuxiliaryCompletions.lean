import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Complex.Convex
import Zeta23.OPICA.WeightedLaplace
import Zeta23.OPICAFollowup.NativeSourceTransforms
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.CCM

def auxCompletionFilter (k : ℕ) (t : ℝ) : ℝ :=
  if 0≤t then
    Real.exp (-((k:ℝ)+3/2)*t)*(1-Real.exp (-t))^k/(Nat.factorial (k+1):ℝ)*
      (((2*k+3:ℕ):ℝ)*Real.exp (-t)-(k+2:ℕ))
  else 0

def auxCompletionPrimitive (k : ℕ) (t : ℝ) : ℝ :=
  if 0≤t then
    Real.exp (-((k:ℝ)+3/2)*t)*(1-Real.exp (-t))^(k+1)/(Nat.factorial (k+1):ℝ)
  else 0

def auxCompletionKernel (k : ℕ) : ℝ → ℝ := nativeIntegerTranslateAction (auxCompletionFilter k)

def auxRationalFactor (k : ℕ) (z : ℂ) : ℂ :=
  (z-1/2)/(∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2))

def auxCompletionAlpha (k : ℕ) : ℝ := (k:ℝ)+1/2

def auxCompletionBound (k : ℕ) : ℝ :=
  2*(riemannZeta (k+1:ℕ)).re*(1+2^(3*k+4):ℝ)/(2*Real.pi)^(k+1)

theorem auxCompletionFilter_zero_before (k : ℕ) {t : ℝ} (ht : t<0) :
    auxCompletionFilter k t=0 := by simp only [auxCompletionFilter,not_le.mpr ht,ite_false]

theorem auxCompletionPrimitive_zero (k : ℕ) : auxCompletionPrimitive k 0=0 := by
  simp [auxCompletionPrimitive]

theorem auxCompletionFilter_measurable (k : ℕ) : Measurable (auxCompletionFilter k) := by
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem auxCompletionFilter_abs_bound (k : ℕ) {t : ℝ} (ht : 0≤t) :
    |auxCompletionFilter k t| ≤
      ((k+2:ℕ):ℝ)/(Nat.factorial (k+1):ℝ)*Real.exp (-((k:ℝ)+3/2)*t) := by
  have he0 : 0≤Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 0≤(1-Real.exp (-t))^k := pow_nonneg (by linarith) _
  have hp1 : (1-Real.exp (-t))^k≤1 := pow_le_one₀ (by linarith) (by linarith)
  have hb : |((2*k+3:ℕ):ℝ)*Real.exp (-t)-(k+2:ℕ)|≤((k+2:ℕ):ℝ) := by
    apply abs_le.mpr
    push_cast
    constructor <;> nlinarith
  rw [auxCompletionFilter,if_pos ht,abs_mul,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hp,abs_of_pos (by positivity : 0<(Nat.factorial (k+1):ℝ))]
  calc
    _ ≤ (Real.exp (-((k:ℝ)+3/2)*t)*1/(Nat.factorial (k+1):ℝ))*((k+2:ℕ):ℝ) :=
      mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 (Real.exp_pos _).le)
        (by positivity)) hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

def auxBetaIntegrand (A : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-A*(t:ℂ))*Complex.ofReal ((1-Real.exp (-t))^n)

def auxBetaLaplace (A : ℂ) (n : ℕ) : ℂ := ∫ t : ℝ in Ioi 0, auxBetaIntegrand A n t

theorem auxBetaIntegrand_norm_le (A : ℂ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    ‖auxBetaIntegrand A n t‖ ≤ Real.exp (-A.re*t) := by
  have he : 0≤1-Real.exp (-t) ∧ 1-Real.exp (-t)≤1 := by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-t)]
  unfold auxBetaIntegrand
  rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg he.1 n)]
  have hre : (-A*(t:ℂ)).re = -A.re*t := by simp
  rw [hre]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ he.1 he.2)

theorem auxBetaIntegrand_integrable {A : ℂ} (hA : 0<A.re) (n : ℕ) :
    IntegrableOn (auxBetaIntegrand A n) (Ioi 0) := by
  apply (integrableOn_exp_mul_Ioi (by linarith : -A.re<0) 0).mono'
    ((by unfold auxBetaIntegrand; fun_prop : Continuous (auxBetaIntegrand A n)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact auxBetaIntegrand_norm_le A n (le_of_lt ht)

theorem auxBetaIntegrand_tendsto_zero {A : ℂ} (hA : 0<A.re) (n : ℕ) :
    Tendsto (auxBetaIntegrand A n) atTop (𝓝 0) := by
  have hx : Tendsto (fun t : ℝ => -A.re*t) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -A.re<0)).2 tendsto_id
  exact squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact auxBetaIntegrand_norm_le A n ht) (Real.tendsto_exp_atBot.comp hx)

set_option backward.isDefEq.respectTransparency.types false in
theorem auxBetaIntegrand_hasDerivAt (A : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (auxBetaIntegrand A (n+1))
      (-A*auxBetaIntegrand A (n+1) t+(n+1:ℕ)*auxBetaIntegrand (A+1) n t) t := by
  have hu : HasDerivAt (fun t : ℝ => Complex.exp (-A*(t:ℂ)))
      (-A*Complex.exp (-A*(t:ℂ))) t := by
    convert (((hasDerivAt_id (t:ℂ)).const_mul (-A)).cexp).comp_ofReal using 1 <;>
      simp only [id_eq,mul_one,mul_comm]
  have hv : HasDerivAt (fun t : ℝ => 1-Real.exp (-t)) (Real.exp (-t)) t := by
    simpa only [mul_neg,mul_one,neg_neg] using ((hasDerivAt_neg t).exp).const_sub 1
  have hp := (hv.pow (n+1)).ofReal_comp
  have h := hu.mul hp
  have hExp : Complex.exp (-(A+1)*(t:ℂ))=
      Complex.exp (-A*(t:ℂ))*Complex.exp (-(t:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  have hraw : HasDerivAt (auxBetaIntegrand A (n+1))
      (-A*Complex.exp (-A*(t:ℂ))*Complex.ofReal ((1-Real.exp (-t))^(n+1))+
        Complex.exp (-A*(t:ℂ))*Complex.ofReal (((n+1:ℕ):ℝ)*(1-Real.exp (-t))^n*Real.exp (-t))) t := by
    convert h using 1 <;> rfl
  convert hraw using 1
  dsimp [auxBetaIntegrand]
  rw [hExp,←Complex.ofReal_neg,←Complex.ofReal_exp]
  push_cast
  ring

theorem auxBetaLaplace_zero {A : ℂ} (hA : 0<A.re) : auxBetaLaplace A 0=1/A := by
  unfold auxBetaLaplace auxBetaIntegrand
  simp only [pow_zero,Complex.ofReal_one,mul_one]
  rw [integral_exp_mul_complex_Ioi (show (-A).re<0 by simp; linarith)]
  simp

theorem auxBetaLaplace_recurrence {A : ℂ} (hA : 0<A.re) (n : ℕ) :
    A*auxBetaLaplace A (n+1)=(n+1:ℕ)*auxBetaLaplace (A+1) n := by
  have hA1 : 0<(A+1).re := by simp; linarith
  have hfirst := (auxBetaIntegrand_integrable hA (n+1)).const_mul (-A)
  have hsecond := (auxBetaIntegrand_integrable hA1 n).const_mul ((n+1:ℕ):ℂ)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (_ht : t∈Ici (0:ℝ)) => auxBetaIntegrand_hasDerivAt A n t)
    (hfirst.add hsecond) (auxBetaIntegrand_tendsto_zero hA (n+1))
  have h0 : auxBetaIntegrand A (n+1) 0=0 := by simp [auxBetaIntegrand]
  rw [h0,sub_zero,integral_add hfirst hsecond,integral_const_mul,integral_const_mul] at hval
  change -A*auxBetaLaplace A (n+1)+((n+1:ℕ):ℂ)*auxBetaLaplace (A+1) n=0 at hval
  linear_combination -hval

theorem auxBetaProduct_ne_zero {A : ℂ} (hA : 0<A.re) (n : ℕ) :
    (∏ j ∈ Finset.range (n+1), (A+(j:ℂ))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _hj hzero
  have h := congrArg Complex.re hzero
  simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at h
  have hnonneg : 0≤(j:ℝ) := Nat.cast_nonneg _
  linarith

theorem auxBetaLaplace_eval {A : ℂ} (hA : 0<A.re) (n : ℕ) :
    auxBetaLaplace A n=(Nat.factorial n:ℂ)/(∏ j ∈ Finset.range (n+1), (A+(j:ℂ))) := by
  induction n generalizing A with
  | zero => simpa using auxBetaLaplace_zero hA
  | succ n ih =>
    have hA1 : 0<(A+1).re := by simp; linarith
    have hAz : A≠0 := by intro he; rw [he] at hA; norm_num at hA
    have hP := auxBetaProduct_ne_zero hA1 n
    have hprod : (∏ j ∈ Finset.range (n+1+1), (A+(j:ℂ)))=
        A*(∏ j ∈ Finset.range (n+1), ((A+1)+(j:ℂ))) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero,add_zero]
      rw [mul_comm _ A]
      congr 1
      apply Finset.prod_congr rfl
      intro j _hj
      push_cast
      ring
    apply mul_left_cancel₀ hAz
    rw [auxBetaLaplace_recurrence hA n,ih hA1,hprod,Nat.factorial_succ]
    push_cast
    field_simp

theorem auxCompletionFilter_damped_eq_beta (k : ℕ) (z : ℂ) {t : ℝ} (ht : 0≤t) :
    Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)=
      (((k+1:ℕ):ℂ)*auxBetaIntegrand (z+((k:ℂ)+3/2)+1) k t-
        ((k+2:ℕ):ℂ)*auxBetaIntegrand (z+((k:ℂ)+3/2)) (k+1) t)/(Nat.factorial (k+1):ℂ) := by
  have hshift : Complex.exp (-(z+((k:ℂ)+3/2)+1)*(t:ℂ))=
      Complex.exp (-(z+((k:ℂ)+3/2))*(t:ℂ))*Complex.exp (-(t:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  have hbase : Complex.exp (-z*(t:ℂ))*Complex.exp (-((k:ℂ)+3/2)*(t:ℂ))=
      Complex.exp (-(z+((k:ℂ)+3/2))*(t:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  rw [auxCompletionFilter,if_pos ht]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_sub,
    Complex.ofReal_exp,auxBetaIntegrand]
  push_cast
  rw [hshift,←hbase,pow_succ]
  ring

theorem auxCompletionFilter_integrable_laplace (k : ℕ) {z : ℂ}
    (hz : -((k:ℝ)+3/2)<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t))=auxRationalFactor k z := by
  let A : ℂ := z+((k:ℂ)+3/2)
  have hA : 0<A.re := by dsimp [A]; norm_num; linarith
  have hA1 : 0<(A+1).re := by simp; linarith
  have hfirst := (auxBetaIntegrand_integrable hA1 k).const_mul ((k+1:ℕ):ℂ)
  have hsecond := (auxBetaIntegrand_integrable hA (k+1)).const_mul ((k+2:ℕ):ℂ)
  have hcombo := (hfirst.sub hsecond).div_const (Nat.factorial (k+1):ℂ)
  have hIoi : IntegrableOn (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)) (Ioi 0) := by
    apply Integrable.congr hcombo
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (auxCompletionFilter_damped_eq_beta k z ht.le).symm
  have hzero (t : ℝ) (ht : t∉Ici (0:ℝ)) :
      Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)=0 := by
    rw [auxCompletionFilter_zero_before k (lt_of_not_ge ht),Complex.ofReal_zero,mul_zero]
  constructor
  · exact IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hIoi) hzero
  · rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero,integral_Ici_eq_integral_Ioi]
    have heq : (∫ t : ℝ in Ioi 0, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t))=
        (((k+1:ℕ):ℂ)*auxBetaLaplace (A+1) k-((k+2:ℕ):ℂ)*auxBetaLaplace A (k+1))/(Nat.factorial (k+1):ℂ) := by
      calc
        _ = ∫ t : ℝ in Ioi 0, (((k+1:ℕ):ℂ)*auxBetaIntegrand (A+1) k t-
            ((k+2:ℕ):ℂ)*auxBetaIntegrand A (k+1) t)/(Nat.factorial (k+1):ℂ) :=
          setIntegral_congr_fun measurableSet_Ioi (fun t ht => auxCompletionFilter_damped_eq_beta k z ht.le)
        _ = _ := by rw [integral_div,integral_sub hfirst hsecond,integral_const_mul,integral_const_mul]; rfl
    rw [heq,←auxBetaLaplace_recurrence hA k,auxBetaLaplace_eval hA (k+1)]
    have hfact : (Nat.factorial (k+1):ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (k+1)
    have hprod : (∏ j ∈ Finset.range (k+1+1), (A+(j:ℂ)))=
        (∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2)) := by
      apply Finset.prod_congr rfl
      intro j _hj
      dsimp [A]
      push_cast
      ring
    have hP := auxBetaProduct_ne_zero hA (k+1)
    rw [hprod] at hP ⊢
    unfold auxRationalFactor
    dsimp [A]
    push_cast
    field_simp
    ring

theorem auxCompletionKernel_zero_before (k : ℕ) {t : ℝ} (ht : t<0) :
    auxCompletionKernel k t=0 := by
  unfold auxCompletionKernel nativeIntegerTranslateAction
  have hzero (n : ℕ) : nativeIntegerCoefficient n*auxCompletionFilter k (t-Real.log n)=0 := by
    rw [auxCompletionFilter_zero_before k (by linarith [Real.log_natCast_nonneg n]),mul_zero]
  simp only [hzero,tsum_zero]

theorem auxCompletionKernel_measurable (k : ℕ) : Measurable (auxCompletionKernel k) :=
  Measurable.tsum (fun n => measurable_const.mul
    ((auxCompletionFilter_measurable k).comp (by fun_prop)))

theorem auxCompletionKernel_initial_laplace (k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t))=
      auxRationalFactor k z*riemannZeta (z+1/2) := by
  have hfilter := auxCompletionFilter_integrable_laplace k (z := z) (by
    have hk : 0≤(k:ℝ) := Nat.cast_nonneg _
    linarith)
  have h := complexWeightedTranslate_integrable_laplace
    (fun n => (nativeIntegerCoefficient n:ℂ)) (fun t => Complex.ofReal (auxCompletionFilter k t)) z
    hfilter.1 (nativeIntegerLaplaceCoefficient_summable_norm hz)
  have hcast (t : ℝ) : Complex.ofReal (auxCompletionKernel k t)=
      ∑' n : ℕ, (nativeIntegerCoefficient n:ℂ)*Complex.ofReal (auxCompletionFilter k (t-Real.log n)) := by
    simp only [auxCompletionKernel,nativeIntegerTranslateAction,Complex.ofReal_tsum,Complex.ofReal_mul]
  simp_rw [←hcast] at h
  refine ⟨h.1,?_⟩
  rw [show (∑' n : ℕ, (nativeIntegerCoefficient n:ℂ)*Complex.exp (-z*(Real.log n:ℂ)))=
    riemannZeta (z+1/2) from nativeIntegerLaplaceCoefficient_tsum hz,hfilter.2] at h
  exact h.2.trans (mul_comm _ _)

theorem auxCompletionFilter_integrable (k : ℕ) : Integrable (auxCompletionFilter k) := by
  let K : ℝ := ((k+2:ℕ):ℝ)/(Nat.factorial (k+1):ℝ)
  let a : ℝ := (k:ℝ)+3/2
  have ha : 0<a := by dsimp [a]; positivity
  have hdom : IntegrableOn (fun t : ℝ => K*Real.exp (-a*t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -a<0) 0).const_mul K)
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ici 0) ?_
    (fun t ht => auxCompletionFilter_zero_before k (lt_of_not_ge ht))
  apply hdom.mono' (auxCompletionFilter_measurable k).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact auxCompletionFilter_abs_bound k ht

theorem auxCompletionFilter_L1_bound (k : ℕ) :
    (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) := by
  let K : ℝ := ((k+2:ℕ):ℝ)/(Nat.factorial (k+1):ℝ)
  let a : ℝ := (k:ℝ)+3/2
  have ha : 0<a := by dsimp [a]; positivity
  have hdom : IntegrableOn (fun t : ℝ => K*Real.exp (-a*t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -a<0) 0).const_mul K)
  have hF := hdom.integrable_indicator measurableSet_Ici
  have hbound : (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤
      ∫ t : ℝ, (Ici (0:ℝ)).indicator (fun t : ℝ => K*Real.exp (-a*t)) t := by
    apply integral_mono (auxCompletionFilter_integrable k).norm hF
    intro t
    change ‖auxCompletionFilter k t‖≤_
    by_cases ht : 0≤t
    · rw [indicator_of_mem (show t∈Ici (0:ℝ) from ht),Real.norm_eq_abs]
      exact auxCompletionFilter_abs_bound k ht
    · rw [indicator_of_notMem (show t∉Ici (0:ℝ) from ht),
        auxCompletionFilter_zero_before k (lt_of_not_ge ht),norm_zero]
  have hint : (∫ t : ℝ, (Ici (0:ℝ)).indicator (fun t : ℝ => K*Real.exp (-a*t)) t)=K/a := by
    rw [integral_indicator measurableSet_Ici,integral_const_mul,integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (by linarith : -a<0)]
    simp [div_eq_mul_inv]
  rw [hint] at hbound
  apply hbound.trans
  have hb : ((k+2:ℕ):ℝ)≤2*a := by dsimp [a]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ = ((((k+2:ℕ):ℝ)/a)/(Nat.factorial (k+1):ℝ)) := by dsimp [K]; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ ha).mpr hb) (by positivity)

open Polynomial

def auxProfilePolynomial (k : ℕ) : Polynomial ℝ :=
  C ((Nat.factorial (k+1):ℝ)⁻¹)*X^(k+1)*(1-X)^k*
    (C ((2*k+3:ℕ):ℝ)*X-C ((k+2:ℕ):ℝ))

def auxProfilePrimitivePolynomial (k : ℕ) : Polynomial ℝ :=
  C ((Nat.factorial (k+1):ℝ)⁻¹)*X^(k+2)*(1-X)^(k+1)

def auxCompletionProfile (k : ℕ) (u : ℝ) : ℝ :=
  if u∈Icc (0:ℝ) 1 then (auxProfilePolynomial k).eval u else 0

theorem auxProfilePolynomial_eval (k : ℕ) (u : ℝ) :
    (auxProfilePolynomial k).eval u=
      u^(k+1)*(1-u)^k*(((2*k+3:ℕ):ℝ)*u-(k+2:ℕ))/(Nat.factorial (k+1):ℝ) := by
  simp only [auxProfilePolynomial,eval_mul,eval_C,eval_pow,eval_X,eval_sub,eval_one]
  ring

theorem auxProfilePolynomial_eq_neg_derivative (k : ℕ) :
    auxProfilePolynomial k=-(auxProfilePrimitivePolynomial k).derivative := by
  simp only [auxProfilePolynomial,auxProfilePrimitivePolynomial,derivative_mul,
    derivative_C,zero_mul,zero_add,derivative_pow,derivative_X,derivative_sub,
    derivative_one,zero_sub,Nat.add_sub_cancel,mul_one]
  rw [show k+2-1=k+1 by omega]
  rw [show X^(k+2)=(X:Polynomial ℝ)^(k+1)*X by rw [show k+2=(k+1)+1 by omega,pow_succ]]
  rw [pow_succ (1-X) k]
  push_cast
  simp only [Polynomial.C_add,Polynomial.C_mul,Polynomial.C_ofNat,Polynomial.C_1]
  ring

theorem auxProfilePolynomial_zero (k : ℕ) : (auxProfilePolynomial k).eval 0=0 := by
  rw [auxProfilePolynomial_eval]
  simp

theorem auxProfilePolynomial_one (k : ℕ) (hk : 1≤k) : (auxProfilePolynomial k).eval 1=0 := by
  rw [auxProfilePolynomial_eval]
  simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)]

theorem polynomial_one_sub_X_derivative_eval_one (n j : ℕ) :
    (Polynomial.derivative^[j] ((1-X)^n:Polynomial ℝ)).eval 1=
      (-1:ℝ)^j*(Nat.descFactorial n j:ℝ)*0^(n-j) := by
  have he : ((1-X)^n:Polynomial ℝ)=((X:Polynomial ℝ)^n).comp (1-X) := by simp
  rw [he,Polynomial.iterate_derivative_comp_one_sub_X,Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp
  ring

theorem auxProfilePolynomial_derivative_zero (k j : ℕ) (hj : j≤k) :
    (Polynomial.derivative^[j] (auxProfilePolynomial k)).eval 0=0 := by
  have hdiv : (X:Polynomial ℝ)^(k+1)∣auxProfilePolynomial k := by
    refine ⟨C ((Nat.factorial (k+1):ℝ)⁻¹)*(1-X)^k*
      (C ((2*k+3:ℕ):ℝ)*X-C ((k+2:ℕ):ℝ)),?_⟩
    unfold auxProfilePolynomial
    ring
  obtain ⟨q,hq⟩ := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j hdiv
  rw [hq,eval_mul,eval_pow,eval_X,zero_pow (show k+1-j≠0 by omega),zero_mul]

theorem auxProfilePolynomial_derivative_one_vanish (k j : ℕ) (hj : j<k) :
    (Polynomial.derivative^[j] (auxProfilePolynomial k)).eval 1=0 := by
  have hdiv : ((1-X):Polynomial ℝ)^k∣auxProfilePolynomial k := by
    refine ⟨C ((Nat.factorial (k+1):ℝ)⁻¹)*X^(k+1)*
      (C ((2*k+3:ℕ):ℝ)*X-C ((k+2:ℕ):ℝ)),?_⟩
    unfold auxProfilePolynomial
    ring
  obtain ⟨q,hq⟩ := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j hdiv
  rw [hq,eval_mul,eval_pow,eval_sub,eval_one,eval_X,sub_self,
    zero_pow (show k-j≠0 by omega),zero_mul]

theorem auxProfilePolynomial_derivative_one_top (k : ℕ) :
    (Polynomial.derivative^[k] (auxProfilePolynomial k)).eval 1=(-1:ℝ)^k := by
  let P : Polynomial ℝ := C ((Nat.factorial (k+1):ℝ)⁻¹)*X^(k+1)*
    (C ((2*k+3:ℕ):ℝ)*X-C ((k+2:ℕ):ℝ))
  have he : auxProfilePolynomial k=P*(1-X)^k := by dsimp [auxProfilePolynomial,P]; ring
  rw [he,Polynomial.iterate_derivative_mul,eval_finsetSum]
  rw [Finset.sum_eq_single k]
  · simp only [Nat.sub_self,Function.iterate_zero_apply,Nat.choose_self,one_smul,eval_mul]
    rw [polynomial_one_sub_X_derivative_eval_one]
    simp only [Nat.sub_self,pow_zero,mul_one,Nat.descFactorial_self]
    dsimp [P]
    simp only [eval_mul,eval_C,eval_pow,eval_X,one_pow,mul_one,eval_sub]
    have hfact : (Nat.factorial (k+1):ℝ)≠0 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · intro j hj hjk
    have hjlt : j<k := by have := Finset.mem_range.mp hj; omega
    simp only [eval_smul,eval_mul]
    rw [polynomial_one_sub_X_derivative_eval_one,
      zero_pow (show k-j≠0 by omega),mul_zero,mul_zero,smul_zero]
  · intro hk
    exact (hk (Finset.mem_range.mpr (by omega))).elim

theorem complex_contDiff_infty_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem polynomial_interval_ibp (P : Polynomial ℝ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    (∫ u : ℝ in 0..1, Complex.ofReal (P.eval u)*iteratedDeriv (n+1) ψ u)=
      Complex.ofReal (P.eval 1)*iteratedDeriv n ψ 1-
      Complex.ofReal (P.eval 0)*iteratedDeriv n ψ 0-
      ∫ u : ℝ in 0..1, Complex.ofReal (P.derivative.eval u)*iteratedDeriv n ψ u := by
  have hψn := complex_contDiff_infty_iteratedDeriv hψ n
  have hψn1 := complex_contDiff_infty_iteratedDeriv hψ (n+1)
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
  · intro u _hu
    convert (P.hasDerivAt u).ofReal_comp using 1
  · intro u _hu
    rw [iteratedDeriv_succ]
    exact ((hψn.differentiable (by norm_num)) u).hasDerivAt
  · exact (Complex.continuous_ofReal.comp P.derivative.continuous).intervalIntegrable _ _
  · exact hψn1.continuous.intervalIntegrable _ _

theorem polynomial_interval_higher_ibp (P : Polynomial ℝ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ)
    (hzero : ∀ j<n, (Polynomial.derivative^[j] P).eval 0=0 ∧
      (Polynomial.derivative^[j] P).eval 1=0) :
    (∫ u : ℝ in 0..1, Complex.ofReal (P.eval u)*iteratedDeriv (n+1) ψ u)=
      (-1:ℂ)^n*(Complex.ofReal ((Polynomial.derivative^[n] P).eval 1)*ψ 1-
        Complex.ofReal ((Polynomial.derivative^[n] P).eval 0)*ψ 0-
        ∫ u : ℝ in 0..1, Complex.ofReal ((Polynomial.derivative^[n+1] P).eval u)*ψ u) := by
  induction n generalizing P with
  | zero => simpa only [Nat.zero_add,Function.iterate_zero_apply,Function.iterate_one,iteratedDeriv_zero,pow_zero,one_mul]
      using polynomial_interval_ibp P ψ hψ 0
  | succ n ih =>
    have hiter (j : ℕ) : Polynomial.derivative^[j] P.derivative=Polynomial.derivative^[j+1] P :=
      (Function.iterate_succ_apply _ _ _).symm
    have hz0 := hzero 0 (by omega)
    simp only [Function.iterate_zero_apply] at hz0
    have hz' : ∀ j<n, (Polynomial.derivative^[j] P.derivative).eval 0=0 ∧
        (Polynomial.derivative^[j] P.derivative).eval 1=0 := by
      intro j hj
      rw [hiter]
      exact hzero (j+1) (by omega)
    have htail := ih P.derivative hz'
    simp_rw [hiter] at htail
    rw [polynomial_interval_ibp P ψ hψ (n+1),hz0.1,hz0.2]
    simp only [Complex.ofReal_zero,zero_mul,sub_zero,zero_sub]
    rw [htail,pow_succ]
    ring

theorem auxCompletionProfile_integral_eq_interval (k : ℕ) (g : ℝ → ℂ) :
    (∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u)*g u)=
      ∫ u : ℝ in 0..1, Complex.ofReal ((auxProfilePolynomial k).eval u)*g u := by
  have heq : (fun u : ℝ => Complex.ofReal (auxCompletionProfile k u)*g u)=
      (Icc (0:ℝ) 1).indicator (fun u : ℝ => Complex.ofReal ((auxProfilePolynomial k).eval u)*g u) := by
    funext u
    by_cases hu : u∈Icc (0:ℝ) 1 <;> simp [auxCompletionProfile,hu]
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]

/-- The exact derivative measure on every smooth test: one density and one
endpoint atom, whose coefficient has magnitude one. -/
theorem auxCompletionProfile_distributional_derivative (k : ℕ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (-1:ℂ)^(k+1)*(∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u)*iteratedDeriv (k+1) ψ u)=
      (∫ u : ℝ in 0..1, Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u)+
        (-1:ℂ)^(k+1)*ψ 1 := by
  rw [auxCompletionProfile_integral_eq_interval]
  have hzero : ∀ j<k, (Polynomial.derivative^[j] (auxProfilePolynomial k)).eval 0=0 ∧
      (Polynomial.derivative^[j] (auxProfilePolynomial k)).eval 1=0 := by
    intro j hj
    exact ⟨auxProfilePolynomial_derivative_zero k j hj.le,auxProfilePolynomial_derivative_one_vanish k j hj⟩
  rw [polynomial_interval_higher_ibp (auxProfilePolynomial k) ψ hψ k hzero,
    auxProfilePolynomial_derivative_one_top,auxProfilePolynomial_derivative_zero k k le_rfl,
    Complex.ofReal_zero,zero_mul,sub_zero,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  let p : ℂ := (-1:ℂ)^k
  have hsign : p*p=1 := by
    dsimp [p]
    rw [←pow_add,show k+k=2*k by omega,pow_mul]
    norm_num
  rw [pow_succ]
  let J : ℂ := ∫ u : ℝ in 0..1,
    Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u
  change (p*(-1))*(p*(p*ψ 1-J))=J+(p*(-1))*ψ 1
  calc
    _ = -(p*p)*(p*ψ 1-J) := by ring
    _ = _ := by rw [hsign]; ring

theorem auxCompletionProfile_endpoint_atom_norm (k : ℕ) : ‖(-1:ℂ)^(k+1)‖=1 := by simp

/-!
UNCHECKED continuation. Insert after the preserved AuxiliaryEndpointProfiles
statements in the already-planned AuxiliaryCompletions module.
This section proves supporting statements only, not any of the three complete
auxiliary primary roots. It needs Mathlib.Data.Nat.Choose.Sum in addition to the
endpoint fragment's polynomial derivative import.
-/

/-- The explicit nonnegative coefficient budget after integrating the density
monomials. This is not a substitute for identifying the actual density. -/
def auxDensityCoefficientBudget (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+2), ((k+1).choose j : ℝ) * ((k+2+j).choose (k+1) : ℝ)

/-- Finite binomial algebra, with constants uniform in k. -/
theorem auxDensityCoefficientBudget_le (k : ℕ) :
    auxDensityCoefficientBudget k ≤ (2 : ℝ)^(3*k+4) := by
  have hchoose (j : ℕ) (hj : j ∈ Finset.range (k+2)) :
      ((k+2+j).choose (k+1) : ℝ) ≤ (2 : ℝ)^(2*k+3) := by
    have hjle : j ≤ k+1 := by have := Finset.mem_range.mp hj; omega
    have hnat : (k+2+j).choose (k+1) ≤ 2^(2*k+3) :=
      (Nat.choose_le_two_pow _ _).trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega))
    exact_mod_cast hnat
  have hsum : (∑ j ∈ Finset.range (k+2), ((k+1).choose j : ℝ)) = (2 : ℝ)^(k+1) := by
    exact_mod_cast Nat.sum_range_choose (k+1)
  calc
    _ ≤ ∑ j ∈ Finset.range (k+2), ((k+1).choose j : ℝ) * (2 : ℝ)^(2*k+3) := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hchoose j hj) (Nat.cast_nonneg _)
    _ = (2 : ℝ)^(k+1) * (2 : ℝ)^(2*k+3) := by rw [←Finset.sum_mul,hsum]
    _ = _ := by rw [←pow_add]; congr 1; omega

/-- Descending factorial normalization used by the actual polynomial derivative.
There is no missing (j+1), or endpoint/factorial normalization convention. -/
theorem auxDensity_descFactorial_ratio (k j : ℕ) :
    ((k+2+j).descFactorial (k+2) : ℝ) / (Nat.factorial (k+1) : ℝ) =
      (j+1 : ℕ) * ((k+2+j).choose (k+1) : ℝ) := by
  have hc := Nat.choose_succ_right_eq (k+2+j) (k+1)
  have hsub : k+2+j-(k+1)=j+1 := by omega
  rw [hsub] at hc
  have hcr : ((k+2+j).choose (k+2) : ℝ) * (k+2 : ℕ) =
      ((k+2+j).choose (k+1) : ℝ) * (j+1 : ℕ) := by exact_mod_cast hc
  calc
    _ = ((k+2 : ℕ):ℝ) * ((k+2+j).choose (k+2) : ℝ) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      rw [show k+2=(k+1)+1 by omega,Nat.factorial_succ]
      push_cast
      have hf : (Nat.factorial (k+1) : ℝ) ≠ 0 := by positivity
      field_simp [hf]
      ring
    _ = _ := by simpa only [mul_comm] using hcr

/-- Binomial expansion at the actual primitive, before differentiating. -/
theorem auxProfilePrimitive_expansion (k : ℕ) :
    auxProfilePrimitivePolynomial k =
      ∑ j ∈ Finset.range (k+2),
        Polynomial.C (((Nat.factorial (k+1):ℝ)⁻¹) *
          ((-1:ℝ)^j * ((k+1).choose j : ℝ))) * Polynomial.X^(k+2+j) := by
  have hpow : ((1-Polynomial.X : Polynomial ℝ)^(k+1)) =
      ∑ j ∈ Finset.range (k+2),
        Polynomial.C ((-1:ℝ)^j * ((k+1).choose j : ℝ)) * Polynomial.X^j := by
    rw [show (1-Polynomial.X : Polynomial ℝ) = Polynomial.X*Polynomial.C (-1)+1 by simp; ring,add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow,mul_one,mul_pow,Polynomial.C_mul,Polynomial.C_pow,
      Polynomial.C_eq_natCast]
    ring
  rw [auxProfilePrimitivePolynomial,hpow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Polynomial.C_mul]
  ring

/-- Exact monomial representation of D^(k+1)Phi_k. -/
theorem auxProfileDensity_polynomial (k : ℕ) :
    Polynomial.derivative^[k+1] (auxProfilePolynomial k) =
      ∑ j ∈ Finset.range (k+2),
        Polynomial.C ((-1:ℝ)^(j+1) * ((k+1).choose j : ℝ) *
          (j+1 : ℕ) * ((k+2+j).choose (k+1) : ℝ)) * Polynomial.X^j := by
  have hneg (P : Polynomial ℝ) (n : ℕ) :
      Polynomial.derivative^[n] (-P) = -(Polynomial.derivative^[n] P) := by
    induction n generalizing P with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih,Polynomial.derivative_neg,
        Function.iterate_succ_apply']
  rw [auxProfilePolynomial_eq_neg_derivative,hneg,
    ←Function.iterate_succ_apply,
    show k+1+1=k+2 by omega,auxProfilePrimitive_expansion,
    Polynomial.iterate_derivative_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul,
    show k+2+j-(k+2)=j by omega]
  have hcoef :
      -(((Nat.factorial (k+1):ℝ)⁻¹ * ((-1:ℝ)^j*((k+1).choose j:ℝ))) *
        ((k+2+j).descFactorial (k+2):ℝ)) =
      (-1:ℝ)^(j+1)*((k+1).choose j:ℝ)*(j+1:ℕ)*((k+2+j).choose (k+1):ℝ) := by
    have hratio := auxDensity_descFactorial_ratio k j
    rw [pow_succ]
    rw [div_eq_mul_inv] at hratio
    calc
      _ = -((-1:ℝ)^j*((k+1).choose j:ℝ)) *
          (((k+2+j).descFactorial (k+2):ℝ)*(Nat.factorial (k+1):ℝ)⁻¹) := by ring
      _ = _ := by rw [hratio]; push_cast; ring
  simpa only [Polynomial.C_neg,Polynomial.C_mul,mul_assoc,neg_mul] using
    congrArg (fun a : ℝ => Polynomial.C a * (Polynomial.X:Polynomial ℝ)^j) hcoef

/-- Nonnegative pointwise majorant of the actual derivative density, only on
its true compact support. -/
def auxProfileDensityMajorant (k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+2),
    (((k+1).choose j : ℝ) * ((k+2+j).choose (k+1) : ℝ)) *
      ((j+1 : ℕ) * u^j)

theorem auxProfileDensity_abs_le (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    |(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u| ≤
      auxProfileDensityMajorant k u := by
  rw [auxProfileDensity_polynomial,Polynomial.eval_finsetSum]
  calc
    _ ≤ ∑ j ∈ Finset.range (k+2),
        |(Polynomial.C ((-1:ℝ)^(j+1)*((k+1).choose j:ℝ)*
          (j+1:ℕ)*((k+2+j).choose (k+1):ℝ))*Polynomial.X^j).eval u| :=
      Finset.abs_sum_le_sum_abs (fun j : ℕ =>
        (Polynomial.C ((-1:ℝ)^(j+1)*((k+1).choose j:ℝ)*
          (j+1:ℕ)*((k+2+j).choose (k+1):ℝ))*Polynomial.X^j).eval u)
        (Finset.range (k+2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
        Polynomial.eval_X,abs_mul,abs_pow,abs_neg,abs_one,one_pow,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) ((k+1).choose j)),
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (j+1)),
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) ((k+2+j).choose (k+1))),
        abs_of_nonneg hu]
      ring

theorem auxProfileDensityMajorant_integral (k : ℕ) :
    (∫ u : ℝ in 0..1, auxProfileDensityMajorant k u) =
      auxDensityCoefficientBudget k := by
  have hmon (j : ℕ) : (∫ u : ℝ in 0..1, ((j+1 : ℕ):ℝ)*u^j) = 1 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0:ℝ)) (b := 1)
      (fun u _ => by simpa using hasDerivAt_pow (j+1) u)
      ((by fun_prop : Continuous (fun u : ℝ => ((j+1:ℕ):ℝ)*u^j)).intervalIntegrable _ _)
    simpa using hh
  unfold auxProfileDensityMajorant auxDensityCoefficientBudget
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul,hmon,mul_one]
  · intro j _
    exact (by fun_prop : Continuous (fun u : ℝ =>
      (((k+1).choose j : ℝ)*((k+2+j).choose (k+1):ℝ))*
        (((j+1:ℕ):ℝ)*u^j))).intervalIntegrable _ _

/-- Full order-uniform density L1 bound. The endpoint atom is deliberately NOT
included here: it is added by the following test-functional theorem. -/
theorem auxCompletionProfile_density_L1_bound (k : ℕ) :
    (∫ u : ℝ in 0..1,
      |(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u|) ≤
      (2:ℝ)^(3*k+4) := by
  have hD := (Polynomial.derivative^[k+1] (auxProfilePolynomial k)).continuous
  calc
    _ ≤ ∫ u : ℝ in 0..1, auxProfileDensityMajorant k u := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hD.abs.intervalIntegrable _ _)
        (by exact (by unfold auxProfileDensityMajorant; fun_prop :
          Continuous (auxProfileDensityMajorant k)).intervalIntegrable _ _) ?_
      intro u hu
      exact auxProfileDensity_abs_le k u hu.1
    _ = auxDensityCoefficientBudget k := auxProfileDensityMajorant_integral k
    _ ≤ _ := auxDensityCoefficientBudget_le k

/-- Actual density-plus-atom functional bound on smooth complex tests.
The +1 is the norm of the genuine endpoint atom at u=1. -/
theorem auxCompletionProfile_derivative_test_bound (k : ℕ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ Icc (0:ℝ) 1, ‖ψ u‖ ≤ M) :
    ‖(-1:ℂ)^(k+1) * (∫ u : ℝ,
      Complex.ofReal (auxCompletionProfile k u) * iteratedDeriv (k+1) ψ u)‖ ≤
      (1+(2:ℝ)^(3*k+4))*M := by
  rw [auxCompletionProfile_distributional_derivative k ψ hψ]
  have hψc : Continuous ψ := hψ.continuous
  have hnorm : ‖∫ u : ℝ in 0..1,
      Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u‖ ≤
      M*(∫ u : ℝ in 0..1,
        |(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u|) := by
    calc
      _ ≤ ∫ u : ℝ in 0..1,
          ‖Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ u : ℝ in 0..1,
          M*|(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (by exact (by fun_prop : Continuous (fun u : ℝ =>
            ‖Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u‖)).intervalIntegrable _ _)
          (by exact (by fun_prop : Continuous (fun u : ℝ =>
            M*|(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u|)).intervalIntegrable _ _) ?_
        intro u hu
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbound u hu)
          (abs_nonneg ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u))
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hatom : ‖(-1:ℂ)^(k+1)*ψ 1‖ ≤ M := by
    simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using
      hbound 1 (by constructor <;> norm_num)
  calc
    _ ≤ ‖∫ u : ℝ in 0..1,
        Complex.ofReal ((Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u)*ψ u‖ +
        ‖(-1:ℂ)^(k+1)*ψ 1‖ := norm_add_le _ _
    _ ≤ M*(2:ℝ)^(3*k+4)+M :=
      add_le_add (hnorm.trans (mul_le_mul_of_nonneg_left
        (auxCompletionProfile_density_L1_bound k) hM)) hatom
    _ = _ := by ring

/-- Literal heat-Fourier exponential; both frequency signs are allowed. -/
def auxProfileFrequency (xi : ℝ) : ℂ := -((2*Real.pi*xi : ℝ):ℂ)*Complex.I

def auxProfileFourierTest (xi u : ℝ) : ℂ :=
  Complex.exp (auxProfileFrequency xi * (u:ℂ))

def auxProfileFourierIntegral (k : ℕ) (xi : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u) * auxProfileFourierTest xi u

theorem auxProfileFrequency_norm (xi : ℝ) :
    ‖auxProfileFrequency xi‖ = 2*Real.pi*|xi| := by
  simp only [auxProfileFrequency,norm_mul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,Complex.norm_I,mul_one,abs_of_pos Real.pi_pos]
  norm_num

theorem auxProfileFourierTest_norm (xi u : ℝ) : ‖auxProfileFourierTest xi u‖ = 1 := by
  rw [auxProfileFourierTest,Complex.norm_exp]
  have hre : (auxProfileFrequency xi * (u:ℂ)).re = 0 := by
    simp [auxProfileFrequency]
  rw [hre,Real.exp_zero]

theorem auxProfileFourierTest_hasDerivAt (xi u : ℝ) :
    HasDerivAt (auxProfileFourierTest xi)
      (auxProfileFrequency xi * auxProfileFourierTest xi u) u := by
  have h := (((hasDerivAt_id (u:ℂ)).const_mul (auxProfileFrequency xi)).cexp).comp_ofReal
  convert h using 1
  · rfl
  · simp only [auxProfileFourierTest,id_eq,mul_one]
    ring

theorem auxProfileFourierTest_iteratedDeriv (xi : ℝ) (n : ℕ) :
    iteratedDeriv n (auxProfileFourierTest xi) =
      fun u => (auxProfileFrequency xi)^n * auxProfileFourierTest xi u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext u
    rw [((auxProfileFourierTest_hasDerivAt xi u).const_mul
      ((auxProfileFrequency xi)^n)).deriv,pow_succ]
    ring

/-- Actual Fourier decay from the density plus its endpoint atom. The domain
excludes frequency zero only because division by its norm occurs. -/
theorem auxCompletionProfile_fourier_decay (k : ℕ) (xi : ℝ) (hxi : xi ≠ 0) :
    ‖auxProfileFourierIntegral k xi‖ ≤
      (1+(2:ℝ)^(3*k+4)) / (2*Real.pi*|xi|)^(k+1) := by
  have htest : ContDiff ℝ (⊤ : ℕ∞) (auxProfileFourierTest xi) := by
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have h := auxCompletionProfile_derivative_test_bound k (auxProfileFourierTest xi)
    htest 1 (by norm_num) (fun u _ => (auxProfileFourierTest_norm xi u).le)
  have hI : (∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u) *
      iteratedDeriv (k+1) (auxProfileFourierTest xi) u) =
      (auxProfileFrequency xi)^(k+1) * auxProfileFourierIntegral k xi := by
    rw [auxProfileFourierTest_iteratedDeriv]
    have he (u : ℝ) :
        Complex.ofReal (auxCompletionProfile k u) *
            ((auxProfileFrequency xi)^(k+1)*auxProfileFourierTest xi u) =
        (auxProfileFrequency xi)^(k+1) *
            (Complex.ofReal (auxCompletionProfile k u)*auxProfileFourierTest xi u) := by ring
    simp_rw [he]
    rw [integral_const_mul]
    rfl
  rw [hI] at h
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,mul_one,
    auxProfileFrequency_norm] at h
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi*|xi|)^(k+1))).mpr
    (by simpa only [mul_comm] using h)


/-!
## Actual Poisson completion and its open transform domain

UNCHECKED continuation at 9b6a9a3.  No new primary is accepted until its full
imported expected type, physical consumers and axiom closure are checked.
-/

open scoped FourierTransform
open Asymptotics Zeta23.OPICA

lemma auxProfile_complex_eq_indicator (k : ℕ) :
    (fun u : ℝ => (auxCompletionProfile k u : ℂ)) =
      (Icc (0:ℝ) 1).indicator (fun u => Complex.ofReal ((auxProfilePolynomial k).eval u)) := by
  funext u
  by_cases hu : u∈Icc (0:ℝ) 1 <;> simp [auxCompletionProfile,hu]

lemma auxProfile_continuous (k : ℕ) (hk : 1≤k) :
    Continuous (fun u : ℝ => (auxCompletionProfile k u : ℂ)) := by
  rw [auxProfile_complex_eq_indicator]
  have hp : Continuous (fun u : ℝ => Complex.ofReal ((auxProfilePolynomial k).eval u)) :=
    Complex.continuous_ofReal.comp (auxProfilePolynomial k).continuous
  have hb : ∀ x∈frontier (Icc (0:ℝ) 1),
      Complex.ofReal ((auxProfilePolynomial k).eval x)=(0:ℝ→ℂ) x := by
    intro x hx
    rw [frontier_Icc (by norm_num : (0:ℝ)≤1)] at hx
    rcases hx with rfl|rfl
    · simp [auxProfilePolynomial_zero]
    · simp [auxProfilePolynomial_one k hk]
  simpa only [piecewise_eq_indicator] using hp.piecewise hb continuous_const

lemma auxProfile_support (k : ℕ) :
    Function.support (fun u : ℝ => (auxCompletionProfile k u : ℂ)) ⊆ Icc (0:ℝ) 1 := by
  intro u hu
  by_contra hn
  exact hu (by simp [auxCompletionProfile,hn])

lemma auxProfile_compactSupport (k : ℕ) :
    HasCompactSupport (fun u : ℝ => (auxCompletionProfile k u : ℂ)) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (auxProfile_support k) isClosed_Icc)

lemma auxProfile_integrable (k : ℕ) (hk : 1≤k) :
    Integrable (fun u : ℝ => (auxCompletionProfile k u : ℂ)) :=
  (auxProfile_continuous k hk).integrable_of_hasCompactSupport (auxProfile_compactSupport k)

lemma auxProfile_zero_integral (k : ℕ) :
    (∫ u : ℝ, (auxCompletionProfile k u : ℂ))=0 := by
  have he := auxCompletionProfile_integral_eq_interval k (fun _ => 1)
  simp only [mul_one] at he
  rw [he,auxProfilePolynomial_eq_neg_derivative]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1)
    (fun u _ => ((auxProfilePrimitivePolynomial k).hasDerivAt u).ofReal_comp)
    ((Complex.continuous_ofReal.comp (auxProfilePrimitivePolynomial k).derivative.continuous).intervalIntegrable _ _)
  simp only [Polynomial.eval_neg,Complex.ofReal_neg,intervalIntegral.integral_neg]
  rw [h]
  simp [auxProfilePrimitivePolynomial]

lemma auxProfileFourierIntegral_eq_fourier (k : ℕ) (xi : ℝ) :
    auxProfileFourierIntegral k xi=𝓕 (fun u : ℝ => (auxCompletionProfile k u : ℂ)) xi := by
  rw [auxProfileFourierIntegral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [auxProfileFourierTest,auxProfileFrequency,smul_eq_mul]
  rw [mul_comm (Complex.ofReal (auxCompletionProfile k u))]
  congr 1
  congr 1
  push_cast
  ring

lemma auxProfileFourier_zero (k : ℕ) : auxProfileFourierIntegral k 0=0 := by
  simpa [auxProfileFourierIntegral,auxProfileFourierTest,auxProfileFrequency] using auxProfile_zero_integral k

/-- Literal rescaling of the polynomial test, not a substitute completion. -/
def auxScaledProfile (k : ℕ) (a : ℝ) (u : ℝ) : ℂ := auxCompletionProfile k (a*u)

lemma auxScaledProfile_fourier (k : ℕ) (a : ℝ) (ha : 0<a) (xi : ℝ) :
    𝓕 (auxScaledProfile k a) xi=(a:ℂ)⁻¹*auxProfileFourierIntegral k (xi/a) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ→ℂ := fun u => (auxCompletionProfile k u : ℂ)*
    Complex.exp (-((2*Real.pi*(xi/a):ℝ):ℂ)*Complex.I*(u:ℂ))
  have he : (fun u : ℝ => Complex.exp ((-2*Real.pi*u*xi:ℝ)*Complex.I) • auxScaledProfile k a u)=
      fun u => g (a*u) := by
    funext u
    simp only [g,auxScaledProfile,smul_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp [show (a:ℂ) ≠ 0 by exact_mod_cast ha.ne']
    <;> ring
  rw [he,Measure.integral_comp_mul_left g a,abs_of_pos (inv_pos.mpr ha)]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  rfl

lemma auxScaledProfile_atTop_decay (k : ℕ) (a : ℝ) (ha : 0<a) :
    auxScaledProfile k a =O[cocompact ℝ] (fun u : ℝ => |u|^(-2:ℝ)) := by
  refine IsBigO.of_bound 0 ?_
  have he : ∀ᶠ u : ℝ in cocompact ℝ, 2/a≤‖u‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [he] with u hu
  have hnot : a*u∉Icc (0:ℝ) 1 := by
    intro h
    have hnon : 0≤u := by nlinarith [h.1]
    rw [Real.norm_eq_abs,abs_of_nonneg hnon] at hu
    have h2 := (div_le_iff₀ ha).mp hu
    nlinarith [h.2]
  simp [auxScaledProfile,auxCompletionProfile,hnot]

lemma auxScaledProfile_fourier_bound (k : ℕ) (a : ℝ) (ha : 0<a)
    {xi : ℝ} (hxi : xi≠0) :
    ‖𝓕 (auxScaledProfile k a) xi‖ ≤
      ((1+(2:ℝ)^(3*k+4))*a^k/(2*Real.pi)^(k+1))*|xi|^(-((k+1:ℕ):ℝ)) := by
  rw [auxScaledProfile_fourier k a ha,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have h := mul_le_mul_of_nonneg_left
    (auxCompletionProfile_fourier_decay k (xi/a) (div_ne_zero hxi ha.ne')) (inv_nonneg.mpr ha.le)
  apply h.trans_eq
  rw [abs_div,abs_of_pos ha,Real.rpow_neg (abs_nonneg xi),Real.rpow_natCast]
  rw [show 2*Real.pi*(|xi|/a)=(2*Real.pi*|xi|)/a by ring,div_pow,mul_pow]
  have hx : |xi|≠0 := abs_ne_zero.mpr hxi
  have hpi : (2*Real.pi:ℝ)≠0 := by positivity
  rw [pow_succ a]
  field_simp [ha.ne', hx, hpi]
  <;> ring

lemma auxScaledProfile_fourier_summable (k : ℕ) (hk : 1≤k) (a : ℝ) (ha : 0<a) :
    Summable (fun n : ℤ => 𝓕 (auxScaledProfile k a) n) := by
  have hr : 1<((k+1:ℕ):ℝ) := by exact_mod_cast (show 1<k+1 by omega)
  apply Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow hr).mul_left
      ((1+(2:ℝ)^(3*k+4))*a^k/(2*Real.pi)^(k+1)))
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  exact auxScaledProfile_fourier_bound k a ha (by exact_mod_cast hn)

lemma zeta_real_nat_power_sum (k : ℕ) (hk : 1≤k) :
    Summable (fun n : ℕ => 1/(n:ℝ)^(k+1)) ∧
      (∑' n : ℕ, 1/(n:ℝ)^(k+1))=(riemannZeta (k+1:ℕ)).re := by
  have hc : Summable (fun n : ℕ => 1/(n:ℂ)^((k+1:ℕ):ℂ)) :=
    Complex.summable_one_div_nat_cpow.mpr (by norm_num; omega)
  have hz := zeta_eq_tsum_one_div_nat_cpow (s := ((k+1:ℕ):ℂ)) (by norm_num; omega)
  have he (n : ℕ) : (1/(n:ℂ)^((k+1:ℕ):ℂ)).re=1/(n:ℝ)^(k+1) := by
    rw [Complex.cpow_natCast]
    have hh : (1/(n:ℂ)^(k+1))=Complex.ofReal (1/(n:ℝ)^(k+1)) := by push_cast; rfl
    rw [hh,Complex.ofReal_re]
  have hr := Complex.hasSum_re hc.hasSum
  simp only [he] at hr
  refine ⟨hr.summable,?_⟩
  rw [hr.tsum_eq, ←hz]

lemma integer_inverse_power_sum (k : ℕ) (hk : 1≤k) :
    (∑' n : ℤ, |(n:ℝ)|^(-((k+1:ℕ):ℝ)))=2*(riemannZeta (k+1:ℕ)).re := by
  let f : ℤ → ℝ := fun n => |(n:ℝ)|^(-((k+1:ℕ):ℝ))
  have hs := (zeta_real_nat_power_sum k hk).1
  have he (n : ℕ) : f (n:ℤ)=1/(n:ℝ)^(k+1) := by
    change |(n:ℝ)|^(-((k+1:ℕ):ℝ))=1/(n:ℝ)^(k+1)
    rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n),
      Real.rpow_neg (Nat.cast_nonneg (α:=ℝ) n),Real.rpow_natCast,one_div]
  have hneg (n : ℕ) : f (-(n+1):ℤ)=1/((n+1:ℕ):ℝ)^(k+1) := by
    change |((-(n+1):ℤ):ℝ)|^(-((k+1:ℕ):ℝ))=1/((n+1:ℕ):ℝ)^(k+1)
    have hcast : ((-(n+1):ℤ):ℝ)=-((n+1:ℕ):ℝ) := by push_cast; ring
    rw [hcast,abs_neg]
    exact he (n+1)
  have hp : Summable (fun n : ℕ => f (n:ℤ)) := by simpa only [he] using hs
  have hshift := (hasSum_nat_add_iff' 1).mpr hs.hasSum
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_pow (by omega : k+1≠0),
    div_zero,sub_zero] at hshift
  have hn : Summable (fun n : ℕ => f (-(n+1):ℤ)) := by
    simpa only [hneg] using hshift.summable
  change (∑' n : ℤ, f n)=_
  rw [tsum_of_nat_of_neg_add_one hp hn]
  simp only [he,hneg]
  rw [hshift.tsum_eq,(zeta_real_nat_power_sum k hk).2]
  ring

/-- The actual rescaled lattice profile, including its value at every integer
and at the causal endpoint.  This statement is independent of Poisson. -/
lemma auxCompletionKernel_scaled_profile (k : ℕ) (t : ℝ) :
    (auxCompletionKernel k t : ℂ)=
      (Real.exp (-t/2):ℂ)*∑' n : ℕ, auxScaledProfile k (Real.exp (-t)) n := by
  rw [auxCompletionKernel,nativeIntegerTranslateAction,Complex.ofReal_tsum,←tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [nativeIntegerCoefficient,auxScaledProfile,auxCompletionProfile,auxProfilePolynomial_zero]
  have hnp : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(t-Real.log n))=Real.exp (-t)*(n:ℝ) := by
    rw [neg_sub,sub_eq_add_neg,Real.exp_add,Real.exp_log hnp]
    ring
  have hmem : Real.exp (-t)*(n:ℝ)∈Icc (0:ℝ) 1 ↔ 0≤t-Real.log n := by
    rw [←he]
    constructor
    · intro h
      have h' := Real.exp_le_one_iff.mp h.2
      linarith
    · intro h
      exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩
  have hscale : Real.exp (-t/2)*(Real.exp (-t)*(n:ℝ))^(k+1)=
      (1/Real.sqrt (n:ℝ))*Real.exp (-((k:ℝ)+3/2)*(t-Real.log n)) := by
    have hnexp : (n:ℝ)=Real.exp (Real.log (n:ℝ)) := (Real.exp_log hnp).symm
    have hs : Real.sqrt (n:ℝ)=Real.exp (Real.log (n:ℝ)/2) := by
      calc
        _ = Real.sqrt (Real.exp (Real.log (n:ℝ))) := by rw [Real.exp_log hnp]
        _ = _ := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
    rw [hs, one_div, ←Real.exp_neg]
    conv_lhs => rw [hnexp, ←Real.exp_add, ←Real.exp_nat_mul, ←Real.exp_add]
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  have hreal : nativeIntegerCoefficient n * auxCompletionFilter k (t-Real.log n)=
      Real.exp (-t/2)*auxCompletionProfile k (Real.exp (-t)*(n:ℝ)) := by
    by_cases ht : 0≤t-Real.log n
    · rw [auxCompletionFilter,if_pos ht,auxCompletionProfile,if_pos (hmem.mpr ht),
        auxProfilePolynomial_eval,he]
      unfold nativeIntegerCoefficient
      rw [show (1/Real.sqrt (n:ℝ))*
          (Real.exp (-((k:ℝ)+3/2)*(t-Real.log n)) *
            (1-Real.exp (-t)*(n:ℝ))^k/(Nat.factorial (k+1):ℝ)*
            (((2*k+3:ℕ):ℝ)*(Real.exp (-t)*(n:ℝ))-(k+2:ℕ))) =
          ((1/Real.sqrt (n:ℝ))*Real.exp (-((k:ℝ)+3/2)*(t-Real.log n)))*
            ((1-Real.exp (-t)*(n:ℝ))^k*
            (((2*k+3:ℕ):ℝ)*(Real.exp (-t)*(n:ℝ))-(k+2:ℕ))/(Nat.factorial (k+1):ℝ)) by ring,
          ←hscale]
      ring
    · simp only [auxCompletionFilter,if_neg ht,auxCompletionProfile,if_neg (mt hmem.mp ht),mul_zero]
  simpa only [Complex.ofReal_mul,auxScaledProfile] using congrArg Complex.ofReal hreal


lemma auxScaledProfile_nat_summable (k : ℕ) (a : ℝ) (ha : 0<a) :
    Summable (fun n : ℕ => auxScaledProfile k a n) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (1/a)+1))
  intro n hn
  have hbound : 1/a<(n:ℝ) := by
    have hn' : Nat.ceil (1/a)<n := by
      have h := not_lt.mp (fun hh => hn (Finset.mem_range.mpr hh))
      omega
    exact (Nat.le_ceil (1/a)).trans_lt (by exact_mod_cast hn')
  have hlarge : 1<a*(n:ℝ) := by
    have h := (div_lt_iff₀ ha).mp hbound
    nlinarith
  simp [auxScaledProfile,auxCompletionProfile,not_le.mpr hlarge]

lemma auxScaledProfile_int_nat (k : ℕ) (a : ℝ) (ha : 0<a) :
    (∑' n : ℤ, auxScaledProfile k a n)=∑' n : ℕ, auxScaledProfile k a n := by
  have hn (n : ℕ) : auxScaledProfile k a (-(n+1):ℤ)=0 := by
    have hneg : a*((-(n+1):ℤ):ℝ)<0 := by
      apply mul_neg_of_pos_of_neg ha
      have hnpos : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
      push_cast at hnpos ⊢
      linarith
    have hnot : a*((-(n+1):ℤ):ℝ)∉Icc (0:ℝ) 1 := fun h => (not_le.mpr hneg) h.1
    change Complex.ofReal (auxCompletionProfile k (a*((-(n+1):ℤ):ℝ)))=0
    rw [auxCompletionProfile,if_neg hnot,Complex.ofReal_zero]
  have hp : Summable (fun n : ℕ => auxScaledProfile k a (n:ℤ)) := by
    simpa only [Int.cast_natCast] using auxScaledProfile_nat_summable k a ha
  rw [tsum_of_nat_of_neg_add_one hp (by simp only [hn]; exact summable_zero)]
  simp only [hn,tsum_zero,add_zero,Int.cast_natCast]

/-- Primary decay theorem: actual compact profile, all Fourier ordinates,
zero mode cancellation and actual Poisson are assembled before the estimate. -/
theorem aux_completion_uniform_decay (k : ℕ) (hk : 1≤k) :
    (∀ t : ℝ, Summable (fun n : ℤ =>
      𝓕 (auxScaledProfile k (Real.exp (-t))) n)) ∧
    (∀ t : ℝ, |auxCompletionKernel k t|≤
      auxCompletionBound k*Real.exp (-auxCompletionAlpha k*t)) := by
  have hA : 0≤auxCompletionBound k := by
    have hz : 0≤(riemannZeta (k+1:ℕ)).re := by
      rw [←(zeta_real_nat_power_sum k hk).2]
      exact tsum_nonneg fun _ => by positivity
    unfold auxCompletionBound
    positivity
  refine ⟨fun t => auxScaledProfile_fourier_summable k hk _ (Real.exp_pos _),fun t => ?_⟩
  by_cases ht : 0≤t
  · let a : ℝ := Real.exp (-t)
    have ha : 0<a := Real.exp_pos _
    have hcont : Continuous (auxScaledProfile k a) :=
      (auxProfile_continuous k hk).comp (continuous_const.mul continuous_id)
    have hs := auxScaledProfile_fourier_summable k hk a ha
    have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont
      (by norm_num : (1:ℝ)<2) (auxScaledProfile_atTop_decay k a ha) hs 0
    simp only [zero_add,fourier_coe_apply,ofReal_zero,mul_zero,zero_mul,zero_div,Complex.exp_zero,mul_one] at hp
    rw [auxScaledProfile_int_nat k a ha] at hp
    have hscaled := auxCompletionKernel_scaled_profile k t
    change (auxCompletionKernel k t : ℂ)=(Real.exp (-t/2):ℂ)*∑' n : ℕ, auxScaledProfile k a n at hscaled
    rw [hp] at hscaled
    have hterm (n : ℤ) : ‖𝓕 (auxScaledProfile k a) n‖≤
        ((1+(2:ℝ)^(3*k+4))*a^k/(2*Real.pi)^(k+1))*|(n:ℝ)|^(-((k+1:ℕ):ℝ)) := by
      by_cases hn : n=0
      · subst n
        rw [auxScaledProfile_fourier k a ha]
        simp only [Int.cast_zero, zero_div, auxProfileFourier_zero, mul_zero, norm_zero]
        positivity
      · exact auxScaledProfile_fourier_bound k a ha (by exact_mod_cast hn)
    have hnorm := norm_tsum_le_tsum_norm hs.norm
    have hmajor : Summable (fun n : ℤ =>
        ((1+(2:ℝ)^(3*k+4))*a^k/(2*Real.pi)^(k+1))*|(n:ℝ)|^(-((k+1:ℕ):ℝ))) :=
      (Real.summable_abs_int_rpow (by exact_mod_cast (show 1<k+1 by omega))).mul_left _
    have hsum := hs.norm.tsum_le_tsum hterm hmajor
    rw [tsum_mul_left,integer_inverse_power_sum k hk] at hsum
    have hmul := mul_le_mul_of_nonneg_left (hnorm.trans hsum) (Real.exp_nonneg (-t/2))
    have hexp : Real.exp (-t/2)*a^k=Real.exp (-auxCompletionAlpha k*t) := by
      dsimp [a,auxCompletionAlpha]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      ring
    calc
      |auxCompletionKernel k t|=‖(auxCompletionKernel k t:ℂ)‖ := by simp
      _ = Real.exp (-t/2)*‖∑' n : ℤ, 𝓕 (auxScaledProfile k a) n‖ := by
        rw [hscaled,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      _ ≤ _ := hmul.trans_eq (by dsimp [auxCompletionBound]; rw [←hexp]; ring)
  · rw [auxCompletionKernel_zero_before k (lt_of_not_ge ht),abs_zero]
    exact mul_nonneg hA (Real.exp_nonneg _)

/-- Filled analytic representative.  The raw product has value zero at 1/2,
whereas this function has the removable value forced by the physical integral. -/
def auxCompletionFilledTransform (k : ℕ) (z : ℂ) : ℂ :=
  zetaPoleCleared (z+1/2)/(∏ j∈Finset.range (k+2), (z+(k+1+j:ℕ)+1/2))

def auxCompletionLaplace (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)

lemma auxDenominator_ne_zero (k : ℕ) (z : ℂ)
    (hz : -auxCompletionAlpha k<z.re) :
    (∏ j∈Finset.range (k+2), (z+(k+1+j:ℕ)+1/2))≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hzero
  have h := congrArg Complex.re hzero
  simp only [Complex.add_re,Complex.natCast_re] at h
  norm_num at h
  have hj0 : 0≤(j:ℝ) := Nat.cast_nonneg _
  dsimp [auxCompletionAlpha] at hz
  push_cast at h
  norm_num at h
  linarith

lemma auxCompletionFilledTransform_analytic (k : ℕ) {z : ℂ}
    (hz : -auxCompletionAlpha k<z.re) : AnalyticAt ℂ (auxCompletionFilledTransform k) z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+1/2) z := by fun_prop
  have hnum := (zetaPoleCleared_analyticAt (z+1/2)).comp (f := fun w : ℂ => w+1/2) hshift
  exact hnum.div
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => ∏ j∈Finset.range (k+2), (w+(k+1+j:ℕ)+1/2)) z)
    (auxDenominator_ne_zero k z hz)

lemma auxCompletionFilledTransform_agrees (k : ℕ) {z : ℂ} (hz : z≠1/2) :
    auxCompletionFilledTransform k z=auxRationalFactor k z*riemannZeta (z+1/2) := by
  have hs : z+1/2≠1 := by intro hs; apply hz; linear_combination hs
  rw [auxCompletionFilledTransform,zetaPoleCleared_eq hs,auxRationalFactor]
  simp only [div_eq_mul_inv]
  ring

lemma auxCompletionFilledTransform_at_half (k : ℕ) :
    auxCompletionFilledTransform k (1/2)=(Nat.factorial (k+1):ℂ)/(Nat.factorial (2*k+3):ℂ) := by
  have hprod : (∏ j∈Finset.range (k+2), ((1/2:ℂ)+(k+1+j:ℕ)+1/2))=
      (Nat.factorial (2*k+3):ℂ)/(Nat.factorial (k+1):ℂ) := by
    have hnat : (∏ j∈Finset.range (k+2), (k+2+j))*Nat.factorial (k+1)=Nat.factorial (2*k+3) := by
      have h := Nat.factorial_mul_ascFactorial (k+1) (k+2)
      rw [show k+1+(k+2)=2*k+3 by omega] at h
      simpa [Nat.ascFactorial_eq_prod_range,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,mul_comm] using h
    apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (k+1))).mpr
    have he : (∏ j∈Finset.range (k+2), ((1/2:ℂ)+(k+1+j:ℕ)+1/2))=
        ((∏ j∈Finset.range (k+2), (k+2+j)):ℕ) := by
      push_cast
      apply Finset.prod_congr rfl
      intro j _
      push_cast
      ring
    rw [he]
    exact_mod_cast hnat
  rw [auxCompletionFilledTransform,show (1/2:ℂ)+1/2=1 by norm_num,zetaPoleCleared_one,hprod]
  field_simp

lemma auxCompletionKernel_laplace_integrable (k : ℕ) (hk : 1≤k) {z : ℂ}
    (hz : -auxCompletionAlpha k<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)) := by
  have hdom : IntegrableOn (fun t : ℝ => auxCompletionBound k*
      Real.exp (-(z.re+auxCompletionAlpha k)*t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -(z.re+auxCompletionAlpha k)<0) 0).const_mul _)
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ici (0:ℝ)) ?_
    (fun t ht => by rw [auxCompletionKernel_zero_before k (lt_of_not_ge ht),Complex.ofReal_zero,mul_zero])
  have hmeas : Measurable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)) :=
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).measurable).mul
      (Complex.measurable_ofReal.comp (auxCompletionKernel_measurable k))
  apply hdom.mono' hmeas.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
  have hre : (-z*(t:ℂ)).re=-z.re*t := by simp
  rw [hre]
  have h := mul_le_mul_of_nonneg_left ((aux_completion_uniform_decay k hk).2 t)
    (Real.exp_nonneg (-z.re*t))
  apply h.trans_eq
  rw [←mul_assoc,mul_comm (Real.exp _) (auxCompletionBound k),mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma auxCompletion_weightedL2 (k : ℕ) (hk : 1≤k) (epsilon : ℝ)
    (hepsilon : -auxCompletionAlpha k<epsilon) :
    MemLp (weightedCausalProfile epsilon (fun t => (auxCompletionKernel k t:ℂ))) 2 volume := by
  let f : ℝ→ℂ := weightedCausalProfile epsilon (fun t => (auxCompletionKernel k t:ℂ))
  have hf : AEStronglyMeasurable f volume := by
    exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (auxCompletionKernel_measurable k)).aestronglyMeasurable).indicator measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm hf).mpr
  have hdom : Integrable ((Ici (0:ℝ)).indicator (fun t => (auxCompletionBound k)^2*
      Real.exp (-2*(epsilon+auxCompletionAlpha k)*t))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -2*(epsilon+auxCompletionAlpha k)<0) 0).const_mul _))
        |>.integrable_indicator measurableSet_Ici
  apply hdom.mono' (hf.norm.pow 2)
  filter_upwards with t
  by_cases ht : t∈Ici (0:ℝ)
  · change |‖f t‖^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp [f,weightedCausalProfile]
    rw [indicator_of_mem ht,norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
    have hre : (-((epsilon:ℂ)*(t:ℂ))).re=-epsilon*t := by simp
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have h := pow_le_pow_left₀ (abs_nonneg _) ((aux_completion_uniform_decay k hk).2 t) 2
    have he : Real.exp (-epsilon*t)^2*(auxCompletionBound k*Real.exp (-auxCompletionAlpha k*t))^2=
        (auxCompletionBound k)^2*Real.exp (-2*(epsilon+auxCompletionAlpha k)*t) := by
      rw [mul_pow]
      have hpow (x : ℝ) : Real.exp x ^ 2 = Real.exp (2*x) := (Real.exp_nat_mul x 2).symm
      rw [hpow,hpow]
      calc
        _ = (auxCompletionBound k)^2 *
          (Real.exp (2*(-epsilon*t))*Real.exp (2*(-auxCompletionAlpha k*t))) := by ring
        _ = _ := by rw [←Real.exp_add]; congr 2; ring
    simpa only [mul_pow,neg_mul,Set.indicator_of_mem ht] using
      (mul_le_mul_of_nonneg_left h (sq_nonneg (Real.exp (-epsilon*t)))).trans_eq he
  · simp [f,weightedCausalProfile,ht]

lemma auxCompletionLaplace_analytic (k : ℕ) (hk : 1≤k) (z : ℂ)
    (hz : -auxCompletionAlpha k<z.re) : AnalyticAt ℂ (auxCompletionLaplace k) z := by
  let epsilon : ℝ := (z.re-auxCompletionAlpha k)/2
  have he : -auxCompletionAlpha k<epsilon := by dsimp [epsilon]; linarith
  let f : WeightedL2Data := ⟨fun t => (auxCompletionKernel k t:ℂ),epsilon,
    auxCompletion_weightedL2 k hk epsilon he⟩
  have heq : weightedLaplace f=auxCompletionLaplace k := by
    funext w
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by
        change Complex.exp (-w*(t:ℂ))*(auxCompletionKernel k t:ℂ)=0
        rw [auxCompletionKernel_zero_before k (lt_of_not_ge ht),Complex.ofReal_zero,mul_zero])
  rw [←heq]
  exact laplace_holomorphic_of_weighted_L2 f z (by dsimp [epsilon,f]; linarith)

/-- Filter identity includes k=0 on its original domain.  The full improved
kernel domain and the removable value are proved for every k>=1. -/
theorem aux_completion_actual_transform :
    (∀ k : ℕ, ∀ z : ℂ, -((k:ℝ)+3/2)<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ)) ∧
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ))=auxRationalFactor k z) ∧
    (∀ k : ℕ, ∀ z : ℂ, 1/2<z.re →
      auxCompletionLaplace k z=auxRationalFactor k z*riemannZeta (z+1/2)) ∧
    (∀ k : ℕ, 1≤k → ∀ z : ℂ, -auxCompletionAlpha k<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)) ∧
      AnalyticAt ℂ (auxCompletionLaplace k) z ∧
      auxCompletionLaplace k z=auxCompletionFilledTransform k z) ∧
    (∀ k : ℕ, 1≤k → auxCompletionLaplace k (1/2)=
      (Nat.factorial (k+1):ℂ)/(Nat.factorial (2*k+3):ℂ)) := by
  have hid (k : ℕ) (hk : 1≤k) :
      EqOn (auxCompletionLaplace k) (auxCompletionFilledTransform k)
        {z : ℂ | -auxCompletionAlpha k<z.re} := by
    let U : Set ℂ := {z : ℂ | -auxCompletionAlpha k<z.re}
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (-auxCompletionAlpha k)).isPreconnected
    have ha : AnalyticOnNhd ℂ (auxCompletionLaplace k) U :=
      fun z hz => auxCompletionLaplace_analytic k hk z hz
    have hb : AnalyticOnNhd ℂ (auxCompletionFilledTransform k) U :=
      fun z hz => auxCompletionFilledTransform_analytic k hz
    have he : auxCompletionLaplace k =ᶠ[𝓝 (1:ℂ)] auxCompletionFilledTransform k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (1:ℂ)∈{z : ℂ | 1/2<z.re})] with z hz
      rw [auxCompletionFilledTransform_agrees k (by intro h; subst z; norm_num at hz)]
      exact (auxCompletionKernel_initial_laplace k hz).2
    exact ha.eqOn_of_preconnected_of_eventuallyEq hb hUconn
      (by dsimp [U,auxCompletionAlpha]; norm_num; linarith [Nat.cast_nonneg (α:=ℝ) k]) he
  refine ⟨fun k z hz => auxCompletionFilter_integrable_laplace k hz,
    fun k z hz => (auxCompletionKernel_initial_laplace k hz).2,
    fun k hk z hz => ⟨auxCompletionKernel_laplace_integrable k hk hz,
      auxCompletionLaplace_analytic k hk z hz,hid k hk hz⟩,?_⟩
  intro k hk
  rw [hid k hk (by dsimp [auxCompletionAlpha]; norm_num; linarith [Nat.cast_nonneg (α:=ℝ) k]),auxCompletionFilledTransform_at_half]

lemma shifted_nat_product_factorial (a n : ℕ) :
    (∏ j∈Finset.range n, (a+1+j))*Nat.factorial a=Nat.factorial (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    calc
      _ = (a+1+n)*((∏ j∈Finset.range n, (a+1+j))*Nat.factorial a) := by ring
      _ = (a+n+1)*Nat.factorial (a+n) := by rw [ih,show a+1+n=a+n+1 by omega]
      _ = _ := by rw [show a+(n+1)=(a+n)+1 by omega,Nat.factorial_succ]

lemma zeta_real_nat_ge_one (k : ℕ) (hk : 1≤k) :
    1≤(riemannZeta (k+1:ℕ)).re := by
  rw [←(zeta_real_nat_power_sum k hk).2]
  have h := (zeta_real_nat_power_sum k hk).1.sum_le_tsum ({1} : Finset ℕ)
    (fun n hn => by positivity)
  simpa using h

lemma zeta_real_nat_le_two_value (k : ℕ) (hk : 1≤k) :
    (riemannZeta (k+1:ℕ)).re≤(riemannZeta 2).re := by
  have hz2 : (∑' n : ℕ, 1/(n:ℝ)^2)=(riemannZeta 2).re := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat] using (zeta_real_nat_power_sum 1 (by norm_num)).2
  rw [←(zeta_real_nat_power_sum k hk).2, ←hz2]
  apply (zeta_real_nat_power_sum k hk).1.tsum_le_tsum ?_
    (zeta_real_nat_power_sum 1 (by norm_num)).1
  intro n
  by_cases hn : n=0
  · simp [hn]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ hn1 (by omega : 2≤k+1))

lemma auxCompletionBound_pos (k : ℕ) (hk : 1≤k) : 0<auxCompletionBound k := by
  have hz := zeta_real_nat_ge_one k hk
  unfold auxCompletionBound
  positivity

lemma auxCompletionBound_uniform_envelope (k : ℕ) (hk : 1≤k) :
    auxCompletionBound k≤64*(riemannZeta 2).re*(8:ℝ)^k := by
  have hz := zeta_real_nat_ge_one k hk
  have hz2 := zeta_real_nat_ge_one 1 (by norm_num)
  have hden : 1≤(2*Real.pi)^(k+1) := one_le_pow₀ (by nlinarith [Real.two_le_pi])
  have hp : 1≤(2:ℝ)^(3*k+4) := one_le_pow₀ (by norm_num)
  unfold auxCompletionBound
  calc
    _ ≤ 2*(riemannZeta (k+1:ℕ)).re*(1+(2:ℝ)^(3*k+4)) :=
      div_le_self (by positivity) hden
    _ ≤ 4*(riemannZeta 2).re*(2:ℝ)^(3*k+4) := by
      have hζ := zeta_real_nat_le_two_value k hk
      nlinarith
    _ = _ := by
      rw [pow_add,pow_mul]
      norm_num
      ring

lemma auxRationalFactor_ne_zero {p : ℂ} (hp : 0<p.re) (hne : p≠1/2) (k : ℕ) :
    auxRationalFactor k p≠0 := by
  apply div_ne_zero (sub_ne_zero.mpr hne)
  apply auxDenominator_ne_zero
  dsimp [auxCompletionAlpha]
  linarith [Nat.cast_nonneg (α:=ℝ) k]

lemma aux_factor_norm_bound (p : ℂ) (j : ℕ) (hj : 1≤j) :
    ‖p+(j:ℂ)+1/2‖≤(1+‖p+1/2‖)*(j:ℝ) := by
  have hjr : (1:ℝ)≤j := by exact_mod_cast hj
  calc
    _ = ‖(p+1/2)+(j:ℂ)‖ := by congr 1; ring
    _ ≤ ‖p+1/2‖+‖(j:ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by rw [Complex.norm_natCast]; nlinarith [norm_nonneg (p+1/2)]

lemma auxDenominator_norm_le_product (p : ℂ) (k : ℕ) :
    ‖∏ j∈Finset.range (k+2), (p+(k+1+j:ℕ)+1/2)‖ ≤
      (1+‖p+1/2‖)^(k+2)*(∏ j∈Finset.range (k+2), ((k+1+j:ℕ):ℝ)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ j∈Finset.range (k+2), (1+‖p+1/2‖)*((k+1+j:ℕ):ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro j hj
      exact aux_factor_norm_bound p _ (by omega)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma auxDenominator_norm_le_power (p : ℂ) (k : ℕ) :
    ‖∏ j∈Finset.range (k+2), (p+(k+1+j:ℕ)+1/2)‖ ≤
      (2*(1+‖p+1/2‖)*(k+1))^(k+2) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _j∈Finset.range (k+2), (2*(1+‖p+1/2‖)*(k+1)) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro j hj
      have hj' : j≤k+1 := by have := Finset.mem_range.mp hj; omega
      apply (aux_factor_norm_bound p _ (by omega)).trans
      have hc : ((k+1+j:ℕ):ℝ)≤2*(k+1) := by exact_mod_cast (show k+1+j≤2*(k+1) by omega)
      nlinarith [norm_nonneg (p+1/2)]
    _ = _ := by simp

lemma aux_filter_ratio_binomial {p : ℂ} (hp : 0<p.re) (hne : p≠1/2) (k : ℕ) :
    (∫ t : ℝ, ‖auxCompletionFilter k t‖)/‖auxRationalFactor k p‖ ≤
      (2/‖p-1/2‖)*(1+‖p+1/2‖)^(k+2)*(k+1)*(4:ℝ)^(k+1) := by
  have ha : 0<‖p-1/2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hden := auxDenominator_ne_zero k p (by dsimp [auxCompletionAlpha]; linarith [Nat.cast_nonneg (α:=ℝ) k])
  have hprod : (∏ j∈Finset.range (k+2), ((k+1+j:ℕ):ℝ)) /
      (Nat.factorial (k+1):ℝ) = (k+1)*((2*k+2).choose (k+1):ℝ) := by
    have hp' := shifted_nat_product_factorial k (k+2)
    have hc := Nat.choose_mul_factorial_mul_factorial (n:=2*k+2) (k:=k+1) (by omega)
    have hkfac : (Nat.factorial k:ℝ)≠0 := by positivity
    have hk1fac : (Nat.factorial (k+1):ℝ)≠0 := by positivity
    have hsub : 2*k+2-(k+1)=k+1 := by omega
    rw [hsub] at hc
    have hpR : (∏ j∈Finset.range (k+2), ((k+1+j:ℕ):ℝ))*(Nat.factorial k:ℝ)=
        (Nat.factorial (2*k+2):ℝ) := by
      exact_mod_cast (by simpa [show k+(k+2)=2*k+2 by omega] using hp')
    have hcR : ((2*k+2).choose (k+1):ℝ)*(Nat.factorial (k+1):ℝ)*
        (Nat.factorial (k+1):ℝ)=(Nat.factorial (2*k+2):ℝ) := by exact_mod_cast hc
    have hrec : (Nat.factorial (k+1):ℝ)=(k+1)*(Nat.factorial k:ℝ) := by rw [Nat.factorial_succ]; norm_cast
    apply (div_eq_iff hk1fac).mpr
    apply mul_right_cancel₀ hkfac
    rw [hpR]
    rw [hcR.symm,hrec]
    ring
  have hchoose : ((2*k+2).choose (k+1):ℝ)≤(4:ℝ)^(k+1) := by
    have h := Nat.choose_le_two_pow (2*k+2) (k+1)
    have he : (2:ℕ)^(2*k+2)=4^(k+1) := by
      rw [show 2*k+2=2*(k+1) by omega,pow_mul]; norm_num
    rw [he] at h
    exact_mod_cast h
  calc
    _ ≤ (2/(Nat.factorial (k+1):ℝ))/‖auxRationalFactor k p‖ :=
      div_le_div_of_nonneg_right (auxCompletionFilter_L1_bound k) (norm_nonneg _)
    _ = (2/‖p-1/2‖)*(‖∏ j∈Finset.range (k+2), (p+(k+1+j:ℕ)+1/2)‖/
      (Nat.factorial (k+1):ℝ)) := by
      rw [auxRationalFactor,norm_div]
      field_simp
    _ ≤ (2/‖p-1/2‖)*((1+‖p+1/2‖)^(k+2)*
      ((∏ j∈Finset.range (k+2), ((k+1+j:ℕ):ℝ))/(Nat.factorial (k+1):ℝ))) := by
      have h := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (auxDenominator_norm_le_product p k)
          (Nat.cast_nonneg (Nat.factorial (k+1)))) (by positivity : 0≤2/‖p-1/2‖)
      simpa only [mul_div_assoc] using h
    _ ≤ _ := by
      rw [hprod]
      have h := mul_le_mul_of_nonneg_left hchoose
        (by positivity : 0≤(2/‖p-1/2‖)*(1+‖p+1/2‖)^(k+2)*(k+1))
      simpa only [mul_assoc] using h

lemma aux_rational_lower_power {p : ℂ} (hp : 0<p.re) (hne : p≠1/2) (k : ℕ) :
    ‖p-1/2‖/(2*(1+‖p+1/2‖)*(k+1))^(k+2) ≤ ‖auxRationalFactor k p‖ := by
  rw [auxRationalFactor,norm_div]
  have hden := auxDenominator_ne_zero k p (by
    dsimp [auxCompletionAlpha]; linarith [Nat.cast_nonneg (α:=ℝ) k])
  exact div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.mpr hden)
    (auxDenominator_norm_le_power p k)

/-- Uniform in k; fixed p may be any genuine right coordinate except the
removable point.  The native-zero instance below discharges that exclusion. -/
lemma aux_completion_ratio_bounds_at_coordinate (p : ℂ) (hp : 0<p.re) (hne : p≠1/2) :
    ∃ Cp : ℝ, 0<Cp ∧ ∀ k : ℕ, 1≤k →
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) ∧
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)/‖auxRationalFactor k p‖≤
        Real.exp (Cp*(k+1)) ∧
      Real.exp (-(k:ℝ)*Real.log (k+1)-Cp*(k+1))≤
        ‖auxRationalFactor k p‖/auxCompletionBound k := by
  let a : ℝ := ‖p-1/2‖
  let D : ℝ := 1+‖p+1/2‖
  let Z : ℝ := 64*(riemannZeta 2).re
  have ha : 0<a := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hD : 1≤D := by dsimp [D]; linarith [norm_nonneg (p+1/2)]
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hz2 : 1≤(riemannZeta 2).re := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat] using zeta_real_nat_ge_one 1 (by norm_num)
  have hZ : 1≤Z := by dsimp [Z]; linarith
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let C₁ : ℝ := 1+|Real.log (2/a)|+2*|Real.log D|+|Real.log 4|
  let C₂ : ℝ := 2+|Real.log a|+2*|Real.log (2*D)|+|Real.log Z|+|Real.log 8|
  let Cp : ℝ := C₁+C₂+1
  have hC₁ : 0≤C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0≤C₂ := by dsimp [C₂]; positivity
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  have hC₁p : C₁≤Cp := by dsimp [Cp]; linarith
  have hC₂p : C₂≤Cp := by dsimp [Cp]; linarith
  refine ⟨Cp,hCp,fun k hk => ⟨auxCompletionFilter_L1_bound k,?_,?_⟩⟩
  · apply (aux_filter_ratio_binomial hp hne k).trans
    have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
    have hn : (1:ℝ)≤k+1 := by linarith
    have hnp : (0:ℝ)<k+1 := by positivity
    have hA : Real.log (2/a)≤|Real.log (2/a)| *(k+1) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hn)
    have hB : ((k:ℝ)+2)*Real.log D≤2*|Real.log D| *(k+1) := by
      have h := mul_le_mul_of_nonneg_left (le_abs_self (Real.log D))
        (by positivity : (0:ℝ)≤k+2)
      have h' := mul_le_mul_of_nonneg_right (show (k:ℝ)+2≤2*(k+1) by linarith)
        (abs_nonneg (Real.log D))
      nlinarith
    have hC : Real.log (k+1)≤(k:ℝ)+1 :=
      (Real.log_le_sub_one_of_pos hnp).trans (by linarith)
    have hD' : ((k:ℝ)+1)*Real.log 4≤|Real.log 4| *(k+1) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_abs_self (Real.log 4)) hnp.le
    have hlog : Real.log ((2/a)*D^(k+2)*(k+1)*(4:ℝ)^(k+1))≤Cp*(k+1) := by
      have heq : Real.log ((2/a)*D^(k+2)*(k+1)*(4:ℝ)^(k+1)) =
          Real.log (2/a)+((k:ℝ)+2)*Real.log D+Real.log (k+1)+((k:ℝ)+1)*Real.log 4 := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
        push_cast
        ring
      rw [heq]
      have h' := mul_le_mul_of_nonneg_right hC₁p hnp.le
      dsimp [C₁] at h'
      nlinarith
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at h
    exact h
  · have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
    have hn : (1:ℝ)≤k+1 := by linarith
    have hnp : (0:ℝ)<k+1 := by positivity
    have hR := aux_rational_lower_power hp hne k
    have hA := auxCompletionBound_uniform_envelope k hk
    have hAp := auxCompletionBound_pos k hk
    have hlow : a/((2*D*(k+1))^(k+2)*(Z*(8:ℝ)^k)) ≤
        ‖auxRationalFactor k p‖/auxCompletionBound k := by
      calc
        _ = (a/(2*D*(k+1))^(k+2))/(Z*(8:ℝ)^k) := (div_div _ _ _).symm
        _ ≤ ‖auxRationalFactor k p‖/(Z*(8:ℝ)^k) :=
          div_le_div_of_nonneg_right hR (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) hAp hA
    apply le_trans ?_ hlow
    have hAa : -(|Real.log a| *(k+1))≤Real.log a := by
      have h := le_mul_of_one_le_right (abs_nonneg (Real.log a)) hn
      linarith [neg_abs_le (Real.log a)]
    have hDD : ((k:ℝ)+2)*Real.log (2*D)≤2*|Real.log (2*D)| *(k+1) := by
      have h := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2*D)))
        (by positivity : (0:ℝ)≤k+2)
      have h' := mul_le_mul_of_nonneg_right (show (k:ℝ)+2≤2*(k+1) by linarith)
        (abs_nonneg (Real.log (2*D)))
      nlinarith
    have hL : Real.log (k+1)≤(k:ℝ)+1 :=
      (Real.log_le_sub_one_of_pos hnp).trans (by linarith)
    have hZZ : Real.log Z≤|Real.log Z| *(k+1) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hn)
    have h8 : (k:ℝ)*Real.log 8≤|Real.log 8| *(k+1) := by
      have h := mul_le_mul_of_nonneg_left (le_abs_self (Real.log 8)) hk0
      nlinarith [abs_nonneg (Real.log 8)]
    have hlog : -(k:ℝ)*Real.log (k+1)-Cp*(k+1)≤
        Real.log (a/((2*D*(k+1))^(k+2)*(Z*(8:ℝ)^k))) := by
      have heq : Real.log (a/((2*D*(k+1))^(k+2)*(Z*(8:ℝ)^k))) =
          Real.log a-((k:ℝ)+2)*Real.log (2*D)-((k:ℝ)+2)*Real.log (k+1)-
            Real.log Z-(k:ℝ)*Real.log 8 := by
        rw [Real.log_div ha.ne' (by positivity),
          Real.log_mul (by positivity) (by positivity),Real.log_pow,
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul hZp.ne' (by positivity),Real.log_pow]
        push_cast
        ring
      rw [heq]
      have h' := mul_le_mul_of_nonneg_right hC₂p hnp.le
      dsimp [C₂] at h'
      nlinarith
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at he
    exact he

/-- Original primary at actual nontrivial right zeros, with one constant
selected before every k.  No zero-free hypothesis is used. -/
theorem aux_completion_ratio_bounds (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    ∃ Cp : ℝ, 0<Cp ∧ ∀ k : ℕ, 1≤k →
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) ∧
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)/‖auxRationalFactor k ((rho:ℂ)-1/2)‖≤
        Real.exp (Cp*(k+1)) ∧
      Real.exp (-(k:ℝ)*Real.log (k+1)-Cp*(k+1))≤
        ‖auxRationalFactor k ((rho:ℂ)-1/2)‖/auxCompletionBound k := by
  have hp : 0<((rho:ℂ)-1/2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hne : (rho:ℂ)-1/2≠1/2 := by
    intro h
    apply rho.property.not_trivial.2
    linear_combination h
  exact aux_completion_ratio_bounds_at_coordinate _ hp hne

end Zeta23.OPICAFollowup
