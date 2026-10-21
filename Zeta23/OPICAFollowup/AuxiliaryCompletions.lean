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

end Zeta23.OPICAFollowup
