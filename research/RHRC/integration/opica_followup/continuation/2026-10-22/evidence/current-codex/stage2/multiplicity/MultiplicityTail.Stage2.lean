import Zeta23.CCM.NativeCompletionEquation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Convolution
import Zeta23.OPICAFollowup.AuxiliaryCompletions
import Zeta23.OPICAFollowup.UniformSourceBounds
import Zeta23.ExceptionalZero.NativeActualInputZeroJets
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.L2Space

/-!
The genuine monic Laguerre tail test is constructed here with its exact norm,
arbitrary degree, real lower endpoint and both imaginary signs. The full norm
and actual native convolution/top-moment, finite-residual and terminal-memory
primaries are separately proved. The prime field is used through finite history.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter Polynomial
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- The polynomial conjugate of differentiation by exp(-x). -/
def laguerreRodriguesStep (P : Polynomial ℝ) : Polynomial ℝ := P.derivative-P

/-- Monic Laguerre polynomial via the actual Rodrigues operator.
This definition fixes the normalization independently of an orthogonality
claim or a supplied Gram matrix. -/
def monicLaguerre (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1:ℝ)^n)*laguerreRodriguesStep^[n] (Polynomial.X^n)

def laguerreWeightedPair (P Q : Polynomial ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (-x)*P.eval x*Q.eval x

lemma exp_neg_polynomial_integrable (P : Polynomial ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*P.eval x) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1 <;>
      first | rfl | (simp only [Polynomial.eval_add,mul_add]; rfl)
  | monomial n a =>
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := n)
      (b := (1:ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) (by norm_num)
    convert h.const_mul a using 1
    first | rfl | simp only [Real.rpow_one,Real.rpow_natCast,Polynomial.eval_monomial,
      mul_comm,mul_assoc,mul_neg_one]
    rfl

lemma exp_neg_polynomial_tendsto_zero (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-x)*P.eval x) atTop (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add,mul_add,add_zero] using hP.add hQ
  | monomial n a =>
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    simpa only [Polynomial.eval_monomial,mul_comm,mul_left_comm,mul_assoc,mul_zero] using
      h.const_mul a

lemma exp_neg_monomial_integral (n : ℕ) :
    (∫ x : ℝ in Ioi 0, Real.exp (-x)*x^n) = (n.factorial:ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n:ℝ)+1) (r := (1:ℝ)) (by positivity) (by norm_num)
  simpa only [add_sub_cancel_right,Real.rpow_natCast,neg_mul,one_mul,
    Real.one_rpow,mul_one,one_mul,div_one,Real.Gamma_nat_eq_factorial,mul_comm] using h

lemma laguerreWeightedPair_integrable (P Q : Polynomial ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*P.eval x*Q.eval x) (Ioi 0) := by
  simpa only [Polynomial.eval_mul,mul_assoc] using exp_neg_polynomial_integrable (P*Q)

lemma laguerreWeightedPair_const_mul_left (a : ℝ) (P Q : Polynomial ℝ) :
    laguerreWeightedPair (Polynomial.C a*P) Q=a*laguerreWeightedPair P Q := by
  unfold laguerreWeightedPair
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  simp_rw [show ∀ x : ℝ, Real.exp (-x)*(a*P.eval x)*Q.eval x=
    a*(Real.exp (-x)*P.eval x*Q.eval x) by intro x; ring]
  rw [integral_const_mul]

lemma laguerreWeightedPair_const_right (P : Polynomial ℝ) (a : ℝ) :
    laguerreWeightedPair P (Polynomial.C a) =
      a*(∫ x : ℝ in Ioi 0, Real.exp (-x)*P.eval x) := by
  unfold laguerreWeightedPair
  simp only [Polynomial.eval_C]
  rw [integral_mul_const]
  ring

/-- Full integration by parts on (0,infinity); the origin term is displayed
before the vanishing hypothesis is used. -/
lemma laguerre_weighted_ibp (P Q : Polynomial ℝ) :
    laguerreWeightedPair (laguerreRodriguesStep P) Q+
      laguerreWeightedPair P Q.derivative = -P.eval 0*Q.eval 0 := by
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => Real.exp (-x)*(P*Q).eval x)
      (Real.exp (-x)*((laguerreRodriguesStep P)*Q+P*Q.derivative).eval x) x := by
    have h := ((hasDerivAt_neg x).exp).mul ((P*Q).hasDerivAt x)
    convert h using 1 <;>
      first | rfl | (simp only [Polynomial.derivative_mul,Polynomial.eval_mul,
        Polynomial.eval_add,laguerreRodriguesStep,Polynomial.eval_sub]; ring)
  have hi := exp_neg_polynomial_integrable ((laguerreRodriguesStep P)*Q+P*Q.derivative)
  have hz := exp_neg_polynomial_tendsto_zero (P*Q)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x (_hx : x∈Ici (0:ℝ)) => hd x) hi hz
  simp only [Polynomial.eval_add,Polynomial.eval_mul,mul_add,←mul_assoc] at h
  rw [integral_add (laguerreWeightedPair_integrable (laguerreRodriguesStep P) Q)
    (laguerreWeightedPair_integrable P Q.derivative)] at h
  simpa only [Real.exp_zero,neg_zero,one_mul,Polynomial.eval_mul,zero_sub,
    neg_mul,laguerreWeightedPair,mul_assoc] using h

lemma laguerre_step_divisible {n : ℕ} {P : Polynomial ℝ}
    (hP : (Polynomial.X:Polynomial ℝ)^(n+1)∣P) :
    (Polynomial.X:Polynomial ℝ)^n∣laguerreRodriguesStep P := by
  have hd := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd 1 hP
  simp only [Nat.add_sub_cancel,Function.iterate_one] at hd
  have hp : (Polynomial.X:Polynomial ℝ)^n∣P :=
    dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) hP
  exact dvd_sub hd hp

/-- n integrations by parts, with all origin terms justified by divisibility.
No summability or orthogonality is built into a data structure. -/
lemma laguerre_iterated_ibp (n : ℕ) (P Q : Polynomial ℝ)
    (hP : (Polynomial.X:Polynomial ℝ)^n∣P) :
    laguerreWeightedPair (laguerreRodriguesStep^[n] P) Q =
      (-1:ℝ)^n*laguerreWeightedPair P (Polynomial.derivative^[n] Q) := by
  induction n generalizing P Q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (laguerreRodriguesStep P) Q (laguerre_step_divisible hP)]
    have hP0 : P.eval 0=0 := by
      obtain ⟨S,hS⟩ := hP
      rw [hS,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
        zero_pow (Nat.succ_ne_zero _),zero_mul]
    have h := laguerre_weighted_ibp P (Polynomial.derivative^[n] Q)
    rw [hP0,neg_zero,zero_mul] at h
    have heq : laguerreWeightedPair (laguerreRodriguesStep P)
        (Polynomial.derivative^[n] Q) =
        -laguerreWeightedPair P ((Polynomial.derivative^[n] Q).derivative) := by linarith
    rw [heq,Function.iterate_succ_apply',pow_succ]
    ring

lemma laguerre_step_degree_le (P : Polynomial ℝ) :
    (laguerreRodriguesStep P).natDegree≤P.natDegree := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le (Polynomial.natDegree_derivative_le P |>.trans (Nat.sub_le _ _)) le_rfl

lemma laguerre_iterate_degree_le (j : ℕ) (P : Polynomial ℝ) :
    (laguerreRodriguesStep^[j] P).natDegree≤P.natDegree := by
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (laguerre_step_degree_le P)

lemma laguerre_step_top_coeff (P : Polynomial ℝ) (n : ℕ) (hP : P.natDegree≤n) :
    (laguerreRodriguesStep P).coeff n = -P.coeff n := by
  have hzero : P.coeff (n+1)=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [laguerreRodriguesStep,Polynomial.coeff_sub,Polynomial.coeff_derivative,
    hzero,zero_mul,zero_sub]

lemma laguerre_iterate_top_coeff (n j : ℕ) :
    (laguerreRodriguesStep^[j] (Polynomial.X^n:Polynomial ℝ)).coeff n=(-1:ℝ)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',laguerre_step_top_coeff _ n
      ((laguerre_iterate_degree_le j _).trans (by simp)),ih,pow_succ]
    ring

lemma monicLaguerre_natDegree_le (n : ℕ) : (monicLaguerre n).natDegree≤n := by
  exact (Polynomial.natDegree_mul_le ..).trans (by
    simpa only [monicLaguerre,Polynomial.natDegree_C,zero_add,Polynomial.natDegree_X_pow] using
      laguerre_iterate_degree_le n (Polynomial.X^n:Polynomial ℝ))

lemma monicLaguerre_top_coeff (n : ℕ) : (monicLaguerre n).coeff n=1 := by
  rw [monicLaguerre,Polynomial.coeff_C_mul,laguerre_iterate_top_coeff,
    ←pow_add,show n+n=2*n by omega,pow_mul]
  norm_num

lemma monicLaguerre_monic (n : ℕ) : (monicLaguerre n).Monic := by
  have hn : (monicLaguerre n).natDegree=n := le_antisymm (monicLaguerre_natDegree_le n)
    (Polynomial.le_natDegree_of_ne_zero (by rw [monicLaguerre_top_coeff]; norm_num))
  exact show (monicLaguerre n).leadingCoeff=1 by
    rw [Polynomial.leadingCoeff,hn,monicLaguerre_top_coeff]

lemma polynomial_top_iterated_derivative (P : Polynomial ℝ) (n : ℕ)
    (hP : P.natDegree≤n) :
    Polynomial.derivative^[n] P = Polynomial.C ((n.factorial:ℝ)*P.coeff n) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j=0
  · subst j
    simp [Nat.descFactorial_self,nsmul_eq_mul]
  · have hcoeff : P.coeff (j+n)=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hcoeff,hj]

lemma monicLaguerre_top_derivative (n : ℕ) :
    Polynomial.derivative^[n] (monicLaguerre n)=Polynomial.C (n.factorial:ℝ) := by
  rw [polynomial_top_iterated_derivative _ n (monicLaguerre_natDegree_le n),
    monicLaguerre_top_coeff,mul_one]

lemma monicLaguerre_orthogonality (n : ℕ) (Q : Polynomial ℝ) (hQ : Q.natDegree<n) :
    laguerreWeightedPair (monicLaguerre n) Q=0 := by
  rw [monicLaguerre,laguerreWeightedPair_const_mul_left,
    laguerre_iterated_ibp n _ Q dvd_rfl,Polynomial.iterate_derivative_eq_zero hQ]
  simp [laguerreWeightedPair]

lemma monicLaguerre_exact_norm_sq (n : ℕ) :
    (∫ x : ℝ in Ioi 0, Real.exp (-x)*((monicLaguerre n).eval x)^2) =
      (n.factorial:ℝ)^2 := by
  have hp : (∫ x : ℝ in Ioi 0, Real.exp (-x)*((monicLaguerre n).eval x)^2)=
      laguerreWeightedPair (monicLaguerre n) (monicLaguerre n) := by
    simp only [laguerreWeightedPair,pow_two,mul_assoc]
  rw [hp]
  rw [monicLaguerre,laguerreWeightedPair_const_mul_left,
    laguerre_iterated_ibp n _ _ dvd_rfl]
  change (-1:ℝ)^n*((-1:ℝ)^n*
    laguerreWeightedPair (Polynomial.X^n) (Polynomial.derivative^[n] (monicLaguerre n)))=_
  rw [monicLaguerre_top_derivative,laguerreWeightedPair_const_right]
  simp only [Polynomial.eval_pow,Polynomial.eval_X]
  rw [exp_neg_monomial_integral]
  have hsign : (-1:ℝ)^n*(-1:ℝ)^n=1 := by
    rw [←pow_add,show n+n=2*n by omega,pow_mul]; norm_num
  calc
    _ = ((-1:ℝ)^n*(-1:ℝ)^n)*(n.factorial:ℝ)^2 := by ring
    _ = _ := by rw [hsign,one_mul]

/-- Zero-order convention n=0 is not omitted. The actual tail test includes
exp(-conj(p)*t), rather than a real-only or wrongly conjugated exponential. -/
def monicLaguerreTail (n : ℕ) (p : ℂ) (T : ℝ) (t : ℝ) : ℂ :=
  (Ici T).indicator (fun t =>
    (((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)):ℝ)*
      Complex.exp (-(starRingEnd ℂ p)*(t:ℂ))) t

def laguerreSquareProfile (n : ℕ) (x : ℝ) : ℝ :=
  (Ici (0:ℝ)).indicator (fun x => Real.exp (-x)*((monicLaguerre n).eval x)^2) x

lemma laguerreSquareProfile_integrable (n : ℕ) : Integrable (laguerreSquareProfile n) := by
  have h := laguerreWeightedPair_integrable (monicLaguerre n) (monicLaguerre n)
  have hc : IntegrableOn (fun x : ℝ => Real.exp (-x)*((monicLaguerre n).eval x)^2)
      (Ici 0) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    simpa only [pow_two,mul_assoc] using h
  exact hc.integrable_indicator measurableSet_Ici

lemma laguerreSquareProfile_integral (n : ℕ) :
    (∫ x : ℝ,laguerreSquareProfile n x)=(n.factorial:ℝ)^2 := by
  unfold laguerreSquareProfile
  rw [integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi,monicLaguerre_exact_norm_sq]

lemma monicLaguerreTail_norm_sq (n : ℕ) (p : ℂ) (T t : ℝ) (hp : 0<p.re) :
    ‖monicLaguerreTail n p T t‖^2 =
      (((2*p.re)^n)⁻¹)^2*Real.exp (-2*p.re*T)*
        laguerreSquareProfile n (2*p.re*(t-T)) := by
  have ha : 0<2*p.re := by linarith
  by_cases ht : T≤t
  · have hu : 0≤2*p.re*(t-T) := mul_nonneg ha.le (sub_nonneg.mpr ht)
    have htmem : t ∈ Ici T := ht
    have humem : 2*p.re*(t-T) ∈ Ici (0:ℝ) := hu
    simp only [monicLaguerreTail,indicator_of_mem htmem,laguerreSquareProfile,
      indicator_of_mem humem,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
      Complex.neg_re,Complex.conj_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero,mul_pow]
    have he : (Real.exp (-p.re*t))^2=
        Real.exp (-2*p.re*T)*Real.exp (-(2*p.re*(t-T))) := by
      rw [←Real.exp_nat_mul,←Real.exp_add]; congr 1; ring
    rw [he]
    simp only [sq_abs]
    ring
  · have hu : ¬0≤2*p.re*(t-T) := by nlinarith
    simp [monicLaguerreTail,laguerreSquareProfile,ht,hu]

lemma monicLaguerreTail_memLp (n : ℕ) (p : ℂ) (T : ℝ) (hp : 0<p.re) :
    MemLp (monicLaguerreTail n p T) 2 volume := by
  have hm : AEStronglyMeasurable (monicLaguerreTail n p T) volume := by
    apply AEStronglyMeasurable.indicator _ measurableSet_Ici
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)):ℝ)*
      Complex.exp (-(starRingEnd ℂ p)*(t:ℂ)))).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have h := ((laguerreSquareProfile_integrable n).comp_mul_left'
    (by positivity : (2*p.re)≠0)).comp_sub_right T
  exact (h.const_mul ((((2*p.re)^n)⁻¹)^2*Real.exp (-2*p.re*T))).congr
    (Filter.Eventually.of_forall (fun t => (monicLaguerreTail_norm_sq n p T t hp).symm))

lemma monicLaguerreTail_integral_norm_sq (n : ℕ) (p : ℂ) (T : ℝ) (hp : 0<p.re) :
    (∫ t : ℝ, ‖monicLaguerreTail n p T t‖^2)=
      Real.exp (-2*p.re*T)*(n.factorial:ℝ)^2/(2*p.re)^(2*n+1) := by
  simp_rw [monicLaguerreTail_norm_sq n p T _ hp]
  rw [integral_const_mul]
  have hshift : (∫ t : ℝ,laguerreSquareProfile n (2*p.re*(t-T)))=
      ∫ u : ℝ,laguerreSquareProfile n (2*p.re*u) :=
    integral_sub_right_eq_self (fun u : ℝ => laguerreSquareProfile n (2*p.re*u)) T
  rw [hshift,Measure.integral_comp_mul_left (laguerreSquareProfile n) (2*p.re),
    smul_eq_mul,abs_of_pos (inv_pos.mpr (by positivity : 0<2*p.re)),
    laguerreSquareProfile_integral]
  field_simp
  ring

/-- The actual L2 vector is constructed from the actual integrable tail test. -/
def monicLaguerreTailL2 (n : ℕ) (p : ℂ) (T : ℝ) (hp : 0<p.re) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
  (monicLaguerreTail_memLp n p T hp).toLp (monicLaguerreTail n p T)

/-- Original Laguerre primary, full m>=1, delta>0, T real scope.
The output gives the actual representative and squared norm as well as the
paper's norm, eliminating any hidden choice of normalization. -/
theorem laguerre_tail_norm (m : ℕ) (hm : 1≤m) (p : ℂ) (hp : 0<p.re) (T : ℝ) :
    (monicLaguerre (m-1)).Monic ∧
    (∀ Q : Polynomial ℝ, Q.natDegree<m-1 →
      laguerreWeightedPair (monicLaguerre (m-1)) Q=0) ∧
    MemLp (monicLaguerreTail (m-1) p T) 2 volume ∧
    (monicLaguerreTailL2 (m-1) p T hp : ℝ→ℂ)=ᵐ[volume]
      monicLaguerreTail (m-1) p T ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖^2=
      Real.exp (-2*p.re*T)*((m-1).factorial:ℝ)^2/(2*p.re)^(2*(m-1)+1) ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖=
      Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2) := by
  have hnorm : ‖monicLaguerreTailL2 (m-1) p T hp‖^2=
      ∫ t : ℝ, ‖monicLaguerreTail (m-1) p T t‖^2 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(monicLaguerreTail_memLp (m-1) p T hp).coeFn_toLp] with t ht
    dsimp only [monicLaguerreTailL2]
    rw [ht,real_inner_self_eq_norm_sq]
  have hsq := hnorm.trans (monicLaguerreTail_integral_norm_sq (m-1) p T hp)
  refine ⟨monicLaguerre_monic _,fun Q hQ => monicLaguerre_orthogonality _ Q hQ,
    monicLaguerreTail_memLp _ p T hp,
    (monicLaguerreTail_memLp _ p T hp).coeFn_toLp,hsq,?_⟩
  have hMp : (0:ℝ)<2*p.re := by linarith
  have hright : 0≤Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2) := by
    positivity
  have hcast : ((m:ℝ)-1/2)*2=(2*(m-1)+1:ℕ) := by
    have hmreal : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by
      rw [Nat.cast_sub hm]; norm_num
    push_cast
    rw [hmreal]
    ring
  have hden : ((2*p.re)^((m:ℝ)-1/2))^2=(2*p.re)^(2*(m-1)+1) := by
    rw [←Real.rpow_natCast ((2*p.re)^((m:ℝ)-1/2)) 2,←Real.rpow_mul hMp.le]
    norm_num only [Nat.cast_ofNat]
    rw [hcast,Real.rpow_natCast]
  have he : (Real.exp (-p.re*T))^2=Real.exp (-2*p.re*T) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hsquare : (Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2))^2=
      Real.exp (-2*p.re*T)*((m-1).factorial:ℝ)^2/(2*p.re)^(2*(m-1)+1) := by
    calc
      _ = (Real.exp (-p.re*T))^2*((m-1).factorial:ℝ)^2/
          ((2*p.re)^((m:ℝ)-1/2))^2 := by ring
      _ = _ := by rw [he,hden]
  exact (sq_eq_sq₀ (norm_nonneg _) hright).mp (hsq.trans hsquare.symm)

end Zeta23.OPICAFollowup


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
  rw [←Real.sqrt_eq_rpow,show -a*T=-(a*T) by ring,Real.exp_neg]
  have hs : Real.sqrt (2*a)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  field_simp [hs,Real.exp_ne_zero]


theorem nativeAuxiliaryTruncatedVector_tail_norm (k d : ℕ) (T : ℝ) (hk : 1≤k) :
    ‖nativeTailRestriction T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2)‖≤
      auxCompletionBound k/Real.sqrt (2*auxCompletionAlpha k)*tailMemory (auxCompletionAlpha k) d T := by
  let a := auxCompletionAlpha k
  let A := auxCompletionBound k
  let J := tailMemory a d T
  have ha : 0<a := by dsimp [a,auxCompletionAlpha]; positivity
  have hA : 0<A := auxCompletionBound_pos k hk
  have hJ : 0≤J := tailMemory_nonneg a d T
  have hdom : ‖nativeTailRestriction T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2)‖≤
      ‖nativeTailExponentialVector a T (A*J) ha‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [nativeTailRestriction_coe T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2),
      nativeAuxiliaryTruncatedVector_coe k d T hk,
      nativeTailExponentialVector_coe a T (A*J) ha] with t htail hf hg
    rw [htail]
    by_cases ht : t∈Ici T
    · rw [indicator_of_mem ht,hf,hg,indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hA.le hJ) (Real.exp_nonneg _))]
      exact (nativeAuxiliaryTruncatedImage_memory_bound k d T t hk).trans_eq (by dsimp [A,a,J]; ring)
    · rw [indicator_of_notMem ht,norm_zero]
      exact norm_nonneg _
  exact hdom.trans_eq (by rw [nativeTailExponentialVector_norm a T (A*J) ha (mul_nonneg hA.le hJ)]; ring)

theorem nativeResidual_norm_le_input_add_memory (k d : ℕ) (T : ℝ) (hk : 1≤k) :
    ‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖≤
      ‖nativeAuxiliaryStableVector k d‖+
        auxCompletionBound k/Real.sqrt (2*auxCompletionAlpha k)*tailMemory (auxCompletionAlpha k) d T := by
  have hid : (nativeTruncatedResidualVector k d T:NativeCompletionL2)=
      nativeTailRestriction T (nativeAuxiliaryStableVector k d:NativeCompletionL2)-
        nativeTailRestriction T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2) := by
    apply Lp.ext
    filter_upwards [nativeTruncatedResidualVector_coe k d T hk,
      Lp.coeFn_sub (nativeTailRestriction T (nativeAuxiliaryStableVector k d:NativeCompletionL2))
        (nativeTailRestriction T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2)),
      nativeTailRestriction_coe T (nativeAuxiliaryStableVector k d:NativeCompletionL2),
      nativeTailRestriction_coe T (nativeAuxiliaryTruncatedVector k d T:NativeCompletionL2),
      nativeAuxiliaryStableVector_coe_input k d,nativeAuxiliaryTruncatedVector_coe k d T hk]
        with t hr hsub hty htf hy hf
    rw [hr,hsub,Pi.sub_apply,hty,htf]
    by_cases ht : t∈Ici T
    · rw [indicator_of_mem ht,indicator_of_mem ht,hy,hf]
      rfl
    · rw [indicator_of_notMem ht,indicator_of_notMem ht,sub_zero]
      exact nativeTruncatedResidual_zero_before k d T (lt_of_not_ge ht)
  rw [hid]
  exact (norm_sub_le _ _).trans
    (add_le_add (nativeTailRestriction_norm_le T (nativeAuxiliaryStableVector k d:NativeCompletionL2))
      (nativeAuxiliaryTruncatedVector_tail_norm k d T hk))

/-- Exact A6, using only the finite prime-field history and the actually
stable completed input. The memory is the weighted L1 integral. -/
theorem native_terminal_memory_lower (k d : ℕ) (hk : 1≤k)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) (T : ℝ) :
    Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k*
      max (nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
        Real.exp (((rho:ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0≤
          tailMemory (auxCompletionAlpha k) d T := by
  have ha : 0<auxCompletionAlpha k := by dsimp [auxCompletionAlpha]; positivity
  have hA : 0<auxCompletionBound k := auxCompletionBound_pos k hk
  have hs : 0<Real.sqrt (2*auxCompletionAlpha k) := Real.sqrt_pos.mpr (by positivity)
  have hJ : 0≤tailMemory (auxCompletionAlpha k) d T := tailMemory_nonneg _ _ _
  have hlo := nativeResidual_tail_lower_bound k d T hk rho hright
  have hup := nativeResidual_norm_le_input_add_memory k d T hk
  have hdiff : nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
      Real.exp (((rho:ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖≤
        auxCompletionBound k/Real.sqrt (2*auxCompletionAlpha k)*tailMemory (auxCompletionAlpha k) d T := by
    linarith
  have hm := max_le hdiff
    (mul_nonneg (div_nonneg hA.le hs.le) hJ)
  calc
    _ ≤ (Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k)*
        ((auxCompletionBound k/Real.sqrt (2*auxCompletionAlpha k))*tailMemory (auxCompletionAlpha k) d T) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg hs.le hA.le)
    _ = _ := by field_simp [hA.ne',hs.ne']


end Zeta23.OPICAFollowup
