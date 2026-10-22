import Zeta23.OPICAFollowup.AuxiliaryCompletions
import Zeta23.OPICAFollowup.UniformSourceBounds
import Zeta23.ExceptionalZero.NativeActualInputZeroJets
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.L2Space

/-!
The genuine monic Laguerre tail test is constructed here with its exact norm,
arbitrary degree, real lower endpoint and both imaginary signs. The full norm
root has independent type/domain consumers. Native convolution/top-moment,
finite-residual and terminal-memory primaries remain separate obligations.
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
