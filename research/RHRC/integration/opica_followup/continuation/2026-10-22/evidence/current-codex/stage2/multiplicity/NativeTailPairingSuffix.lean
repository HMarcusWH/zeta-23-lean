
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

#print axioms nativeResidual_laguerre_inner

end Zeta23.OPICAFollowup
