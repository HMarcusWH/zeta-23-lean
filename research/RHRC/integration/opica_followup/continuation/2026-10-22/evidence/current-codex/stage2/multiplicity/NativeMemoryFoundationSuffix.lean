
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

#print axioms nativeAuxiliaryTruncatedImage_memory_bound
#print axioms nativeTailExponentialVector_norm

end Zeta23.OPICAFollowup
