
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

#print axioms nativeTruncatedResidual_memLp_two
#print axioms nativeTruncatedResidual_zero_before

end Zeta23.OPICAFollowup
