
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

#print axioms native_terminal_memory_lower

end Zeta23.OPICAFollowup
