
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

#print axioms native_auxiliary_tail_residual_lower

end Zeta23.OPICAFollowup
