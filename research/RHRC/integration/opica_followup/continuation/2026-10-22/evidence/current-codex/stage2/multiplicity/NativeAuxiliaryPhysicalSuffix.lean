
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

#print axioms nativeAuxiliaryInput_completedPrime
#print axioms native_auxiliary_top_moment

end Zeta23.OPICAFollowup
