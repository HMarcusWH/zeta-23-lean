
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

#print axioms nativeAuxiliaryTruncatedMoment_vanishes
#print axioms nativeTruncatedResidualMoment_eq_auxiliary

end Zeta23.OPICAFollowup
