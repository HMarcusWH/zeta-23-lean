
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

#print axioms nativeAuxiliaryInput_initial_laplace
#print axioms nativeAuxiliaryInputLaplace_eq_continuation
#print axioms nativeAuxiliaryMoment_integrable

end Zeta23.OPICAFollowup
