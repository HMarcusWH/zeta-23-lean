
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

#print axioms nativeAuxiliaryMoment_vanishes_below
#print axioms nativeAuxiliaryMoment_top_value

end Zeta23.OPICAFollowup
