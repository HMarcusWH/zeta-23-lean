import Zeta23.ExceptionalZero.NativeActualKernelZeroJets
import Zeta23.CCM.NativeCompletedInputZetaLaplace

/-!
# The actual physical completed input has the nonzero zero jet

The physical transform is identified on a genuine neighborhood before
transporting its order and derivatives. The right-side actual zero,
positive damping, multiplicity and causal witness are the existing ones.
The source is the unchanged single-Q transform of j=P²q. No input jet,
visibility, prime-field membership or range conclusion is a caller premise.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

theorem nativeCompletedInputCausalLaplaceMoment_zero_damping_shift
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) :
    nativeCausalLaplaceMoment w 0
        (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2) =
      ∫ t : ℝ, Complex.exp (-(w + (epsilon : ℂ)) * (t : ℂ)) *
        (nativeCompletedInput t : ℂ) := by
  rw [← nativeCausalExponentialWitness_inner_eq_laplaceMoment w hw 0]
  simpa only [pow_zero, one_mul] using
    nativeCausalExponentialWitness_inner_completedInput w hw 0 epsilon hepsilon

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

theorem nativeActualInputLaplace_eventuallyEq_multiplier
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re)
    (hne : w + (epsilon : ℂ) ≠ (1 / 2 : ℂ)) :
    (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0
      (CCM.nativeCompletedInputCausalL2 epsilon hepsilon : CCM.NativeCompletionL2)) =ᶠ[𝓝 w]
      fun z => nativeZeroJetInputMultiplier (z + (epsilon : ℂ)) := by
  have hpos : 0 < (w + (epsilon : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hwN : ∀ᶠ z in 𝓝 w, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hposN : ∀ᶠ z in 𝓝 w, 0 < (z + (epsilon : ℂ)).re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp
      (continuous_id.add continuous_const))).mem_nhds hpos
  have hneN : ∀ᶠ z in 𝓝 w, z + (epsilon : ℂ) ≠ (1 / 2 : ℂ) :=
    (continuous_id.add continuous_const).continuousAt.eventually_ne hne
  filter_upwards [hwN, hposN, hneN] with z hz hzpos hzne
  rw [CCM.nativeCompletedInputCausalLaplaceMoment_zero_damping_shift epsilon hepsilon z hz,
    CCM.nativeCompletedInput_complexLaplace hzpos hzne, nativeZeroJetInputMultiplier]
  ring

private theorem centered_zero_ne_half (rho : zetaZeroConfig.carrier) :
    (rho : ℂ) - 1 / 2 ≠ (1 / 2 : ℂ) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  intro h
  apply hrho.not_trivial.2
  linear_combination h

theorem nativeActualInputLaplace_order_of_zero
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) (w : ℂ) (hw : 0 < w.re)
    (hcenter : w + (epsilon : ℂ) = (rho : ℂ) - 1 / 2) :
    analyticOrderAt (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0
      (CCM.nativeCompletedInputCausalL2 epsilon hepsilon : CCM.NativeCompletionL2)) w =
        (zeroMult (rho : ℂ) - 1 : ℕ) := by
  have hne : w + (epsilon : ℂ) ≠ (1 / 2 : ℂ) := by
    rw [hcenter]
    exact centered_zero_ne_half rho
  rw [analyticOrderAt_congr
    (nativeActualInputLaplace_eventuallyEq_multiplier epsilon hepsilon w hw hne)]
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + (epsilon : ℂ)) w := by fun_prop
  have hd : deriv (fun z : ℂ => z + (epsilon : ℂ)) w ≠ 0 := by
    simp only [deriv_add_const, deriv_id'']
    exact one_ne_zero
  have hord := analyticOrderAt_comp_of_deriv_ne_zero (f := nativeZeroJetInputMultiplier) hshift hd
  change analyticOrderAt (fun z : ℂ => nativeZeroJetInputMultiplier (z + (epsilon : ℂ))) w = _ at hord
  rw [hord, hcenter]
  exact nativeZeroJetInputMultiplier_order rho hoff

private theorem nativeActualInputLaplace_leadingJet
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (rho : zetaZeroConfig.carrier)
    (w : ℂ) (hw : 0 < w.re)
    (hcenter : w + (epsilon : ℂ) = (rho : ℂ) - 1 / 2) :
    (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
      CCM.nativeCausalLaplaceMoment w (zeroMult (rho : ℂ) - 1)
        (CCM.nativeCompletedInputCausalL2 epsilon hepsilon : CCM.NativeCompletionL2) =
      -(CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        CCM.nativeOriginalSourceLaplace ((rho : ℂ) - 1 / 2)) *
          iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ) := by
  have hne : w + (epsilon : ℂ) ≠ (1 / 2 : ℂ) := by
    rw [hcenter]
    exact centered_zero_ne_half rho
  have hev := nativeActualInputLaplace_eventuallyEq_multiplier epsilon hepsilon w hw hne
  have hd := hev.iteratedDeriv_eq (zeroMult (rho : ℂ) - 1)
  rw [CCM.nativeCausalLaplaceMoment_iteratedDeriv w hw _] at hd
  have htranslated : iteratedDeriv (zeroMult (rho : ℂ) - 1)
      (fun z : ℂ => nativeZeroJetInputMultiplier (z + (epsilon : ℂ))) w =
        iteratedDeriv (zeroMult (rho : ℂ) - 1) nativeZeroJetInputMultiplier
          ((rho : ℂ) - 1 / 2) := by
    simpa only [hcenter] using congrFun
      (iteratedDeriv_comp_add_const (zeroMult (rho : ℂ) - 1)
        nativeZeroJetInputMultiplier (epsilon : ℂ)) w
  exact hd.trans (htranslated.trans (nativeZeroJetInputMultiplier_jet rho))

/-- The actual physical pairing, including its exact multiplicity phase.
The zeta jet is an iterated derivative, so no factorial is inserted. -/
theorem nativeCompletedInput_zeroJet_value (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le) =
      (-1 : ℂ) ^ zeroMult (rho : ℂ) *
        CCM.nativeCompletionRationalMultiplier ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        CCM.nativeOriginalSourceLaplace ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (nativeZeroJetRightZero rho : ℂ) := by
  have hj := nativeActualInputLaplace_leadingJet (nativeZeroJetDamping rho)
    (nativeZeroJetDamping_pos rho hoff).le (nativeZeroJetRightZero rho)
    (nativeZeroJetParameter rho) (nativeZeroJetParameter_re_pos rho hoff)
    (nativeZeroJetParameter_add_damping rho)
  rw [nativeZeroJetRightZero_mult] at hj
  have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  have hsucc : zeroMult (rho : ℂ) - 1 + 1 = zeroMult (rho : ℂ) := by omega
  have hphase : (-1 : ℂ) ^ zeroMult (rho : ℂ) =
      -((-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1)) := by
    calc
      (-1 : ℂ) ^ zeroMult (rho : ℂ) =
          (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1 + 1) := congrArg _ hsucc.symm
      _ = _ := by rw [pow_succ]; ring
  have hcancel : (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
      (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  unfold nativeZeroJetAdjointWitness
  rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment]
  calc
    _ = ((-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
        (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1)) *
          CCM.nativeCausalLaplaceMoment (nativeZeroJetParameter rho) (zeroMult (rho : ℂ) - 1)
            (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
              (nativeZeroJetDamping_pos rho hoff).le : CCM.NativeCompletionL2) := by
      rw [hcancel, one_mul]
    _ = (-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
        ((-1 : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
          CCM.nativeCausalLaplaceMoment (nativeZeroJetParameter rho) (zeroMult (rho : ℂ) - 1)
            (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
              (nativeZeroJetDamping_pos rho hoff).le : CCM.NativeCompletionL2)) := by ring
    _ = _ := by rw [hj, hphase]; ring

theorem nativeCompletedInput_zeroJet_ne_zero (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le) ≠ 0 := by
  rw [nativeCompletedInput_zeroJet_value]
  have hright : (nativeZeroJetRightZero rho : ℂ).re ≠ 1 / 2 :=
    ne_of_gt (nativeZeroJetRightZero_re_gt_half rho hoff)
  simpa only [nativeZeroJetRightZero_mult] using
    nativeZeroJetSourceFactor_ne_zero (nativeZeroJetRightZero rho) hright

theorem nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le ∉
      closure (Set.range (CCM.nativeDampedCompletionCausalL2Operator
        (nativeZeroJetDamping rho) (nativeZeroJetDamping_pos rho hoff).le)) := by
  apply CCM.nativeCompletedInput_not_mem_rangeClosure_of_moments
    (nativeZeroJetDamping rho) (nativeZeroJetDamping_pos rho hoff).le
    (nativeZeroJetParameter rho) (nativeZeroJetParameter_re_pos rho hoff)
    (zeroMult (rho : ℂ) - 1)
  · intro j hj
    have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
    exact nativeZeroJet_kernelMoments_eq_zero rho hoff j (by omega)
  · rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment]
    exact nativeCompletedInput_zeroJet_ne_zero rho hoff

theorem nativeCompletedInput_zeroJet_residual_pairing
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) (n : ℕ) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (CCM.nativeCompletedInputResidualIterate (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le n) =
      inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (CCM.nativeAdjointResidualIterate _ _ _ (n + 1)) = _
    rw [CCM.nativeAdjointResidualIterate_succ, inner_sub_right,
      nativeZeroJet_annihilates_range, sub_zero]
    exact ih

theorem nativeCompletedInput_zeroJet_residual_lower
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) (n : ℕ) :
    0 < ‖inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le)‖ / ‖nativeZeroJetAdjointWitness rho hoff‖ ∧
      ‖inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le)‖ / ‖nativeZeroJetAdjointWitness rho hoff‖ ≤
        ‖CCM.nativeCompletedInputResidualIterate (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le n‖ := by
  have hpsi : 0 < ‖nativeZeroJetAdjointWitness rho hoff‖ :=
    norm_pos_iff.mpr (nativeZeroJetAdjointWitness_ne_zero rho hoff)
  refine ⟨div_pos (norm_pos_iff.mpr (nativeCompletedInput_zeroJet_ne_zero rho hoff)) hpsi, ?_⟩
  apply (div_le_iff₀ hpsi).mpr
  rw [← nativeCompletedInput_zeroJet_residual_pairing rho hoff n, mul_comm]
  exact norm_inner_le_norm _ _

end Zeta23.ExceptionalZero

#print axioms Zeta23.CCM.nativeCompletedInputCausalLaplaceMoment_zero_damping_shift
#print axioms Zeta23.ExceptionalZero.nativeActualInputLaplace_eventuallyEq_multiplier
#print axioms Zeta23.ExceptionalZero.nativeActualInputLaplace_order_of_zero
#print axioms Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_value
#print axioms Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_ne_zero
#print axioms Zeta23.ExceptionalZero.nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_residual_pairing
#print axioms Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_residual_lower
