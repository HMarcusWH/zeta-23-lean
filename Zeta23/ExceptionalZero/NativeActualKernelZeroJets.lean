import Zeta23.ExceptionalZero.NativeRangeZeroJetObstruction
import Zeta23.CCM.NativePositiveCompletionComplexLaplace

/-!
# Actual zeta-zero jets annihilate the actual damped causal completion

The literal floor-kernel transform theorem discharges the kernel moments.
The right-side selection and finite actual multiplicity determine a genuine
nonzero causal L2 witness. No kernel-moment or range-annihilation premise is
supplied by the caller. Visibility of the actual input is a separate proof.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

theorem nativeCompletionKernelLaplaceMoment_zero_damping_shift (epsilon : ℝ) (w : ℂ) :
    nativeCompletionKernelLaplaceMoment epsilon w 0 =
      nativePositiveCompletionLaplace (w + (epsilon : ℂ)) := by
  unfold nativeCompletionKernelLaplaceMoment nativePositiveCompletionLaplace
  apply integral_congr_ae
  filter_upwards with t
  simp only [pow_zero, mul_one, nativeDampedCompletionKernel, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg]
  have he : Complex.exp (-(epsilon : ℂ) * (t : ℂ)) * Complex.exp (-w * (t : ℂ)) =
      Complex.exp (-(w + (epsilon : ℂ)) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (-(epsilon : ℂ) * (t : ℂ)) * Complex.exp (-w * (t : ℂ))) *
        (nativePositiveCompletion t : ℂ) := by ring
    _ = _ := by rw [he]

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

theorem nativeActualKernelLaplace_order_of_zero
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (rho : zetaZeroConfig.carrier)
    (w : ℂ) (hw : 0 < w.re)
    (hcenter : w + (epsilon : ℂ) = (rho : ℂ) - 1 / 2) :
    analyticOrderAt (fun z : ℂ => CCM.nativeCompletionKernelLaplaceMoment epsilon z 0) w =
      (zeroMult (rho : ℂ) : ℕ∞) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hpos : 0 < (w + (epsilon : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hne : w + (epsilon : ℂ) ≠ (1 / 2 : ℂ) := by
    intro h
    apply hrho.not_trivial.2
    have heq := hcenter.symm.trans h
    linear_combination heq
  have hev : (fun z : ℂ => CCM.nativeCompletionKernelLaplaceMoment epsilon z 0) =ᶠ[𝓝 w]
      fun z => nativeZeroJetKernelMultiplier (z + (epsilon : ℂ)) := by
    have hposN : ∀ᶠ z in 𝓝 w, 0 < (z + (epsilon : ℂ)).re :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.add continuous_const))).mem_nhds hpos
    have hneN : ∀ᶠ z in 𝓝 w, z + (epsilon : ℂ) ≠ (1 / 2 : ℂ) :=
      (continuous_id.add continuous_const).continuousAt.eventually_ne hne
    filter_upwards [hposN, hneN] with z hzpos hzne
    rw [CCM.nativeCompletionKernelLaplaceMoment_zero_damping_shift]
    exact CCM.nativePositiveCompletion_complexLaplace hzpos hzne
  rw [analyticOrderAt_congr hev]
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + (epsilon : ℂ)) w := by fun_prop
  have hd : deriv (fun z : ℂ => z + (epsilon : ℂ)) w ≠ 0 := by
    simp only [deriv_add_const, deriv_id'']
    exact one_ne_zero
  have hord := analyticOrderAt_comp_of_deriv_ne_zero (f := nativeZeroJetKernelMultiplier) hshift hd
  change analyticOrderAt (fun z : ℂ => nativeZeroJetKernelMultiplier (z + (epsilon : ℂ))) w = _ at hord
  rw [hord, hcenter]
  exact nativeZeroJetKernelMultiplier_order rho

theorem nativeZeroJet_kernelMoments_eq_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ∀ j < zeroMult (rho : ℂ), CCM.nativeCompletionKernelLaplaceMoment
      (nativeZeroJetDamping rho) (nativeZeroJetParameter rho) j = 0 := by
  have hord := nativeActualKernelLaplace_order_of_zero (nativeZeroJetDamping rho)
    (nativeZeroJetDamping_pos rho hoff).le (nativeZeroJetRightZero rho)
    (nativeZeroJetParameter rho) (nativeZeroJetParameter_re_pos rho hoff)
    (nativeZeroJetParameter_add_damping rho)
  rw [nativeZeroJetRightZero_mult] at hord
  exact CCM.nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder
    (nativeZeroJetDamping rho) (nativeZeroJetDamping_pos rho hoff).le
    (nativeZeroJetParameter rho) (nativeZeroJetParameter_re_pos rho hoff)
    (zeroMult (rho : ℂ)) (le_of_eq hord.symm)

theorem nativeZeroJet_annihilates_range
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (f : CCM.nativeCompletionCausalL2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (CCM.nativeDampedCompletionCausalL2Operator (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le f) = 0 := by
  apply CCM.nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
  intro j hj
  have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  exact nativeZeroJet_kernelMoments_eq_zero rho hoff j (by omega)

theorem nativeZeroJetAdjointWitness_mem_adjointKernel
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    CCM.nativeDampedCompletionCausalL2Adjoint (nativeZeroJetDamping rho)
      (nativeZeroJetDamping_pos rho hoff).le (nativeZeroJetAdjointWitness rho hoff) = 0 := by
  apply CCM.nativeCausalExponentialWitness_mem_adjointKernel_of_kernel_moments
  intro j hj
  have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  exact nativeZeroJet_kernelMoments_eq_zero rho hoff j (by omega)

end Zeta23.ExceptionalZero

#print axioms Zeta23.CCM.nativeCompletionKernelLaplaceMoment_zero_damping_shift
#print axioms Zeta23.ExceptionalZero.nativeActualKernelLaplace_order_of_zero
#print axioms Zeta23.ExceptionalZero.nativeZeroJet_kernelMoments_eq_zero
#print axioms Zeta23.ExceptionalZero.nativeZeroJet_annihilates_range
#print axioms Zeta23.ExceptionalZero.nativeZeroJetAdjointWitness_mem_adjointKernel
