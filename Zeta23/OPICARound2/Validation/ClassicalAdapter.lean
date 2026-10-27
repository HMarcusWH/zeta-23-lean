import Zeta23.OPICARound2.ClassicalAdapter

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Zeta23.OPICARound2.Validation

theorem actual_logarithmic_unitary_expected_type :
    Function.Surjective reversedLogL2 ∧
      (∀ f : PositiveProbeL2, ‖reversedLogL2 f‖ = ‖f‖) ∧
      (∀ f : PositiveProbeL2, (reversedLogL2 f : ℝ → ℂ) =ᵐ[volume]
        fun t : ℝ => (Real.exp (-t / 2) : ℂ) * f (Real.exp (-t))) :=
  ⟨reversedLogL2_surjective, reversedLogL2.norm_map,
    fun f => reversedLogL2Value_coeFn f⟩

theorem literal_causal_L1_boundary_consumer (f : ℝ → ℂ) (hf : Integrable f)
    (hc : ∀ᵐ t : ℝ, t < 0 → f t = 0) (tau : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ t : ℝ, Complex.exp
        (-((1 / ((n : ℝ) + 3) : ℝ) + Complex.I * (tau : ℂ)) * (t : ℂ)) * f t)
      Filter.atTop (𝓝 (∫ t : ℝ, Complex.exp (-(Complex.I * (tau : ℂ)) * (t : ℂ)) * f t)) := by
  exact probeLaplace_boundary_tendsto f hf hc tau

theorem literal_native_A_boundary_consumer (tau : ℝ) :
    (∫ t : ℝ, Complex.exp (-(Complex.I * (tau : ℂ)) * (t : ℂ)) *
      (CCM.nativePositiveCompletion t : ℂ)) =
        ((Complex.I * (tau : ℂ) - 1 / 2) /
          ((Complex.I * (tau : ℂ) + 1 / 2) * (Complex.I * (tau : ℂ) + 3 / 2))) *
          riemannZeta (Complex.I * (tau : ℂ) + 1 / 2) :=
  nativeCompletionLaplace_boundary tau

theorem actual_causal_L2_Laplace_uniqueness_consumer (f : CausalProbeL2)
    (h : ∀ z : ℂ, 0 < z.re →
      (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (f : ProbeL2) t) = 0) : f = 0 := by
  apply probeCausalLaplace_injective f
  intro z hz
  simpa only [CCM.nativeCausalLaplaceMoment, pow_zero, one_mul] using h z hz

theorem actual_L1_L2_Fourier_uniqueness_consumer (f : ℝ → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (h : ∀ tau : ℝ, (∫ t : ℝ,
      Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t) = 0) :
      f =ᵐ[volume] 0 := probeL1L2Fourier_zero_ae f hf1 hf2 h


theorem literal_native_compact_kernel_expected_type :
    nativeMuntzKernel 0 = 0 ∧
    (∀ x : ℝ, 0 < x → nativeMuntzKernel x =
      ((Real.sqrt x)⁻¹ : ℂ) * probeV (-Real.log x)) ∧
    HasCompactSupport nativeMuntzKernel ∧
    (∀ x : ℝ, x ∉ Icc (0 : ℝ) 1 → nativeMuntzKernel x = 0) ∧
    Integrable nativeMuntzKernel ∧ (∫ x : ℝ, nativeMuntzKernel x) = 0 :=
  ⟨nativeMuntzKernel_zero, fun _ hx => nativeMuntzKernel_of_pos hx,
    nativeMuntzKernel_hasCompactSupport, fun _ hx => nativeMuntzKernel_zero_outside hx,
    nativeMuntzKernel_integrable, nativeMuntzKernel_integral_zero⟩

theorem halfline_C1_and_endpoint_consumers :
    ContDiffOn ℝ 1 nativeMuntzKernel (Ici (0 : ℝ)) ∧
    nativeMuntzKernel 1 = 0 ∧ HasDerivAt nativeMuntzKernel 0 1 ∧
    HasDerivWithinAt nativeMuntzKernel (2 * JPlus (-3 / 2 : ℂ)) (Ici (0 : ℝ)) 0 ∧
    (2 * JPlus (-3 / 2 : ℂ)) ≠ 0 ∧ ¬DifferentiableAt ℝ nativeMuntzKernel 0 :=
  ⟨nativeMuntzKernel_contDiffOn_halfline, nativeMuntzKernel_one,
    nativeMuntzKernel_flat_at_one, nativeMuntzKernel_right_derivative,
    nativeMuntzKernel_right_slope_ne_zero, nativeMuntzKernel_not_differentiable_zero⟩

theorem literal_Mellin_integral_consumer (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => Complex.exp ((s - 1) * (Real.log x : ℂ)) * nativeMuntzKernel x)
      (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, Complex.exp ((s - 1) * (Real.log x : ℂ)) * nativeMuntzKernel x) =
      ((s - 1) / (s * (s + 1))) *
        (∫ t : ℝ, Complex.exp (-(s - 1 / 2) * (t : ℂ)) * (jPlus t : ℂ)) :=
  ⟨nativeMuntzMellin_integrable hs, nativeMuntzMellin_formula hs⟩

theorem mean_subtraction_retained_before_simplification (x : ℝ) (hx : 0 < x) :
    nativeMuntzPf x =
      (∑ n ∈ Finset.range (⌊x⁻¹⌋₊ + 1), nativeMuntzKernel ((n : ℝ) * x)) -
        (x : ℂ)⁻¹ * (∫ y : ℝ, nativeMuntzKernel y) := by
  rw [nativeMuntzPf, if_pos hx]

theorem actual_native_Muntz_dictionary_consumers :
    reversedLogL2 nativeMuntzKernelL2 = (probeTarget : ProbeL2) ∧
    reversedLogL2 nativeMuntzPfL2 = (probeCompletedSource : ProbeL2) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0,
      reversedLogL2 (nativeMuntzPfDilationL2 n hn) = (probeColumn n : ProbeL2)) ∧
    (∀ t : ℝ, (Real.exp (-t / 2) : ℂ) * nativeMuntzPf (Real.exp (-t)) = probeW t) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0, ∀ t : ℝ,
      (Real.exp (-t / 2) : ℂ) * nativeMuntzPf ((n : ℝ) * Real.exp (-t)) =
        (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) :=
  ⟨nativeMuntzKernel_L2_logarithmic_identity, nativeMuntzPf_L2_logarithmic_identity,
    fun _ hn => nativeMuntzPf_dilation_L2_identity hn,
    nativeMuntzPf_logarithmic_identity, fun _ hn => nativeMuntzPf_dilation_logarithmic_identity hn⟩

end Zeta23.OPICARound2.Validation
#print axioms Zeta23.OPICARound2.Validation.actual_logarithmic_unitary_expected_type
#print axioms Zeta23.OPICARound2.Validation.literal_causal_L1_boundary_consumer
#print axioms Zeta23.OPICARound2.Validation.literal_native_A_boundary_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_causal_L2_Laplace_uniqueness_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_L1_L2_Fourier_uniqueness_consumer

#print axioms Zeta23.OPICARound2.native_compact_muntz_adapter

#print axioms Zeta23.OPICARound2.Validation.literal_native_compact_kernel_expected_type

#print axioms Zeta23.OPICARound2.Validation.halfline_C1_and_endpoint_consumers

#print axioms Zeta23.OPICARound2.Validation.literal_Mellin_integral_consumer

#print axioms Zeta23.OPICARound2.Validation.mean_subtraction_retained_before_simplification

#print axioms Zeta23.OPICARound2.Validation.actual_native_Muntz_dictionary_consumers
