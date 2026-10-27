import Zeta23.OPICARound2.FilteredClassicalComparison

/-! Independent physical consumers of the logarithmic unitary and exact
classical tail cancellation. The native factorization and comparison norm
are required separately before accepting S05 in full. -/

noncomputable section
open Set MeasureTheory

namespace Zeta23.OPICARound2.Validation

theorem full_line_allpass_unitary_expected_type :
    (∀ f : ProbeL2, ‖fullCausalInnerEquiv f‖ = ‖f‖) ∧
      Function.Surjective fullCausalInnerEquiv ∧
      (∀ f : ProbeL2, fullCausalInnerEquiv f =
        f - kernelL2Operator causalInnerKernel causalInnerKernel_integrable f) := by
  exact ⟨fun f => fullCausalInnerEquiv.norm_map f, fullCausalInnerEquiv.surjective,
    fun _ => rfl⟩

theorem logarithmic_unitary_expected_type :
    (∀ f : PositiveProbeL2, ‖reversedLogL2Equiv f‖ = ‖f‖) ∧
      Function.Surjective reversedLogL2Equiv ∧
      (∀ f : PositiveProbeL2, reversedLogL2Equiv f =ᵐ[volume]
        fun t : ℝ => (Real.exp (-t / 2) : ℂ) * f (Real.exp (-t))) := by
  exact ⟨fun f => reversedLogL2Equiv.norm_map f, reversedLogL2Equiv.surjective,
    fun f => reversedLogL2Value_coeFn f⟩

theorem logarithmic_inverse_physical_consumer (g : ℝ → ℂ) :
    (∀ t : ℝ, reversedLogUnitary (reversedLogInverse g) t = g t) ∧
    (∫ x : ℝ in Ioi 0, ‖reversedLogInverse g x‖ ^ 2) = ∫ t : ℝ, ‖g t‖ ^ 2 := by
  exact ⟨fun t => congrFun (reversedLogUnitary_inverse g) t,
    reversedLogInverse_integral_norm_sq g⟩

theorem classical_tail_cancellation_expected_type {N : ℕ} (coeff : Fin N → ℂ)
    (h : ∑ i : Fin N, coeff i / ((i.val + 1 : ℕ) : ℂ) = 0) (x : ℝ) (hx : 1 < x) :
    classicalChi x + ∑ i : Fin N, coeff i *
      ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) = 0 :=
  classicalFiniteResidual_zero_above_one coeff h hx

#print axioms logarithmic_unitary_expected_type
#print axioms logarithmic_inverse_physical_consumer
#print axioms classical_tail_cancellation_expected_type
#print axioms full_line_allpass_unitary_expected_type


theorem literal_negative_time_cancellation (t : ℝ) (ht : t < 0) :
    OPICAFollowup.sawtoothWeight t -
      (∫ s : ℝ, ((if 0 ≤ s then Real.exp (-s / 2) else 0 : ℝ) : ℂ) *
        OPICAFollowup.sawtoothWeight (t - s)) = 0 :=
  fullCausalInnerPhysical_sawtooth_of_neg ht

theorem literal_indicator_and_fractional_dictionary :
    fullCausalInnerOperator (reversedLogL2 classicalChiL2) = (comparisonU0 : ProbeL2) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0,
      fullCausalInnerOperator (reversedLogL2 (classicalRhoL2 n hn)) =
        -(CCM.nativeIntegerCoefficient n : ℂ) •
          CCM.nativeCompletionL2Delay (Real.log n) (comparisonH0 : ProbeL2)) :=
  ⟨inner_reversedLog_classicalChi, fun _ hn => inner_reversedLog_classicalRho hn⟩

theorem actual_native_classical_upper_expected_type {N : ℕ} (x : Fin N → ℂ) :
    ‖fixedFilterOperator (probeTarget - ∑ i : Fin N, x i • probeColumn (i.val + 1))‖ ^ 2 ≤
      ∫ u : ℝ in Ioi 0, ‖(if u ∈ Ioo 0 1 then (1 : ℂ) else 0) +
        ∑ i : Fin N, x i * ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * u)) : ℝ) : ℂ)‖ ^ 2 :=
  filtered_probe_classical_comparison x

end Zeta23.OPICARound2.Validation

#print axioms Zeta23.OPICARound2.filtered_probe_classical_comparison
#print axioms Zeta23.OPICARound2.Validation.literal_negative_time_cancellation
#print axioms Zeta23.OPICARound2.Validation.literal_indicator_and_fractional_dictionary
#print axioms Zeta23.OPICARound2.Validation.actual_native_classical_upper_expected_type
