import Zeta23.OPICARound2.FixedFilter

/-! Physical and expected-type consumers. Full S04 isometry/factorization
acceptance remains separate from these literal filter and S16 consumers. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace Zeta23.OPICARound2.Validation

theorem fixed_filter_physical_kernel_consumer :
    (∀ t : ℝ, fixedFilterKernel t =
      if 0 ≤ t then Real.exp (-t / 2) * (t ^ 3 / 6 + t ^ 4 / 24) else 0) ∧
    Integrable fixedFilterKernel ∧ (∫ t : ℝ, ‖fixedFilterKernel t‖) = 48 ∧
    (∀ z : ℂ, 0 ≤ z.re →
      probeLaplace (fun t => (fixedFilterKernel t : ℂ)) z =
        (z + 3 / 2) / (z + 1 / 2) ^ 5) := by
  exact ⟨fun _ => rfl, fixedFilterKernel_integrable, fixedFilterKernel_integral_norm,
    fun z hz => fixedFilterKernel_laplace z hz⟩

theorem fixed_filter_zero_frequency_consumer :
    probeLaplace (fun t => (fixedFilterKernel t : ℂ)) 0 = 48 := by
  rw [fixedFilterKernel_laplace 0 (by norm_num)]
  norm_num [fixedFilterMultiplier]

/-- Every actual finite trial, with no rank or multiplicity premise. -/
theorem fixed_filter_separation_expected_type (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    0 < Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ‖((rho : ℂ) - 1 / 2 + 3 / 2) / ((rho : ℂ) - 1 / 2 + 1 / 2) ^ 5 *
        (CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
          JPlus ((rho : ℂ) - 1 / 2))‖ ∧
    (∀ (N : ℕ) (x : Fin N → ℂ), fixedFilteredZeroBound rho ≤
      ‖fixedFilterOperator (probeTarget - ∑ i : Fin N, x i • probeColumn (i.val + 1))‖) := by
  exact fixed_filtered_native_zero_separation rho hright

/-- This expected-type consumer retains the entire OPEN approximation premise. -/
theorem fixed_filter_RH_expected_type
    (h : ∃ (dims : ℕ → ℕ) (x : (k : ℕ) → Fin (dims k) → ℂ),
      Filter.Tendsto (fun k => ‖fixedFilterOperator (probeTarget -
        ∑ i : Fin (dims k), x k i • probeColumn (i.val + 1))‖)
        Filter.atTop (𝓝 0)) : RiemannHypothesis :=
  rh_of_fixed_filtered_native_approximation h

/-- A concrete rejection of onto-causal cancellation. -/
theorem causal_allpass_onto_rejected : ¬ Function.Surjective causalInnerOperator :=
  causalInnerOperator_not_surjective

theorem actual_causal_allpass_isometry (f : CausalProbeL2) :
    ‖f - causalKernelOperator causalInnerKernel causalInnerKernel_integrable
      causalInnerKernel_zero_of_neg f‖ = ‖f‖ :=
  causalInnerOperator_norm f

theorem actual_full_line_allpass_isometry (f : ProbeL2) :
    ‖f - kernelL2Operator causalInnerKernel causalInnerKernel_integrable f‖ = ‖f‖ :=
  fullCausalInnerOperator_norm f

theorem reduced_source_rectangle_expected_type (z : ℂ)
    (hd0 : (1 / 4 : ℝ) ≤ z.re) (hd1 : z.re ≤ 3 / 8)
    (ht0 : (1 : ℝ) ≤ |z.im|) (ht1 : |z.im| ≤ 2) :
    (4396431852289 / 49942416588800 : ℝ) ≤
      2 * z.re * ‖((z - 1 / 2) / (z + 1 / 2) ^ 2) *
        (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
          (CCM.universalSincSource probeSigma (t - probeSigma) : ℂ))‖ ^ 2 :=
  reduced_probe_source_rectangle_lower z hd0 hd1 ht0 ht1

/-- The required literal floor/log-factorial comparison kernel has its
actual stable native realization and full L1/L2 regularity. -/
theorem actual_comparison_kernels_expected_type :
    Integrable (fun t : ℝ =>
      if 0 ≤ t then Real.exp (-t / 2) * (1 - t) else 0) ∧
    MemLp (fun t : ℝ => ((if 0 ≤ t then Real.exp (-t / 2) * (1 - t) else 0 : ℝ) : ℂ)) 2 volume ∧
    Integrable classicalCompletionKernel ∧
    MemLp (fun t : ℝ => (classicalCompletionKernel t : ℂ)) 2 volume ∧
    (∀ t : ℝ, (if 0 ≤ t then Real.exp (-t / 2) *
      ((1 - t) * (⌊Real.exp t⌋₊ : ℝ) + Real.log (Nat.factorial ⌊Real.exp t⌋₊)) else 0) =
      CCM.nativePositiveCompletion t +
        ∫ s : ℝ, CCM.nativePositiveCompletion s * causalInnerKernel (t - s)) := by
  exact ⟨classicalProbeKernel_integrable, classicalProbeKernel_memLp,
    classicalCompletionKernel_integrable, classicalCompletionKernel_memLp,
    classicalCompletionKernel_eq_native_plus_inner_convolution⟩

theorem literal_comparison_L2_representatives :
    ((comparisonU0 : ProbeL2) =ᵐ[volume] fun t : ℝ => (classicalProbeKernel t : ℂ)) ∧
    ((comparisonH0 : ProbeL2) =ᵐ[volume] fun t : ℝ => (classicalCompletionKernel t : ℂ)) :=
  ⟨comparisonU0_coeFn, comparisonH0_coeFn⟩

theorem actual_probability_source_rectangle (z : ℂ) (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 3 / 8) (htau : |z.im| ≤ 2) :
    (2096767 / 2097152 : ℝ) ≤
      ‖∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
        (CCM.universalSincSource probeSigma (t - probeSigma) : ℂ)‖ :=
  QPlus_baseline_rectangle_lower z hz0 hz1 htau

#print axioms fixed_filter_physical_kernel_consumer
#print axioms fixed_filter_separation_expected_type
#print axioms fixed_filter_RH_expected_type
#print axioms causal_allpass_onto_rejected
#print axioms actual_causal_allpass_isometry
#print axioms actual_full_line_allpass_isometry
#print axioms reduced_source_rectangle_expected_type
#print axioms actual_comparison_kernels_expected_type
#print axioms literal_comparison_L2_representatives


theorem literal_h0_transform_and_removable_value :
    (∀ z : ℂ, 0 < z.re → z ≠ 1 / 2 →
      (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
        ((if 0 ≤ t then Real.exp (-t / 2) *
          ((1 - t) * (⌊Real.exp t⌋₊ : ℝ) + Real.log (Nat.factorial ⌊Real.exp t⌋₊)) else 0 : ℝ) : ℂ)) =
          ((z - 1 / 2) / (z + 1 / 2) ^ 2) * riemannZeta (z + 1 / 2)) ∧
    probeLaplace (fun t : ℝ => (classicalCompletionKernel t : ℂ)) (1 / 2) = 1 :=
  ⟨classicalCompletionKernel_laplace, classicalCompletionKernel_laplace_half⟩

theorem actual_native_fixed_filter_factorization :
    fixedFilterOperator probeTarget = causalInnerOperator (causalInnerOperator comparisonU) ∧
    fixedFilterOperator probeCompletedSource = causalInnerOperator (causalInnerOperator comparisonH) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0, fixedFilterOperator (probeColumn n) =
      causalInnerOperator (causalInnerOperator ((CCM.nativeIntegerCoefficient n : ℂ) •
        probeDelay (Real.log n) (probe_log_nonneg hn) comparisonH))) ∧
    (∀ N : ℕ, ∀ x : Fin N → ℂ,
      ‖fixedFilterOperator (probeTarget - ∑ i : Fin N, x i • probeColumn (i.val + 1))‖ =
        ‖comparisonU - ∑ i : Fin N, x i • ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) •
          probeDelay (Real.log ((i.val + 1 : ℕ) : ℝ))
            (probe_log_nonneg (Nat.succ_ne_zero i.val)) comparisonH)‖) :=
  ⟨fixedFilter_target_factorization, fixedFilter_completed_factorization,
    fun _ hn => fixedFilter_column_factorization hn,
    fun _ x => fixedFilteredProbeResidual_norm_eq x⟩

theorem reduced_actual_zero_lower_consumer (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) {N : ℕ} (x : Fin N → ℂ) :
    2 * ((rho : ℂ) - 1 / 2).re *
      ‖((((rho : ℂ) - 1 / 2) - 1 / 2) / (((rho : ℂ) - 1 / 2) + 1 / 2)^2) *
        QPlus ((rho : ℂ) - 1 / 2)‖ ^ 2 ≤ ‖fixedFilteredProbeResidual x‖ ^ 2 :=
  fixedFilteredProbeResidual_reduced_zero_lower rho hright x

end Zeta23.OPICARound2.Validation

#print axioms Zeta23.OPICARound2.native_probe_fixed_stable_filter
#print axioms Zeta23.OPICARound2.Validation.literal_h0_transform_and_removable_value
#print axioms Zeta23.OPICARound2.Validation.actual_native_fixed_filter_factorization
#print axioms Zeta23.OPICARound2.Validation.reduced_actual_zero_lower_consumer
