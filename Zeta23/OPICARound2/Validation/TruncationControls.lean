import Zeta23.OPICARound2.TruncationControls

/-! Restated literal source, finite-prefix, delayed-residual and analytic
source-count consumers. An omitted hypothesis is never replaced by a sampled
identity or an assumed visible critical zero. -/

noncomputable section

open Set MeasureTheory Finset Filter Matrix
open scoped Topology BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2.Validation

theorem truncation_consumer_001 {T t : ℝ} (ht : t ≤ T) :
    mobiusProbeSource t = ∑ n ∈ range (⌊Real.exp T⌋₊ + 1),
      (ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) * jPlus (t - Real.log n) :=
  mobiusProbeSource_history ht

theorem truncation_consumer_002 (t : ℝ) :
    CCM.nativeIntegerTranslateAction mobiusProbeSource t = jPlus t :=
  mobiusProbeSource_integer_inverse t

theorem truncation_consumer_003 (t : ℝ) :
    Integrable (fun s : ℝ => CCM.nativePositiveCompletion s * mobiusProbeSource (t - s)) :=
  mobiusProbeSource_convolution_integrable t

theorem truncation_consumer_004 (t : ℝ) :
    ((∫ s : ℝ, CCM.nativePositiveCompletion s * mobiusProbeSource (t - s) : ℝ) : ℂ) = probeV t :=
  mobiusProbeSource_floor_inverse t

theorem truncation_consumer_005 (a : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    (hf : ∀ s : ℝ, s < 0 → f s = 0) (N : ℕ) {t : ℝ}
    (ht : t < Real.log (N + 1 : ℕ)) :
    OPICAFollowup.arithmeticHistoryAction a f t =
      ∑ n ∈ range (N + 1), a n / Real.sqrt (n : ℝ) * f (t - Real.log n) :=
  arithmetic_history_before_next a hf N ht

theorem truncation_consumer_006 (N : ℕ) :
    (mobiusProbePartialOutput N : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      ∑ n ∈ range (N + 1),
        ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) : ℂ) *
          probeW (t - Real.log n) :=
  mobiusProbePartialOutput_coeFn N

theorem truncation_consumer_007 (N : ℕ) :
    ∀ᵐ t : ℝ, t < Real.log (N + 1 : ℕ) →
      (mobiusProbePartialResidual N : ProbeL2) t = 0 :=
  mobiusProbePartialResidual_delayed N

theorem truncation_consumer_008 (z : ℂ) (hz : 0 < z.re)
    (r : CausalProbeL2) (h : ℝ)
    (hr : ∀ᵐ t : ℝ, t < h → (r : ProbeL2) t = 0) :
    Real.sqrt (2 * z.re) * Real.exp (z.re * h) *
      ‖CCM.nativeCausalLaplaceMoment z 0 (r : ProbeL2)‖ ≤ ‖r‖ :=
  probe_delayed_laplace_bound z hz r h hr

theorem truncation_consumer_009 (N : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      Real.exp (((rho : ℂ) - 1 / 2).re * Real.log (N + 1 : ℕ)) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖mobiusProbePartialResidual N‖ :=
  (native_mobius_delayed_barrier N rho hright).2

theorem truncation_consumer_010 (z : ℂ) : AnalyticAt ℂ JPlus z := JPlus_analyticAt z

theorem truncation_consumer_011 (z : ℂ) :
    ‖JPlus z‖ ≤ probeSourceL1Mass * Real.exp (2 * probeSigma * ‖z‖) :=
  JPlus_exponential_bound z

theorem truncation_consumer_012 {R : ℝ} (hR : 0 < R) :
    (probeSourceZeroCount R : ℝ) ≤
      (Real.log (16 * max 1 probeSourceL1Mass) + 4 * probeSigma * R) / Real.log 2 :=
  probe_source_zero_count_bound hR

theorem truncation_consumer_013 (T : ℝ) :
    (∫ t : ℝ, ‖probeFloorKernelTail T t‖) ≤ 2 * Real.exp (-T / 2) :=
  probeFloorKernelTail_mass_bound T

theorem truncation_consumer_014 (T : ℝ) (f : ProbeL2) :
    ‖CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f -
        kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f‖ ≤
      2 * Real.exp (-T / 2) * ‖f‖ :=
  native_floor_physical_cutoff_bound T f

theorem truncation_consumer_015 (T : ℝ) :
    ‖(probeCompletedSource : ProbeL2) -
        kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
          (probeSource : ProbeL2)‖ ≤
      2 * Real.exp (-T / 2) * ‖probeSource‖ :=
  native_probe_source_physical_cutoff_bound T

theorem truncation_consumer_016 (lambda : ℂ) (hlambda : lambda.re = 0)
    (f : CausalProbeL2) :
    Tendsto (fun e : ℝ => (e : ℂ) *
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (f : ProbeL2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  probe_boundary_laplace_first_order_limit lambda hlambda f

theorem truncation_consumer_017 (lambda : ℂ) (hlambda : lambda.re = 0)
    (f : CausalProbeL2) (F : ℂ → ℂ) (hF : MeromorphicAt F lambda)
    (hmatch : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), F (lambda + (e : ℂ)) =
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (f : ProbeL2)) :
    0 ≤ meromorphicOrderAt F lambda :=
  probe_boundary_meromorphic_order_nonneg lambda hlambda f F hF hmatch

theorem truncation_consumer_018 (f : CausalProbeL2)
    (hf : probeOperator f = probeTarget) (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2) :
    (zetaZeroConfig.mult (rho : ℂ) : ℤ) ≤
      (meromorphicOrderAt JPlus ((rho : ℂ) - 1 / 2)).untop₀ :=
  native_probe_range_boundary_order f hf rho hcritical

theorem truncation_consumer_019 (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    Tendsto (fun N : ℕ => ‖mobiusProbePartialResidual N‖) atTop atTop :=
  native_mobius_residual_norm_tendsto_atTop rho hright

theorem truncation_consumer_020 {T : ℝ} (hT : 0 < T) (hRH : RiemannHypothesis)
    (hDom : ∀ rho ∈ zetaZeroConfig.window T (2 * T),
      (zetaZeroConfig.mult rho : ℤ) ≤ (meromorphicOrderAt JPlus (rho - 1 / 2)).untop₀) :
    (zetaZeroConfig.N T (2 * T) : ℤ) ≤ probeSourceZeroCount (3 * T) :=
  probe_zeta_count_le_source_count_of_order_domination hT hRH hDom

theorem truncation_consumer_021 (hRH : RiemannHypothesis) :
    ∃ rho : zetaZeroConfig.carrier, (rho : ℂ).re = 1 / 2 ∧
      (meromorphicOrderAt JPlus ((rho : ℂ) - 1 / 2)).untop₀ <
        (zetaZeroConfig.mult (rho : ℂ) : ℤ) :=
  native_probe_visible_critical_zero_of_RH hRH

theorem truncation_consumer_022 : probeTarget ∉ Set.range probeOperator :=
  native_probe_target_not_mem_range

theorem truncation_consumer_023 (z : ℂ) (hz : 0 < z.re) (hne : z ≠ 1 / 2)
    (f : CausalProbeL2) :
    Real.sqrt (2 * z.re) * ‖CCM.nativeCompletionRationalMultiplier z * JPlus z‖ ≤
      ‖probeTarget - probeOperator f‖ +
        ‖CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)‖ * ‖f‖ :=
  probe_residual_evaluation_bound z hz hne f

theorem truncation_consumer_024 (B : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ f : CausalProbeL2, ‖f‖ ≤ B →
      eta ≤ ‖probeTarget - probeOperator f‖ :=
  native_probe_bounded_input_gap B

theorem truncation_consumer_025 (u : ℕ → CausalProbeL2)
    (herr : Tendsto (fun N : ℕ => ‖probeTarget - probeOperator (u N)‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖u N‖) atTop atTop :=
  native_probe_successful_input_norms_tendsto_atTop u herr

theorem truncation_consumer_026 (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2) (k : ℕ)
    (hk : analyticOrderAt JPlus ((rho : ℂ) - 1 / 2) = (k : ℕ∞))
    (hkm : k < zeroMult (rho : ℂ)) :
    ∃ cstar M0 : ℝ, 0 < cstar ∧ 0 < M0 ∧ ∀ f : CausalProbeL2, M0 ≤ ‖f‖ →
      cstar * ‖f‖ ^ (-((2 * (k : ℝ) + 1) /
        (2 * (zeroMult (rho : ℂ) : ℝ) - 2 * (k : ℝ) - 1))) ≤
        ‖probeTarget - probeOperator f‖ :=
  native_probe_boundary_power_cost rho hcritical k hk hkm

theorem truncation_consumer_027 (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2)
    (hvisible : JPlus ((rho : ℂ) - 1 / 2) ≠ 0) :
    ∃ cstar eta0 : ℝ, 0 < cstar ∧ 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∀ f : CausalProbeL2,
        ‖probeTarget - probeOperator f‖ ≤ eta →
        (cstar / eta) ^ (2 * (zeroMult (rho : ℂ) : ℝ) - 1) ≤ ‖f‖ :=
  native_probe_visible_boundary_input_cost rho hcritical hvisible

theorem truncation_consumer_028 {t : ℝ} (ht : t < Real.log 2) :
    mobiusProbeSource t = jPlus t := mobiusProbeSource_first_cell ht

theorem truncation_consumer_029 (T t : ℝ) :
    probeFloorKernelCutoff T t = (Icc (0 : ℝ) T).indicator CCM.nativePositiveCompletion t :=
  probeFloorKernelCutoff_eq_Icc T t

/-- Actual dictionary columns instantiate the finite Gram-entry error. -/
theorem truncation_consumer_030 (T : ℝ) (m n : ℕ) :
    ‖inner ℂ (probeColumn m : ProbeL2) (probeColumn n : ProbeL2) -
      inner ℂ (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
          (probeInput m : ProbeL2))
        (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
          (probeInput n : ProbeL2))‖ ≤
      (2 * Real.exp (-T / 2) * ‖probeInput m‖) * ‖probeColumn n‖ +
        ‖kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
          (probeInput m : ProbeL2)‖ * (2 * Real.exp (-T / 2) * ‖probeInput n‖) :=
  native_floor_cutoff_gram_bound T (probeInput m : ProbeL2) (probeInput n : ProbeL2)

theorem truncation_consumer_031 :
    probeIntegerTailConstant = ‖2 * CCM.nativeOriginalSourceLaplace (-3 / 2 : ℂ)‖ ^ 2 / 12 ∧
      0 < probeIntegerTailConstant :=
  ⟨probeIntegerTailConstant_eq_original,probeIntegerTailConstant_pos⟩

theorem truncation_consumer_032 {K : ℕ} (hK : 1 ≤ K) {t : ℝ}
    (ht : Real.log K + 2 * probeSigma ≤ t) :
    probeIntegerTargetPrefix K t = probeNativeTailAmplitude *
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * ((K : ℂ) * ((K : ℂ) + 1) / 2) :=
  probeIntegerTargetPrefix_tail hK ht

theorem truncation_consumer_033 (K : ℕ) :
    (probeIntegerTargetPrefixL2 K : ProbeL2) =ᵐ[volume] probeIntegerTargetPrefix K :=
  probeIntegerTargetPrefixL2_coeFn K

theorem truncation_consumer_034 {K : ℕ} (hK : 1 ≤ K) :
    (∫ t : ℝ in Ioi (Real.log K + 2 * probeSigma), ‖probeIntegerTargetPrefix K t‖ ^ 2) =
      probeIntegerTailConstant * Real.exp (-3 * probeSigma) * ((K : ℝ) + 1) ^ 2 / (K : ℝ) :=
  probeIntegerTargetPrefix_tail_square_paper hK

theorem truncation_consumer_035 :
    Tendsto (fun K : ℕ => ‖probeIntegerTargetPrefixL2 K‖) atTop atTop :=
  probeIntegerTargetPrefixL2_norm_tendsto_atTop

theorem truncation_consumer_036 (t : ℝ) :
    Tendsto (fun K : ℕ => probeIntegerTargetPrefix K t) atTop (𝓝 (probeW t)) :=
  probeIntegerTargetPrefix_tendsto_pointwise t

theorem truncation_consumer_037 (K : ℕ) {t : ℝ} (ht : t < 0) :
    probeIntegerTargetPrefix K t = 0 := probeIntegerTargetPrefix_causal K ht

/-- Removing every Möbius column leaves the actual nonzero target residual. -/
theorem truncation_zero_prefix_control :
    mobiusProbePartialInput 0 = 0 ∧ mobiusProbePartialResidual 0 = probeTarget ∧
      0 < ‖mobiusProbePartialResidual 0‖ := by
  have hi : mobiusProbePartialInput 0 = 0 := by simp [mobiusProbePartialInput]
  have hr : mobiusProbePartialResidual 0 = probeTarget := by
    simp [mobiusProbePartialResidual,mobiusProbePartialOutput,hi]
  exact ⟨hi,hr,by rw [hr]; exact norm_pos_iff.mpr probeTarget_ne_zero⟩

/-- Index zero is never a spurious extra dictionary column. -/
theorem truncation_zero_column_control : probeInput 0 = 0 ∧ probeColumn 0 = 0 :=
  ⟨probeInput_zero,probeColumn_zero⟩

/-- The original source mass is positive and its transform is nonzero at zero;
the Jensen count cannot be vacuous through an identically zero source. -/
theorem truncation_nonzero_source_control :
    0 < probeSourceL1Mass ∧ JPlus 0 ≠ 0 := by
  exact ⟨probeSourceL1Mass_pos,by rw [JPlus_zero]; norm_num⟩

/-- The exact-range theorem excludes every individual causal input while
retaining the OPEN range-closure criterion as a separate proposition. -/
theorem truncation_exact_inversion_control (f : CausalProbeL2) :
    probeOperator f ≠ probeTarget := by
  intro h
  exact native_probe_target_not_mem_range ⟨f,h⟩

/-- The literal n=1 term is active before log 2; deleting it cannot preserve
the local inverse on the unchanged source. -/
theorem truncation_first_column_control :
    ∃ t : ℝ, t < Real.log 2 ∧ mobiusProbeSource t ≠ 0 :=
  mobiusProbeSource_nonzero_first_cell

/-- The actual source has zeros on the critical boundary. Hence criticality
alone cannot be substituted for the explicit visibility input in S07c.
This control asserts no zeta zero at this boundary point. -/
theorem truncation_boundary_source_zero_control :
    (-Complex.I * CCM.UniversalSinc.fixedCoincidentArgument).re = 0 ∧
      JPlus (-Complex.I * CCM.UniversalSinc.fixedCoincidentArgument) = 0 := by
  have hi : Complex.I * (-Complex.I * CCM.UniversalSinc.fixedCoincidentArgument) =
      CCM.UniversalSinc.fixedCoincidentArgument := by
    rw [← mul_assoc]
    norm_num
  have hp : CCM.UniversalSinc.product probeSigma
      (Complex.I * (-Complex.I * CCM.UniversalSinc.fixedCoincidentArgument)) = 0 := by
    rw [hi]
    unfold CCM.UniversalSinc.product
    exact tprod_of_exists_eq_zero ⟨0,CCM.UniversalSinc.fixed_coincident_factor_zeros.2.1⟩
  refine ⟨?_,?_⟩
  · simp [CCM.UniversalSinc.fixedCoincidentArgument,Complex.mul_re]
  · rw [JPlus_one_copy_formula,hp,mul_zero,mul_zero]

/-- The zero-index convention creates no extra integer-prefix source. -/
theorem truncation_integer_zero_prefix_control :
    probeIntegerTargetPrefix 0 = 0 ∧ probeIntegerTargetPrefixL2 0 = 0 := by
  have hz : probeIntegerTargetPrefix 0 = 0 := by
    funext t
    simp [probeIntegerTargetPrefix,CCM.nativeIntegerCoefficient]
  refine ⟨hz,?_⟩
  apply Lp.ext
  filter_upwards [probeIntegerTargetPrefixL2_coeFn 0,Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht hzero
  rw [ht,hz]
  exact hzero.symm

/-- The actual source is an explicit counterexample to upgrading pointwise
integer-history convergence into global L2 convergence. -/
theorem truncation_integer_no_L2_limit_control :
    (∀ t : ℝ, Tendsto (fun K : ℕ => probeIntegerTargetPrefix K t) atTop (𝓝 (probeW t))) ∧
      MemLp probeW 2 volume ∧
      ¬ Tendsto probeIntegerTargetPrefixL2 atTop (𝓝 (probeCompletedSource : ProbeL2)) := by
  refine ⟨probeIntegerTargetPrefix_tendsto_pointwise,probeW_memLp,?_⟩
  intro h
  exact not_tendsto_atTop_of_tendsto_nhds h.norm probeIntegerTargetPrefixL2_norm_tendsto_atTop

theorem consumer_038 :
    CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 0 (probeTarget : ProbeL2) = 0 ∧
      CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 1 (probeTarget : ProbeL2) = 0 :=
  probeTarget_half_moments

theorem consumer_039 : probePulseCenter ∈ Set.Icc 0 probePulseLength ∧
    ‖probePulseL2‖ ^ 2 ≤ probePulseLength ^ 3 / 3 :=
  ⟨probePulseCenter_mem,probePulseL2_norm_sq_upper⟩

theorem consumer_040 (x : ℕ →₀ ℂ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ k ≤ 2047) :
    12 * Real.exp (-1 / 512) * 2048 ^ 3 ≤ probePulseSeparation ∧
      probePulseSeparation * (∑ k ∈ K, ‖probeDivisorDefect x k‖ ^ 2 / (k : ℝ)) ≤
        ‖probeSparseResidual x‖ ^ 2 :=
  ⟨probePulseSeparation_paper_lower,native_isolated_pulse_lower_bound x K hK⟩

theorem consumer_041 (x : ℕ →₀ ℂ) {k : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hsq : Squarefree k) (hx : x k = 0) :
    probePulseSeparation / (∑ d ∈ k.divisors, (d : ℝ)) ≤ ‖probeSparseResidual x‖ ^ 2 :=
  native_squarefree_omission_bound x hk hmax hsq hx

theorem consumer_042 (x : ℕ →₀ ℂ) (hx : x 2047 = 0) :
    6900 < ‖(probeTarget : ProbeL2) -
      ∑ n ∈ x.support, x n • (probeColumn n : ProbeL2)‖ :=
  native_2047_omission_residual_lower x hx

theorem consumer_043 (x : ℕ → ℂ) {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℂ) * probeDivisorDefect x d) =
      (ArithmeticFunction.moebius k : ℂ) - x k :=
  probeDivisorDefect_inversion x hk

theorem consumer_044 {k n : ℕ} (hk : 0 < k) (hmax : k ≤ 2047) (hn : 0 < n) :
    inner ℂ (probePulseShift (Real.log k)) (probeColumn n : ProbeL2) =
      if n ∣ k then (CCM.nativeIntegerCoefficient k : ℂ) *
        inner ℂ probePulseL2 (probeTarget : ProbeL2) else 0 :=
  probePulseShift_column hk hmax hn

theorem consumer_045 : inner ℂ probePulseL2 (probeTarget : ProbeL2) =
    -probeNativeTailAmplitude * (Real.exp (-2 * probePulseLength) *
      ((probePulseLength - probePulseCenter) / 2 + 1 / 4) : ℝ) :=
  probePulse_pairing

theorem control_009 : probePulseL2 ≠ 0 := probePulseL2_ne_zero

theorem control_010 : Squarefree (2047 : ℕ) ∧
    (∑ d ∈ Nat.divisors 2047, (d : ℝ)) = 2160 :=
  ⟨probe_2047_squarefree,probe_2047_divisor_sum⟩

theorem consumer_046 (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ¬ (probeW =ᵐ[volume.restrict (Ioo (0 : ℝ) epsilon)] fun _ => (0 : ℂ)) ∧
      ∃ u ∈ Ioo (0 : ℝ) epsilon, probeW u ≠ 0 :=
  ⟨endpoint_probeW_essential_left epsilon hepsilon,native_probeW_left_endpoint epsilon hepsilon⟩

theorem consumer_047 (M : ℕ) (i j : Fin M) : nativePrefixGram M i j =
    ∫ t : ℝ in Ico 0 (Real.log (M + 1 : ℕ)),
      conj ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) * probeW (t - Real.log (i.val + 1 : ℕ))) *
        ((CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) * probeW (t - Real.log (j.val + 1 : ℕ))) := by
  simpa only [nativePrefixGram,zero_add] using sourcePrefixGram_apply_integral probeW_memLp 0 M i j

theorem consumer_048 {M : ℕ} (hM : 0 < M) :
    (nativePrefixGram M).PosDef ∧ 0 < nativePrefixLeastEigenvalue M :=
  ⟨native_prefix_gram_posDef M,native_prefix_eigenvalue_pos hM⟩

theorem consumer_049 (x : ℕ →₀ ℂ) {M : ℕ} (hM : 0 < M) :
    (star (fun i : Fin M => (nativePrefixDifference x M) i) ⬝ᵥ
      nativePrefixGram M *ᵥ (fun i : Fin M => (nativePrefixDifference x M) i)).re ≤
        ‖probeSparseResidual x‖ ^ 2 ∧
    nativePrefixLeastEigenvalue M *
      (∑ i : Fin M, ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ^ 2) ≤
        ‖probeSparseResidual x‖ ^ 2 :=
  ⟨native_prefix_gram_residual_bound x M,native_prefix_coefficient_bound x hM⟩

theorem consumer_050 (x : ℕ →₀ ℂ) {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ≤
      ‖probeSparseResidual x‖ / Real.sqrt (nativePrefixLeastEigenvalue M) :=
  native_prefix_coordinate_error x hM i

theorem consumer_051 {M : ℕ} (hM : 0 < M) (x : ℕ → (ℕ →₀ ℂ))
    (hr : Tendsto (fun n => ‖probeSparseResidual (x n)‖) atTop (𝓝 0)) (i : Fin M) :
    Tendsto (fun n => x n (i.val + 1)) atTop
      (𝓝 (ArithmeticFunction.moebius (i.val + 1) : ℂ)) :=
  native_prefix_coordinate_convergence hM x hr i

theorem consumer_052 {w : ℝ → ℂ} (hw : MemLp w 2 volume) (hc : Continuous w)
    {alpha : ℝ} (ha : 0 ≤ alpha) (hb : ∀ t : ℝ, t < alpha → w t = 0)
    (he : ∀ epsilon : ℝ, 0 < epsilon → ∃ u ∈ Ioo alpha (alpha + epsilon), w u ≠ 0)
    {M : ℕ} (hM : 0 < M) :
    (sourcePrefixGram hw alpha M).PosDef ∧ 0 < sourcePrefixLeastEigenvalue hw alpha M ∧
      ∀ x : EuclideanSpace ℂ (Fin M),
        sourcePrefixLeastEigenvalue hw alpha M * ‖x‖ ^ 2 ≤ sourcePrefixEnergy hw alpha M x :=
  ⟨sourcePrefixGram_posDef hw hc ha hb he M,sourcePrefixLeastEigenvalue_pos hw hc ha hb he hM,
    sourcePrefixLeastEigenvalue_lower hw alpha hM⟩

theorem consumer_053 (sigma epsilon : ℝ) (hs : 0 < sigma) (he : 0 < epsilon) :
    0 < CCM.UniversalSinc.originalSourceLaw sigma (Ioo (-sigma) (-sigma + epsilon)) :=
  original_source_law_left_mass sigma epsilon hs he

theorem consumer_054 : fixedFilterOperator probeTarget = qPlusOperator endpointU2 ∧
    ∀ t : ℝ, 0 ≤ t → endpointU2Real t =
      Real.exp (-t / 2) * (1 - 3 * t + 3 * t ^ 2 / 2 - t ^ 3 / 6) :=
  ⟨endpoint_filtered_target_identity,endpointU2Real_formula⟩

/-- The first unisolated gap is already smaller than the stated pulse length. -/
theorem control_011 : Real.log (2049 : ℝ) - Real.log (2048 : ℝ) < probePulseLength := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2049 / 2048)
    (by norm_num : (2049 : ℝ) / 2048 ≠ 1)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  norm_num [probePulseLength_eq] at h ⊢
  exact h

def delayedProbeSource (t : ℝ) : ℂ := probeW (t - 1)

theorem delayedProbeSource_memLp : MemLp delayedProbeSource 2 volume :=
  probeW_memLp.comp_measurePreserving (measurePreserving_sub_right volume 1)

/-- Causal support containment alone cannot justify using the endpoint zero. -/
theorem control_012 : sourcePrefixColumn delayedProbeSource_memLp 0 1 1 = 0 := by
  apply Lp.ext
  filter_upwards [sourcePrefixColumn_coeFn delayedProbeSource_memLp 0 1 1,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t hp hz
  rw [hp,hz]
  by_cases ht : t ∈ Ioo (0 : ℝ) (0 + Real.log (1 + 1 : ℕ))
  · rw [sourcePrefixProfile,indicator_of_mem ht]
    have hlog : Real.log (2 : ℝ) < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      norm_num at h
      exact h
    norm_num only [CCM.nativeIntegerCoefficient,Nat.cast_one,Real.sqrt_one,div_one,
      Complex.ofReal_one,one_mul,Real.log_one,sub_zero]
    exact probeW_zero_of_neg (by
      change t - 1 < 0
      norm_num only [Nat.reduceAdd,Nat.cast_ofNat,zero_add] at ht
      linarith [ht.2])
  · rw [sourcePrefixProfile,indicator_of_notMem ht]
    rfl

theorem control_013 : ¬ (sourcePrefixGram delayedProbeSource_memLp 0 1).PosDef := by
  intro h
  have hi := Matrix.linearIndependent_of_posDef_gram h
  have hn := hi.ne_zero (0 : Fin 1)
  exact hn (by simpa using control_012)

theorem consumer_055 (f : ProbeL2) :
    f = (probePositivePart f : ProbeL2) + probeNegativePart f :=
  probe_signed_time_decomposition f

theorem consumer_056 (f : ProbeL2) :
    (∫ u : ℝ, ‖probeNegativeExponential u‖ ^ 2) = 1 ∧
      (∫ u : ℝ, ‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖) ≤ ‖probeNegativePart f‖ :=
  ⟨probeNegativeExponential_integral_norm_sq,probeNegativeWeightedMass_bound f⟩

theorem consumer_057 (f : ProbeL2) (t : ℝ) :
    ‖CCM.nativeDampedCompletionPointwise 0 (probeNegativePart f) t‖ ≤
      Real.exp (-t / 2) * ‖probeNegativePart f‖ :=
  native_negative_output_envelope f t

theorem consumer_058 (z : ℂ) (hz : 0 < z.re) (f : ProbeL2) :
    ‖probeFullEvaluation z hz (CCM.nativeDampedCompletionL2Operator 0 (le_rfl)
      (probeNegativePart f))‖ ≤ ‖probeNegativePart f‖ / (z.re + 1 / 2) :=
  native_negative_output_evaluation_bound z hz f

theorem consumer_059 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re) (f : ProbeL2) :
    (((rho : ℂ) - 1 / 2).re + 1 / 2) *
      max (‖probeLaplace probeV ((rho : ℂ) - 1 / 2)‖ -
        ‖(probeTarget : ProbeL2) - CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f‖ /
          Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re)) 0 ≤ ‖probeNegativePart f‖ :=
  noncausal_probe_leakage rho hright f

theorem consumer_060 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re)
    (f : CausalProbeL2) :
    probeFullEvaluation ((rho : ℂ) - 1 / 2)
      (by simp only [Complex.sub_re,Complex.ofReal_re]; norm_num; linarith)
      (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) (f : ProbeL2)) = 0 :=
  native_full_operator_causal_evaluation_zero rho hright f

theorem control_014 (f : CausalProbeL2) : probeNegativePart (f : ProbeL2) = 0 := by
  apply Lp.ext
  filter_upwards [probeNegativePart_coeFn (f : ProbeL2),f.property,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t hn hf hz
  rw [hn,hz]
  by_cases ht : t < 0
  · rw [indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht),hf ht]
    rfl
  · rw [indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht)]
    rfl

theorem control_015 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re) :
    probeLaplace probeV ((rho : ℂ) - 1 / 2) ≠ 0 := by
  have h := probeTarget_laplace_ne_zero rho hright
  rw [probeTarget_laplace_eq_physical] at h
  exact h

/-- Conditional only: no full-line inverse is asserted to exist. -/
theorem control_016 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re) (f : ProbeL2)
    (hinv : CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f = (probeTarget : ProbeL2)) :
    0 < ‖probeNegativePart f‖ := by
  have h := noncausal_probe_leakage rho hright f
  rw [hinv,sub_self,norm_zero,zero_div,sub_zero,max_eq_left (norm_nonneg _)] at h
  have ha : 0 < ((rho : ℂ) - 1 / 2).re + 1 / 2 := by
    simp only [Complex.sub_re,Complex.ofReal_re]
    norm_num
    linarith
  exact lt_of_lt_of_le (mul_pos ha (norm_pos_iff.mpr (control_015 rho hright))) h

end Zeta23.OPICARound2.Validation

#print axioms Zeta23.OPICARound2.native_mobius_probe_inverse
#print axioms Zeta23.OPICARound2.native_mobius_delayed_barrier
#print axioms Zeta23.OPICARound2.JPlus_analyticAt
#print axioms Zeta23.OPICARound2.JPlus_exponential_bound
#print axioms Zeta23.OPICARound2.probe_source_zero_count_bound
#print axioms Zeta23.OPICARound2.native_floor_physical_cutoff_bound
#print axioms Zeta23.OPICARound2.native_probe_range_boundary_order
#print axioms Zeta23.OPICARound2.probe_boundary_meromorphic_order_nonneg
#print axioms Zeta23.OPICARound2.native_mobius_residual_norm_tendsto_atTop
#print axioms Zeta23.OPICARound2.native_probe_visible_critical_zero_of_RH
#print axioms Zeta23.OPICARound2.native_probe_target_not_mem_range
#print axioms Zeta23.OPICARound2.native_probe_bounded_input_gap
#print axioms Zeta23.OPICARound2.native_probe_successful_input_norms_tendsto_atTop
#print axioms Zeta23.OPICARound2.native_probe_boundary_taylor_bounds
#print axioms Zeta23.OPICARound2.positive_power_tradeoff
#print axioms Zeta23.OPICARound2.native_probe_boundary_power_cost
#print axioms Zeta23.OPICARound2.native_probe_visible_boundary_input_cost
#print axioms Zeta23.OPICARound2.native_undamped_nonrange_and_input_cost
#print axioms Zeta23.OPICARound2.probeNativeTailAmplitude_norm_lower
#print axioms Zeta23.OPICARound2.probeIntegerTargetPrefix_tail_square_paper
#print axioms Zeta23.OPICARound2.probeIntegerTargetPrefixL2_norm_tendsto_atTop
#print axioms Zeta23.OPICARound2.probeIntegerTailConstant_eq_original
#print axioms Zeta23.OPICARound2.integer_partial_divergence_and_safe_cutoff
#print axioms Zeta23.OPICARound2.probePulse_pairing
#print axioms Zeta23.OPICARound2.probePulseSeparation_paper_lower
#print axioms Zeta23.OPICARound2.probePulseShift_residual
#print axioms Zeta23.OPICARound2.native_isolated_pulse_lower_bound
#print axioms Zeta23.OPICARound2.probeDivisorDefect_inversion
#print axioms Zeta23.OPICARound2.native_squarefree_omission_bound
#print axioms Zeta23.OPICARound2.native_2047_omission_residual_lower
#print axioms Zeta23.OPICARound2.endpoint_probeV_essential_left
#print axioms Zeta23.OPICARound2.endpoint_probeW_essential_left
#print axioms Zeta23.OPICARound2.sourcePrefixColumns_linearIndependent
#print axioms Zeta23.OPICARound2.sourcePrefixLeastEigenvalue_pos
#print axioms Zeta23.OPICARound2.native_prefix_gram_posDef
#print axioms Zeta23.OPICARound2.native_prefix_eigenvalue_pos
#print axioms Zeta23.OPICARound2.native_prefix_gram_residual_bound
#print axioms Zeta23.OPICARound2.native_prefix_coefficient_bound
#print axioms Zeta23.OPICARound2.native_prefix_coordinate_error
#print axioms Zeta23.OPICARound2.native_prefix_coordinate_convergence
#print axioms Zeta23.OPICARound2.probeNegativeWeightedMass_bound
#print axioms Zeta23.OPICARound2.native_negative_output_envelope
#print axioms Zeta23.OPICARound2.probeFullEvaluation_bound
#print axioms Zeta23.OPICARound2.native_negative_output_evaluation_bound
#print axioms Zeta23.OPICARound2.noncausal_probe_leakage
