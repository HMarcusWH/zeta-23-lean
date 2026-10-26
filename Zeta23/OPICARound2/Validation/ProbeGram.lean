import Zeta23.OPICARound2.ProbeGram

noncomputable section

open Set MeasureTheory Matrix
open scoped Topology ENNReal BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2.Validation

theorem expected_p06_tail (t : ℝ) (ht : 2 * probeSigma ≤ t) :
    probeV t = 2 * JPlus (-3 / 2 : ℂ) *
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) := probeV_tail ht

theorem expected_p06_remainder : HasCompactSupport
    (fun t : ℝ => probeV t - if 0 ≤ t then 2 * JPlus (-3 / 2 : ℂ) *
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) else 0) :=
  probeTailRemainder_hasCompactSupport

theorem expected_p06_correlation (L : ℝ) (hL : 2 * probeSigma ≤ |L|) :
    (∫ t : ℝ, conj (probeV t) * probeV (t + L)) =
      (CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3) *
        Complex.exp (-(3 / 2 : ℂ) * ((|L| : ℝ) : ℂ)) :=
  probeCorrelation_separated hL

theorem domain_p06_target_shift_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lags : ι → ℝ) (hsep : ∀ i j, i ≠ j → 2 * probeSigma ≤ |lags i - lags j|)
    (i j : ι) :
    Matrix.gram ℂ (fun k => CCM.nativeCompletionL2Delay (lags k)
      (probeTarget : CCM.NativeCompletionL2)) i j =
      if i = j then ((‖probeTarget‖ ^ 2 : ℝ) : ℂ) else
        (CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3) *
          Complex.exp (-(3 / 2 : ℂ) * ((|lags i - lags j| : ℝ) : ℂ)) :=
  probeTargetShiftGram_separated lags hsep i j

theorem expected_p08_positive_definite (N : ℕ) (_hN : 1 ≤ N) :
    (Matrix.gram ℂ (fun i : Fin N =>
      CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (i.val + 1)))).PosDef :=
  probe_finite_gram_positive N

theorem domain_p08_actual_synthesis (N : ℕ) (x : Fin N → ℂ) :
    probeSynthesis N x = ∑ i : Fin N, x i •
      CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (i.val + 1)) := rfl

theorem expected_p08_actual_columns_independent (N : ℕ) :
    LinearIndependent ℂ (fun i : Fin N =>
      CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (i.val + 1))) :=
  probeColumns_linearIndependent N

theorem expected_p12_explicit_primal (N : ℕ → ℕ)
    (x : ∀ k : ℕ, Fin (N k) → ℂ)
    (h : Filter.Tendsto
      (fun k => ‖probeTarget - ∑ i : Fin (N k), x k i •
        CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (i.val + 1))‖)
      Filter.atTop (𝓝 0)) : RiemannHypothesis :=
  rh_of_probe_residual_limit N x h

theorem expected_p12_exact_projection_error
    (h : Filter.Tendsto
      (fun N => ‖probeTarget - ((probeFiniteSpace N).orthogonalProjectionOnto probeTarget :
        CCM.nativeCompletionCausalL2)‖) Filter.atTop (𝓝 0)) : RiemannHypothesis :=
  rh_of_probe_error_limit h

theorem expected_p12_subsequence (N : ℕ → ℕ)
    (_hcofinal : Filter.Tendsto N Filter.atTop Filter.atTop)
    (h : Filter.Tendsto (fun k => probeError (N k)) Filter.atTop (𝓝 0)) : RiemannHypothesis :=
  rh_of_probe_error_subsequence_limit N h

theorem expected_p09_schur (N : ℕ) :
    ((probeError N ^ 2 : ℝ) : ℂ) = (‖probeTarget‖ ^ 2 : ℝ) -
      star (fun i : Fin N => inner ℂ (probeColumn (i.val + 1)) probeTarget) ⬝ᵥ
        ((Matrix.gram ℂ (fun i : Fin N => probeColumn (i.val + 1)))⁻¹ *ᵥ
          (fun i : Fin N => inner ℂ (probeColumn (i.val + 1)) probeTarget)) :=
  probeError_sq_schur N

theorem expected_p09_bordered_determinant (N : ℕ) :
    ((probeError N ^ 2 : ℝ) : ℂ) = (probeBorderedGram N).det / (probeGram N).det :=
  probeError_sq_determinant_ratio N

theorem domain_p09_bordered_native_gram (N : ℕ) : probeBorderedGram N =
    Matrix.gram ℂ (Sum.elim
      (fun i : Fin N => CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)
        (probeInput (i.val + 1))) (fun _ : Unit => probeTarget)) :=
  probeBorderedGram_eq_gram N

theorem expected_p09_actual_minimizer (N : ℕ) :
    probeBestOutput N = probeFiniteOutput
      ((probeGram N)⁻¹ *ᵥ (fun i : Fin N => inner ℂ (probeColumn (i.val + 1)) probeTarget)) :=
  probeBestOutput_eq_coefficients N

theorem expected_p09_global_minimum {N : ℕ} (x : Fin N → ℂ) :
    probeError N ≤ ‖probeTarget - ∑ i : Fin N, x i •
      CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (i.val + 1))‖ :=
  probeError_le_residual x

theorem expected_p09_completion_of_squares {N : ℕ} (x : Fin N → ℂ) :
    ‖probeResidual x‖ ^ 2 = probeError N ^ 2 +
      ‖probeBestOutput N - probeFiniteOutput x‖ ^ 2 := probe_residual_pythagoras x

theorem expected_p07_first_mixed :
    inner ℂ (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput 1))
      probeTarget = (probeQ0 : ℂ) +
        (CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3) * (riemannZeta (2 : ℂ) - 1) :=
  probeMixedPairing_one

theorem expected_p07_other_mixed (n : ℕ) (hn : 2 ≤ n) :
    inner ℂ (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput n))
      probeTarget = (CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3) *
        riemannZeta (2 : ℂ) / (n : ℂ) ^ 2 := probeMixedPairing_ge_two hn

theorem domain_p07_source_constant :
    CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3 =
      (((16 / 3 : ℝ) *
        (∫ t : ℝ, Real.cosh ((3 / 2 : ℝ) * t) * CCM.universalSincSource probeSigma t) ^ 2 : ℝ) : ℂ) :=
  probeCorrelationConstant_eq_real

theorem expected_p07_C_bounds : (16 / 3 : ℝ) ≤ probeCorrelationC ∧
    probeCorrelationC ≤ (16 / 3 : ℝ) * Real.cosh (3 * probeSigma / 2) ^ 2 :=
  probeCorrelationC_bounds

theorem expected_p07_C_rational_upper : probeCorrelationC ≤
    (16 / 3 : ℝ) * (134217728 / 134217719 : ℝ) ^ 2 := probeCorrelationC_rational_upper

theorem domain_p07_first_cell (t : ℝ) (ht : t < Real.log 2) :
    (∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) *
      (CCM.nativeOriginalSource ((t - s) - probeSigma) : ℂ)) =
    ∫ s : ℝ, (CCM.nativeCompletionCorrection s : ℂ) *
      (CCM.nativeOriginalSource ((t - s) - probeSigma) : ℂ) :=
  probeW_eq_probeV_first_cell ht

theorem expected_p10_monotone_component (N M : ℕ) (hNM : N ≤ M) :
    probeError M ≤ probeError N := probeError_antitone hNM

theorem expected_p12_squared_schur
    (h : Filter.Tendsto (fun N => probeQ0 -
      (star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)).re)
      Filter.atTop (𝓝 0)) : RiemannHypothesis := rh_of_probe_schur_limit h

theorem domain_p10_native_innovation (N : ℕ) : probeInnovation N =
    CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (N + 1)) -
      (probeFiniteSpace N).starProjection
        (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) (probeInput (N + 1))) := rfl

theorem expected_p10_positive_innovation (N : ℕ) :
    0 < ‖probeColumn (N + 1) -
      (probeFiniteSpace N).starProjection (probeColumn (N + 1))‖ ^ 2 :=
  probeInnovationNormSq_pos N

theorem expected_p10_native_projection_update (N : ℕ) : probeBestOutput (N + 1) =
    probeBestOutput N +
      (inner ℂ (probeInnovation N) probeTarget / ((‖probeInnovation N‖ ^ 2 : ℝ) : ℂ)) •
        probeInnovation N := probeBestOutput_innovation N

theorem expected_p10_exact_decrement (N : ℕ) : probeError N ^ 2 - probeError (N + 1) ^ 2 =
    ‖inner ℂ (probeColumn (N + 1) -
      (probeFiniteSpace N).starProjection (probeColumn (N + 1))) probeTarget‖ ^ 2 /
      ‖probeColumn (N + 1) -
        (probeFiniteSpace N).starProjection (probeColumn (N + 1))‖ ^ 2 :=
  probe_innovation_decrement N

theorem expected_p11_weighted_dirichlet_norm {N : ℕ} (x : Fin N → ℂ) :
    ‖probeResidual x‖ ^ 2 = ∫ tau : ℝ,
      (‖CCM.nativeOriginalSourceLaplace (Complex.I * (tau : ℂ))‖ ^ 2 /
        (2 * Real.pi * (tau ^ 2 + 9 / 4))) *
      ‖1 - riemannZeta (1 / 2 + Complex.I * (tau : ℂ)) *
        (∑ i : Fin N, x i * ((i.val + 1 : ℕ) : ℂ) ^ (-(1 / 2 + Complex.I * (tau : ℂ))))‖ ^ 2 := by
  simpa only [probeOmega, probeBoundaryDefect, probeDirichletPolynomial_eq_cpow] using
    (probe_dirichlet_norm x).2

theorem expected_p11_integrable_energy {N : ℕ} (x : Fin N → ℂ) :
    Integrable (fun tau : ℝ => probeOmega tau *
      ‖1 - riemannZeta (1 / 2 + Complex.I * (tau : ℂ)) *
        probeDirichletPolynomial x (1 / 2 + Complex.I * (tau : ℂ))‖ ^ 2) :=
  (probe_dirichlet_norm x).1

theorem domain_p11_native_residual {N : ℕ} (x : Fin N → ℂ) :
    ‖causalKernelOperator probeC probeC_integrable (fun t ht => probeC_zero_of_neg t ht) probeSource -
      ∑ i : Fin N, x i • CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)
        (probeInput (i.val + 1))‖ ^ 2 =
      ∫ tau : ℝ, probeOmega tau * ‖probeBoundaryDefect x tau‖ ^ 2 :=
  (probe_dirichlet_norm x).2

theorem domain_p11_actual_boundary (tau : ℝ) :
    (∫ t : ℝ, Complex.exp (-(Complex.I * (tau : ℂ)) * (t : ℂ)) *
      (CCM.nativePositiveCompletion t : ℂ)) =
      CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        riemannZeta (Complex.I * (tau : ℂ) + 1 / 2) := nativeCompletionLaplace_boundary tau

theorem expected_s02_native_jets : 0 < probeQbar ∧
    QPlus (1 / 2 : ℂ) = (probeQbar : ℂ) ∧
    iteratedDeriv 2 (probeLaplace probeV) (1 / 2 : ℂ) = 0 ∧
    iteratedDeriv 3 (probeLaplace probeV) (1 / 2 : ℂ) = 3 * (probeQbar : ℂ) ∧
    probeLaplace probeW (1 / 2 : ℂ) = 0 ∧ deriv (probeLaplace probeW) (1 / 2 : ℂ) = 0 ∧
    iteratedDeriv 2 (probeLaplace probeW) (1 / 2 : ℂ) = (probeQbar : ℂ) := by
  rcases native_probe_pole_moment_constraints with ⟨hq, hQ, hV2, hV3, hW0, hW1, hW2, _, _⟩
  exact ⟨hq, hQ, hV2, hV3, hW0, hW1, hW2⟩

theorem expected_s02_full_error_bounds {N : ℕ} (x : Fin N → ℂ) :
    probeQbar * ‖probeDirichletPolynomial x 1‖ ≤ Real.sqrt 24 * ‖probeResidual x‖ ∧
    ‖3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
      iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1‖ ≤
        Real.sqrt 720 * ‖probeResidual x‖ ∧
    (probeDirichletPolynomial x 1 = 0 →
      3 * probeQbar * ‖1 - deriv (probeDirichletPolynomial x) 1‖ ≤ Real.sqrt 720 * ‖probeResidual x‖) ∧
    deriv (probeDirichletPolynomial x) 1 =
      -(∑ i : Fin N, x i * (Real.log (i.val + 1 : ℕ) : ℂ) / ((i.val + 1 : ℕ) : ℂ)) := by
  rcases native_probe_pole_moment_constraints with ⟨_, _, _, _, _, _, _, h, _⟩
  exact h N x

theorem expected_s02_limits (N : ℕ → ℕ) (x : ∀ k : ℕ, Fin (N k) → ℂ)
    (h : Filter.Tendsto (fun k => ‖probeResidual (x k)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun k => probeDirichletPolynomial (x k) 1) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k => deriv (probeDirichletPolynomial (x k)) 1) Filter.atTop (𝓝 1) := by
  rcases native_probe_pole_moment_constraints with ⟨_, _, _, _, _, _, _, _, hL⟩
  exact hL N x h

theorem domain_s02_literal_source : probeQbar =
    ∫ t : ℝ, Real.exp (-t / 2) * CCM.universalSincSource probeSigma (t - probeSigma) := rfl

theorem domain_s02_actual_completed_jet :
    iteratedDeriv 2 (fun z : ℂ => ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) *
      (∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) *
        (CCM.nativeOriginalSource ((t - s) - probeSigma) : ℂ))) (1 / 2 : ℂ) = (probeQbar : ℂ) :=
  probeW_second_half

theorem domain_s02_exact_witness_costs :
    ‖CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) 2‖ ^ 2 = 24 ∧
    ‖CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) 3‖ ^ 2 = 720 := by
  constructor
  · convert probeHalfWitness_norm_sq 2 using 1 <;> norm_num
  · convert probeHalfWitness_norm_sq 3 using 1 <;> norm_num

theorem domain_s02_general_residual_jet {N : ℕ} (x : Fin N → ℂ) :
    iteratedDeriv 3 (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0
      (probeTarget - ∑ i : Fin N, x i • CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)
        (probeInput (i.val + 1)) : ProbeL2)) (1 / 2 : ℂ) =
      3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
        iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1 :=
  probeResidual_third_half x

theorem control_p11_zero_trial_normalization : ‖probeTarget‖ ^ 2 = ∫ tau : ℝ, probeOmega tau := by
  simpa [probeResidual, probeFiniteOutput, probeBoundaryDefect, probeDirichletPolynomial] using
    (probe_dirichlet_norm (fun i : Fin 0 => Fin.elim0 i)).2

theorem control_s02_zero_trial_derivative_cost :
    3 * probeQbar ≤ Real.sqrt 720 * ‖probeTarget‖ := by
  have h := probe_pole_constrained_derivative_bound (fun i : Fin 0 => Fin.elim0 i)
    (by simp [probeDirichletPolynomial])
  rw [probeDirichletPolynomial_deriv_one] at h
  simpa [probeResidual, probeFiniteOutput, probeDirichletPolynomial] using h

#print axioms Zeta23.OPICARound2.probe_tail_and_correlation
#print axioms Zeta23.OPICARound2.probe_finite_gram_positive
#print axioms Zeta23.OPICARound2.rh_of_probe_error_limit
#print axioms Zeta23.OPICARound2.probe_schur_error
#print axioms Zeta23.OPICARound2.probe_target_column
#print axioms Zeta23.OPICARound2.probe_monotone_innovation
#print axioms Zeta23.OPICARound2.probe_dirichlet_norm
#print axioms Zeta23.OPICARound2.nativeCompletionLaplace_boundary
#print axioms Zeta23.OPICARound2.native_probe_pole_moment_constraints

end Zeta23.OPICARound2.Validation
