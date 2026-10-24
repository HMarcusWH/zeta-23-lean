import Zeta23.OPICAFollowup

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation
open Zeta23 Zeta23.OPICA Zeta23.CCM Zeta23.ExceptionalZero

theorem expected_canonical_recovery
    {𝕜 E Y H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜)
    (hker : P.ker ⊓ C.ker ≤ ell.ker) :
    (∀ x, orthogonalRecovery P C ell hker (jointObservation P C x) = ell x) ∧
    (∀ y : WithLp 2 (Y × H), y ∈ (jointObservation P C).rangeᗮ →
      orthogonalRecovery P C ell hker y = 0) ∧
    ‖orthogonalRecovery P C ell hker‖ =
      sSup {q : ℝ | ∃ x : E, jointObservation P C x ≠ 0 ∧
        q = ‖ell x‖ / ‖jointObservation P C x‖} ∧
    (∀ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      (∀ x, R (jointObservation P C x) = ell x) →
        ‖orthogonalRecovery P C ell hker‖ ≤ ‖R‖) ∧
    (∀ epsilon : ℝ, 0 ≤ epsilon → ∀ x : E, ∀ y : WithLp 2 (Y × H),
      ‖y - jointObservation P C x‖ ≤ epsilon →
        ‖ell x - orthogonalRecovery P C ell hker y‖ ≤
          optimalRecoveryCost P C ell * epsilon) := by
  exact ⟨orthogonalRecovery_on_observation P C ell hker,
    orthogonalRecovery_zero_on_orthogonal P C ell hker,
    orthogonalRecovery_norm_eq_optimalRecoveryCost P C ell hker,
    orthogonalRecovery_minimal P C ell hker,
    orthogonalRecovery_noise_bound P C ell hker⟩

theorem expected_filter_causal_actions (state : NativeCausalState)
    (Q : ℕ) (hQ : 0 < Q) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (Y : ℝ) (hY : 0 ≤ Y) (r : ℕ) :
    finiteEulerFilter Q state = (NativeGenerator.finiteEuler Q hQ).act state ∧
    inverseFiniteEulerFilter Q state = (NativeGenerator.inverseFiniteEuler Q hQ).act state ∧
    rationalCausalFilter a b hb state = (NativeGenerator.rational a b ha hb).act state ∧
    truncatedInverseResidual Y r state = (NativeGenerator.residualPowerReal Y r).act state ∧
    (∀ z : ℂ, (finiteEulerFilter Q state).laplace z =
      finiteEulerMultiplier Q z * state.laplace z) ∧
    (∃ S : ℝ, ∀ z : ℂ, S < z.re →
      (inverseFiniteEulerFilter Q state).laplace z =
        (finiteEulerMultiplier Q z)⁻¹ * state.laplace z) ∧
    (∀ z : ℂ, 0 ≤ z.re → (∀ term ∈ state, term.regular.exponent < z.re) →
      (rationalCausalFilter a b hb state).laplace z =
        ((z + (a : ℂ)) / (z + (b : ℂ))) * state.laplace z) ∧
    (∃ S : ℝ, ∀ z : ℂ, S < z.re →
      (truncatedInverseResidual Y r state).laplace z =
        (1 - riemannZeta (z + 1 / 2) * truncatedMoebiusRealMultiplier Y z)^(r + 1) *
          state.laplace z) := by
  exact ⟨finiteEulerFilter_actual_action Q hQ state,
    inverseFiniteEulerFilter_actual_action Q hQ state,
    rationalCausalFilter_actual_action a b ha hb state,
    truncatedInverseResidual_actual_action Y r state,
    finiteEulerFilter_laplace Q state,
    inverseFiniteEulerFilter_laplace Q state,
    fun z hz0 hz => rationalCausalFilter_laplace a b hb state hz0 hz,
    truncatedInverseResidual_laplace Y hY r state⟩

theorem expected_followup_native_output
    {rho : zetaZeroConfig.carrier} {beta : ℝ} {phase : ReversalParity} {late : ℝ}
    (out : FollowupNativeOutput rho beta phase late) :
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine :=
  followupNativeOutput_actual_source_and_input out

theorem expected_followup_native_output_each_phase
    (rho : zetaZeroConfig.carrier) {beta : ℝ}
    (hbeta : 0 < beta) (hgap : beta < |(rho : ℂ).re - 1 / 2|) :
    ∀ (phase : ReversalParity) (late : ℝ),
      ∃ out : FollowupNativeOutput rho beta phase late,
        max late step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
        (step123OpicaView out).field = nativeOriginalPrimeField ∧
        (step123OpicaView out).input = nativeCompletedInput ∧
        Step123SameStateFieldRecord out.generated.native ∧
        GeneratedStep123RangeObstruction rho out.generated.offLine :=
  followupNativeOutput_eachPhase rho hbeta hgap

end Zeta23.OPICAFollowup.Validation

#print axioms Zeta23.OPICAFollowup.Validation.expected_canonical_recovery
#print axioms Zeta23.OPICAFollowup.Validation.expected_filter_causal_actions
#print axioms Zeta23.OPICAFollowup.Validation.expected_followup_native_output
#print axioms Zeta23.OPICAFollowup.Validation.expected_followup_native_output_each_phase
