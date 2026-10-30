import Zeta23.OPICARound4.QuarticErrorReduction

/-! Independent expected-type consumers for the complete source error
reduction. In particular, the uniform threshold must precede the packet,
and the actual generated lower bound is not a source arithmetic upper law. -/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.OPICARound4.Validation

open CCM ExceptionalZero

theorem quartic_rate_consumer (p t c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ p *
      Real.exp (t * L - c * originalDetectorQuarticRootScale L)) atTop (𝓝 0) :=
  quartic_polynomial_exp_tendsto_zero p t c hc

theorem source_shift_consumer {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.retained.state.selection.eta ≤ sourceEtaGrowthConstant *
      (fixedOriginalSincTrialAperture a) ^ 7 * Real.exp (fixedOriginalSincTrialAperture a / 2) :=
  source_eta_polynomial_bound out

theorem same_detector_inverse_consumer {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (hβ : 0 < β) :
    ‖(nativeDetectorPredecessorEquiv σ out.retained.state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      24 * (fixedOriginalSincTrialAperture a) ^ 4 :=
  detector_inverse_polynomial_bound out hβ

theorem complete_error_envelope_consumer {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (hβ : 0 < β) :
    sourceSchurErrorBudget out ≤ sourceSchurUniformEnvelope (fixedOriginalSincTrialAperture a) :=
  sourceSchurErrorBudget_le_uniformEnvelope out hβ

theorem all_exponential_rates_consumer (M : ℝ) :
    Tendsto (fun L : ℝ => sourceSchurUniformEnvelope L * Real.exp (M * L)) atTop (𝓝 0) :=
  sourceSchurUniformEnvelope_mul_exp_tendsto_zero M

theorem threshold_before_packet_consumer (M δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ (β : ℝ) (σ : ReversalParity) (a : ℝ)
      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →
      |detectorSchurLoss out - smoothSourceMain out| <
        δ * Real.exp (-M * fixedOriginalSincTrialAperture a) :=
  exists_uniform_source_schur_error_threshold M δ hδ

theorem native_packet_lower_consumer :
    ∃ L₀ : ℝ, ∀ (β : ℝ) (σ : ReversalParity) (a : ℝ)
      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →
      Real.exp (β * fixedOriginalSincTrialAperture a) / 4 < smoothSourceMain out :=
  exists_uniform_smooth_source_main_lower_threshold

theorem generated_packet_lower_consumer :
    ∃ L₀ : ℝ, ∀ (ρ : zetaZeroConfig.carrier) (β : ℝ) (σ : ReversalParity) (R : ℝ)
      (g : GeneratedStep123CompleteOutput ρ β σ R), L₀ ≤ R →
      Real.exp (β * fixedOriginalSincTrialAperture g.generated.sourceData.separation) / 4 <
        smoothSourceMain g.generated.native :=
  exists_generated_smooth_source_main_lower_threshold

end Zeta23.OPICARound4.Validation

#print axioms Zeta23.OPICARound4.Validation.threshold_before_packet_consumer
#print axioms Zeta23.OPICARound4.Validation.generated_packet_lower_consumer
