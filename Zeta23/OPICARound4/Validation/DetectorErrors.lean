import Zeta23.OPICARound4.SchurErrorTransport

noncomputable section
open MeasureTheory

namespace Zeta23.OPICARound4
open CCM ExceptionalZero

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Independent expected type keeps the smooth forcing on the identical
predecessor, with the positive eta spectral shift and complete Weil form. -/
theorem validation_smooth_source_forcing {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v (smoothSourceForcing out) =
      zetaZeroConfig.W out.originalTrial (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) * EF.weilTest out.originalTrial (out.forcingTest v) 0 :=
  smoothSourceForcing_pairing out v

/-- This checks the full finite comparison rather than a definition of a
desired arithmetic estimate. No bound on smoothSourceMain is a premise. -/
theorem validation_detector_schur_error {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    |nativeOriginalAdmissibleSchurLoss σ out.source_selector -
      ((inner ℂ (smoothSourceForcing out)
          ((nativeDetectorPredecessorEquiv σ out.retained.state.inverses).symm
            (smoothSourceForcing out))).re -
        (zetaZeroConfig.W out.originalTrial out.originalTrial).re -
          out.retained.state.selection.eta * ‖smoothSourceL2 out‖ ^ 2)| ≤
      sourceInverseBudget out * sourceForcingErrorBudget out *
        (2 * finiteForcingBudget out + sourceForcingErrorBudget out) +
      sourceEnergyErrorBudget (fixedOriginalSincTrialAperture a) +
      out.retained.state.selection.eta * sourceImageErrorBudget (fixedOriginalSincTrialAperture a) *
        (2 + sourceImageErrorBudget (fixedOriginalSincTrialAperture a)) :=
  detectorSchurLoss_sub_smoothSourceMain_bound out

theorem validation_detector_first_cutoff {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) (hK : out.retained.state.selection.cutoff = 3) :
    out.retained.predecessorForcing = 0 ∧ smoothSourceForcing out = 0 ∧
      detectorSchurLoss out = -finiteSourceEnergy out - out.retained.state.selection.eta := by
  exact ⟨(detectorForcing_zero_at_first out hK).1,
    (detectorForcing_zero_at_first out hK).2, detectorSchurLoss_at_first out hK⟩

end Zeta23.OPICARound4

#print axioms Zeta23.OPICARound4.validation_smooth_source_forcing
#print axioms Zeta23.OPICARound4.validation_detector_schur_error
#print axioms Zeta23.OPICARound4.validation_detector_first_cutoff
