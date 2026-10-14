import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.CanonicalPoleNeutralTrialResidualChannels
import Zeta23.CCM.NativeSelectedGroundSchur

/-!
# Step123 true neutral residual, full Gram and inverse budgets

Typed N18-N28 consumers on ONE native output packet. The residual is on
the ORIGINAL detector's own parity space, not a generic legal residual
or a selected-ground trial.  The detector complement at Kd and the
selected-ground one-shell shift remain separate.

These facts are proof-bearing component data, not the missing signed
arithmetic upper estimate or a claim that all 44 packet groups are filled.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- N27: the original own-parity neutral residual has the EXACT
variance, including both the canonical double application and the
actual normalized detector Rayleigh value. -/
theorem Step123NativeOutput.ownNeutralResidual_variance
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (inner ℂ p (nativePoleNeutralParityCanonical σ L Kd
        (nativePoleNeutralParityCanonical σ L Kd p))).re -
      canonicalPoleNeutralTrialRayleigh σ L Kd p ^ 2 :=
  canonicalPoleNeutralTrialResidual_variance_eq σ _ _ _
    out.retained.state.detector_unit

/-- N28: the same original own-parity neutral residual equals the
FOUR native channel residuals' complete signed complex Gram sum. -/
theorem Step123NativeOutput.ownNeutralResidual_gram
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (∑ i, ∑ j,
        canonicalPoleNeutralTrialChannelGram σ L Kd p i j).re :=
  canonicalPoleNeutralTrialResidual_gram_sum σ _ _ out.retained.state.detector

/-- N27/N28: do not conflate the actual own-parity neutral
residual with any legal nonneutral trial or chosen eigenvector. -/
theorem Step123NativeOutput.ownNeutralResidual_channels
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    canonicalPoleNeutralTrialResidual σ L Kd p =
      ∑ i, nativeTrialResidual
        (canonicalPoleNeutralTrialChannel σ L Kd i) p :=
  canonicalPoleNeutralTrialResidual_channels_sum σ _ _
    out.retained.state.detector

/-- N19: the shifted detector's predecessor inverse has budget 12
at shift minus eta. -/
theorem Step123NativeOutput.detector_inverse_budget
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let state := out.retained.state
    ‖(nativeDetectorPredecessorEquiv σ state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      12 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a) :=
  nativeDetectorPredecessorEquiv_inverse_bound σ out.retained.state.inverses

/-- N19/N26: the separately selected ground relative inverse has
budget 6 and uses lambda, NOT the detector shift. -/
theorem Step123NativeOutput.selected_inverse_budget
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let state := out.retained.state
    ‖(nativeSelectedGroundPredecessorEquiv
        state.selectedParity state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      6 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a) :=
  nativeSelectedGroundPredecessorEquiv_inverse_bound
    out.retained.state.selectedParity out.retained.state.inverses

/-- N25: the original detector's Schur-complement dimension is the
full Kd-K+1; no one-shell replacement is authorized. -/
theorem Step123NativeOutput.original_detector_complement_dimension
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    Module.finrank ℂ
      (nativeDetectorComplement σ out.retained.state.selection) =
        originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) -
          out.retained.state.selection.cutoff + 1 :=
  nativeDetectorComplement_finrank σ out.retained.state.selection

/-- N26: a selected-ground Schur equation uses the selected lambda
and its one-dimensional successor shell, NOT the original detector. -/
theorem Step123NativeOutput.selected_ground_shiftedSchur
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let state := out.retained.state
    let gamma := state.selectedParity
    let J := nativeSelectedGroundPredecessorEmbedding gamma state.selection
    let T := nativePoleNeutralParityShifted gamma
      (fixedOriginalSincTrialAperture a)
      state.selection.cutoff state.selection.lam
    let P := nativeSelectedGroundPredecessorEquiv gamma state.inverses
    let y := isometricDetectorComplementCoordinate J state.selectedGround
    let response := isometricDetectorResponse J T P y
    inner ℂ (nativePoleNeutralParityCanonical gamma
        (fixedOriginalSincTrialAperture a) state.selection.cutoff
        (y : nativePoleNeutralParitySpace gamma
          (fixedOriginalSincTrialAperture a) state.selection.cutoff))
        (y : nativePoleNeutralParitySpace gamma
          (fixedOriginalSincTrialAperture a) state.selection.cutoff) -
      (state.selection.lam : ℂ) * inner ℂ
        (y : nativePoleNeutralParitySpace gamma
          (fixedOriginalSincTrialAperture a) state.selection.cutoff)
        (y : nativePoleNeutralParitySpace gamma
          (fixedOriginalSincTrialAperture a) state.selection.cutoff) =
      inner ℂ (P response) response :=
  selectedGround_shiftedSchur_eq out.retained.state

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeOutput.ownNeutralResidual_variance
#print axioms Zeta23.CCM.Step123NativeOutput.ownNeutralResidual_gram
#print axioms Zeta23.CCM.Step123NativeOutput.detector_inverse_budget
#print axioms Zeta23.CCM.Step123NativeOutput.selected_inverse_budget
#print axioms Zeta23.CCM.Step123NativeOutput.original_detector_complement_dimension
