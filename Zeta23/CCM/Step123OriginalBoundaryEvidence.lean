import Zeta23.CCM.Step123OutputFieldEvidence
import Zeta23.CCM.OriginalDetectorActualForcingError
import Zeta23.CCM.OriginalDetectorEtaControl
import Zeta23.CCM.Step123NativeAmbientGalerkin
import Zeta23.CCM.OriginalDetectorExteriorPairing
import Zeta23.ExceptionalZero.Step123OutputProducer

/-!
# Source-specific N35-N40 integration on ONE actual generated packet

Nothing in this package is freely chosen by a caller.  All source,
finite detector, actual selected ground, and original smooth exterior
objects are inherited from the unique Step123NativeOutput.
The actual original Weil response is NOT replaced with a selected-ground
contact. The original response retains both tails and interior history.

This is a typed proof package for a verified subset of N35-N40, not an
assertion that all 44 fields or any RH closing cut have been proved.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- The actual native packet's regularity, signed causal histories,
retained selected-ground finite response, and original interior
remain coupled to ONE pre-existing retained state. -/
structure Step123OriginalBoundaryEvidence
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  actual_source_error_smooth :
    ContDiff ℝ 2 out.physicalSourceError
  actual_source_error_supported :
    tsupport out.physicalSourceError ⊆
      Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)
  original_four_histories :
    ∀ x : ℝ,
      nativeWeilPrimeResponse out.originalTrial x =
        out.smoothOriginal.primeHistories x
  original_interior_reconstructed :
    ∀ x : ℝ,
      out.smoothOriginal.response x =
        out.smoothOriginal.left x + out.smoothOriginal.interior x +
          out.smoothOriginal.right x
  selected_legal_normal_outer_exact :
    out.selectedNativeResponseL2 =
      out.selectedNeutralProjectedResponse +
        out.selectedPoleNormalResidual + out.selectedOuterGalerkinResidual
  selected_outer_orthogonal_to_legal :
    ∀ (v : euclideanBoundaryFlatSubspace out.retained.state.selection.cutoff),
      inner ℂ
        (canonicalLegalPhysicalIsometry out.aperture_pos
          out.retained.state.selection.cutoff v)
        out.selectedOuterGalerkinResidual = 0
  actual_quantified_projected_forcing_error :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (v : nativePoleNeutralParitySpace σ
        (fixedOriginalSincTrialAperture a)
        (out.retained.state.selection.cutoff - 1)),
        ‖zetaZeroConfig.W out.physicalSourceError
          (finitePhysicalSynthesis
            (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1)
            (canonicalNativeCoefficientInclusion σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1) v)) +
          (out.retained.state.selection.eta : ℂ) *
            EF.weilTest out.physicalSourceError
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
          (C_Q * (1 + fixedOriginalSincTrialAperture a) *
            Real.exp (fixedOriginalSincTrialAperture a / 2) *
            Real.sqrt (1 +
              (2 * Real.pi *
                (out.retained.state.selection.cutoff - 1 : ℕ) /
                fixedOriginalSincTrialAperture a) ^ 2) +
            out.retained.state.selection.eta) *
            nativePhysicalH1Norm out.physicalSourceError * ‖v‖
  actual_source_shift_upper :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      out.retained.state.selection.eta ≤
        (C_Q / 2) * (1 + fixedOriginalSincTrialAperture a) *
        Real.exp (fixedOriginalSincTrialAperture a / 2) *
          (1 + (2 * Real.pi *
            (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
              fixedOriginalSincTrialAperture a) ^ 2)
  original_compact_pairing_retains_interior :
    ∀ (g : ℝ → ℂ), Continuous g → HasCompactSupport g →
      (∫ x : ℝ,
        originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a x * g x) =
        (∫ x : ℝ,
          originalSmoothWeilLeftExterior (nativeOriginalDetectorPhaseSign σ) a x * g x) +
        (∫ x : ℝ,
          originalSmoothWeilInteriorHistory (nativeOriginalDetectorPhaseSign σ) a x * g x) +
        (∫ x : ℝ,
          originalSmoothWeilRightExterior (nativeOriginalDetectorPhaseSign σ) a x * g x)

/-- All nine proof fields are constructed, not supplied. The original
detector and selected ground are distinct by their existing source types. -/
def Step123OriginalBoundaryEvidence.fromNative
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    Step123OriginalBoundaryEvidence out where
  actual_source_error_smooth := out.physicalSourceError_admissible.1
  actual_source_error_supported := out.physicalSourceError_admissible.2
  original_four_histories := out.original_prime_histories
  original_interior_reconstructed := out.original_response_reconstruction
  selected_legal_normal_outer_exact := out.selectedResponse_decomposition
  selected_outer_orthogonal_to_legal := out.selectedOuterGalerkin_orthogonal
  actual_quantified_projected_forcing_error := out.actualProjectedForcing_error_bound
  actual_source_shift_upper := by
    obtain ⟨C_Q, hC, h⟩ := originalDetector_eta_source_upper
    exact ⟨C_Q, hC, h β σ a out⟩
  original_compact_pairing_retains_interior := fun g hg hgc =>
    originalSmoothWeilResponse_compactPairing_split
      (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos.le hg hgc

/-- The actual zero-indexed producer inherits these N35-N40
supporting constraints without supplying a second detector, new
source, arbitrary exterior, or global L2 assumption. -/
def generatedOriginalBoundaryEvidence
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (out : GeneratedStep123Output ρ β σ R) :
    Step123OriginalBoundaryEvidence out.native :=
  Step123OriginalBoundaryEvidence.fromNative out.native

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123OriginalBoundaryEvidence.fromNative
#print axioms Zeta23.CCM.generatedOriginalBoundaryEvidence
