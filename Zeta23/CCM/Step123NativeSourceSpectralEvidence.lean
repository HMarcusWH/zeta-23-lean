import Zeta23.CCM.Step123NativeResidualOutput
import Zeta23.CCM.Step123OutputFieldEvidence
import Zeta23.CCM.Step123NativeArithmeticRangeEvidence

/-!
# One-source Step123 core/spectral evidence for N01-N28

This typed record extracts source, normalized original detector, true
selected ground, both inverse budgets, own-parity residual/complete Gram,
and ORIGINAL full-complement Schur loss from ONE existing Step123NativeOutput.
No field is provided by a caller and nothing can substitute a second
selector, prime source, or chosen ground.

The complete 44-field contract remains separately open: finite phase
matrix positivity, higher image jets, source-specific forcing estimates
and all other subcontracts must still be audited against exact compiler
declarations and reviewed independently. A green structure is not RH.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

structure Step123NativeSourceSpectralEvidence
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  source_fixed :
    (∀ x : ℝ, 0 ≤ universalSincSource UniversalSinc.fixedScale x) ∧
    tsupport (universalSincSource UniversalSinc.fixedScale) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
    Function.Even (universalSincSource UniversalSinc.fixedScale) ∧
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 ∧
    Zeta23.paperFT
      (fun x : ℝ => (universalSincSource UniversalSinc.fixedScale x : ℂ)) =
      UniversalSinc.product UniversalSinc.fixedScale
  original_trial :
    ∀ x : ℝ,
      out.originalTrial x =
          (fixedOriginalSincTrialNormalization : ℂ) *
            (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
              (nativeOriginalDetectorPhaseSign σ : ℂ) *
              fixedOriginalSincKernel
                (fixedOriginalSincTrialAperture a - x -
                  fixedOriginalSincLobeCenter))
  detector_identified_unit :
    out.retained.state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [out.aperture_gt_four]) ∧
      ‖out.retained.state.detector‖ = 1
  selected_eigenvector :
    ‖out.selectedGround‖ = 1 ∧
    nativePoleNeutralParityCanonical out.retained.state.selectedParity
      (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.cutoff out.selectedGround =
      (out.retained.state.selection.lam : ℂ) • out.selectedGround
  finite_image_unit :
    ‖out.physicalFiniteImage‖ = 1
  finite_image_H1 :
    originalDetectorPhysicalH1Error
      (finitePhysicalSynthesis
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (canonicalNativeCoefficientInclusion σ
          (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
          out.retained.state.detector)) 0 ≤
      Real.sqrt (1 +
        (2 * Real.pi *
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
          fixedOriginalSincTrialAperture a) ^ 2)
  poles :
    canonicalPoleEvenFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) = 0 ∧
    canonicalPoleOddFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) = 0
  schur_loss :
    let state := out.retained.state
    let y := isometricDetectorComplementCoordinate
      (nativeDetectorPredecessorEmbedding σ state.selection)
      state.detector
    y ≠ 0 ∧
      (inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y).re <
        -(Real.exp (β * fixedOriginalSincTrialAperture a)) / 2
  variance :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (inner ℂ p (nativePoleNeutralParityCanonical σ L Kd
        (nativePoleNeutralParityCanonical σ L Kd p))).re -
      canonicalPoleNeutralTrialRayleigh σ L Kd p ^ 2
  gram :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (∑ i, ∑ j,
        canonicalPoleNeutralTrialChannelGram σ L Kd p i j).re
  channels :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    canonicalPoleNeutralTrialResidual σ L Kd p =
      ∑ i, nativeTrialResidual
        (canonicalPoleNeutralTrialChannel σ L Kd i) p
  detector_inverse :
    let state := out.retained.state
    ‖(nativeDetectorPredecessorEquiv σ state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      12 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a)
  selected_inverse :
    let state := out.retained.state
    ‖(nativeSelectedGroundPredecessorEquiv
        state.selectedParity state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      6 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a)
  complement_dimension :
    Module.finrank ℂ
      (nativeDetectorComplement σ out.retained.state.selection) =
        originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) -
          out.retained.state.selection.cutoff + 1
  selected_ground_schur :
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
      inner ℂ (P response) response
  mass_one :
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1
  admissible_selector :
    AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.eta out.retained.state.selection.cutoff

/-- Every proof field follows from the unchanged original source and
a *single* existing retained-state record, with no extra hypotheses. -/
def Step123NativeSourceSpectralEvidence.fromNative
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    Step123NativeSourceSpectralEvidence out where
  source_fixed := step123_fixed_source_evidence
  original_trial := fun x => out.original_trial_reflected x
  detector_identified_unit := out.detector_source_unit
  selected_eigenvector := out.selected_ground_eigen
  finite_image_unit := out.finite_image_unit
  finite_image_H1 := out.finite_image_H1_bound
  poles := out.originalDetector_poles
  schur_loss := out.originalSchur_full_complement
  variance := out.ownNeutralResidual_variance
  gram := out.ownNeutralResidual_gram
  channels := out.ownNeutralResidual_channels
  detector_inverse := out.detector_inverse_budget
  selected_inverse := out.selected_inverse_budget
  complement_dimension := out.original_detector_complement_dimension
  selected_ground_schur := out.selected_ground_shiftedSchur
  mass_one := out.originalSource_mass_one
  admissible_selector := out.source_selector

/-- The same actual zero-generated packet already retains signed
forcing/boundary and native arithmetic/range channels. This adds the
source/spectral N01-N28 evidence without choosing another detector. -/
structure GeneratedStep123ComposedEvidencePacket
    (ρ : zetaZeroConfig.carrier) (β : ℝ)
    (σ : ReversalParity) (R : ℝ) where
  integrated : GeneratedStep123IntegratedPacket ρ β σ R
  source_spectral :
    Step123NativeSourceSpectralEvidence
      integrated.boundary.generated.native

def GeneratedStep123ComposedEvidencePacket.fromIntegrated
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (integrated : GeneratedStep123IntegratedPacket ρ β σ R) :
    GeneratedStep123ComposedEvidencePacket ρ β σ R where
  integrated := integrated
  source_spectral :=
    Step123NativeSourceSpectralEvidence.fromNative
      integrated.boundary.generated.native

/-- Existence, conditional on the precise off-line zero carrier, is
derived from the source-specific producer and contains no bridge. -/
theorem exists_generatedStep123ComposedEvidencePacket
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123ComposedEvidencePacket ρ β σ R) := by
  obtain ⟨integrated⟩ :=
    exists_generatedStep123IntegratedPacket ρ hβ hβρ σ R
  exact ⟨GeneratedStep123ComposedEvidencePacket.fromIntegrated integrated⟩

theorem exists_generatedStep123ComposedEvidencePacket_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123ComposedEvidencePacket ρ β σ R,
      max R 4 <
        fixedOriginalSincTrialAperture
          out.integrated.boundary.generated.sourceData.separation := by
  obtain ⟨integrated, hL⟩ :=
    exists_generatedStep123IntegratedPacket_cofinal ρ hβ hβρ σ R
  exact ⟨GeneratedStep123ComposedEvidencePacket.fromIntegrated integrated, hL⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeSourceSpectralEvidence.fromNative
#print axioms Zeta23.CCM.GeneratedStep123ComposedEvidencePacket.fromIntegrated
#print axioms Zeta23.CCM.exists_generatedStep123ComposedEvidencePacket
#print axioms Zeta23.CCM.exists_generatedStep123ComposedEvidencePacket_cofinal
