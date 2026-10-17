import Zeta23.CCM.NativeOriginalExteriorHistory
import Zeta23.CCM.Step123NativeCorePacket
import Zeta23.CCM.CanonicalPhysicalTrialRealization
import Zeta23.CCM.UniversalSincPhysicalBounds
import Zeta23.CCM.NativeCompletionPublicAPI

/-!
# Step 1-3 mathematical native output data, source-pinned core

This is an ACTIVE typed constructor over ONE generated original detector
and ONE retained state. Every derived view is definitionally computed
from it. The complete N01-N40 release is a separate proof obligation:
the still-open projected-error/normal and complete history contracts
are NOT silently supplied by a field, and are not asserted here.

No rho is stored in this native record. The exact actual-zero extension
is made downstream by Step123OutputProducer.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

structure Step123NativeOutput (β : ℝ) (σ : ReversalParity) (a : ℝ) where
  aperture_pos : 0 < fixedOriginalSincTrialAperture a
  aperture_gt_four : 4 < fixedOriginalSincTrialAperture a
  /-- The unchanged original smooth trial has the producer's already
  proved negative margin at this same separation and original phase. -/
  original_depth :
    (zetaZeroConfig.W
      (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a)
      (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a)).re ≤
        -4 * Real.exp (β * fixedOriginalSincTrialAperture a)
  retained : Step123NativeCorePacket σ
    (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    (Real.exp (β * fixedOriginalSincTrialAperture a)) aperture_pos
  detector_source_eq :
    retained.state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [aperture_gt_four])
  source_selector :
    AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture a)
      retained.state.selection.eta retained.state.selection.cutoff
  smoothOriginal :
    OriginalNativeExteriorRecord (nativeOriginalDetectorPhaseSign σ) a aperture_pos
  smoothOriginal_eq :
    smoothOriginal =
      OriginalNativeExteriorRecord.fromOriginalSource
        (nativeOriginalDetectorPhaseSign σ) a aperture_pos

/-- Constructed from exactly the given actual retained selection, with
no second ground, inverse, detector or source-history hypothesis. -/
def Step123NativeOutput.ofRetained
    {β R : ℝ} (σ : ReversalParity)
    (d : OriginalDetectorPaddedFinitePhaseData β
      (nativeOriginalDetectorPhaseSign σ) R)
    (state : DetectorRetainedSchurState σ
      (fixedOriginalSincTrialAperture d.separation)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
      (Real.exp (β * fixedOriginalSincTrialAperture d.separation))
      d.aperture_pos)
    (hdet : state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        d.two_le_aperture)
    (hsel : AdmissibleDetectorSelector β
      (fixedOriginalSincTrialAperture d.separation)
      state.selection.eta state.selection.cutoff) :
    Step123NativeOutput β σ d.separation := by
  have hfour : 4 < fixedOriginalSincTrialAperture d.separation :=
    (le_max_right R 4).trans_lt d.late
  refine {
    aperture_pos := d.aperture_pos
    aperture_gt_four := hfour
    original_depth := d.original_depth
    retained := Step123NativeCorePacket.ofState σ state
    detector_source_eq := ?_
    source_selector := hsel
    smoothOriginal := OriginalNativeExteriorRecord.fromOriginalSource
      (nativeOriginalDetectorPhaseSign σ) d.separation d.aperture_pos
    smoothOriginal_eq := rfl
  }
  exact hdet

/-- View 1: original physical two-lobe detector, NOT the selected ground. -/
def Step123NativeOutput.originalTrial
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) : ℝ → ℂ :=
  fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a

/-- View 2: the separately selected native spectral state at lambda. -/
def Step123NativeOutput.selectedGround
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    nativePoleNeutralParitySpace o.retained.state.selectedParity
      (fixedOriginalSincTrialAperture a)
      o.retained.state.selection.cutoff :=
  o.retained.state.selectedGround

/-- View 3: the original, generally nonzero physical interior and two
exterior restrictions, not a finite ground's fictitious contact. -/
def Step123NativeOutput.originalExteriorView
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    OriginalNativeExteriorRecord (nativeOriginalDetectorPhaseSign σ) a
      o.aperture_pos :=
  o.smoothOriginal

/-- The genuine normalized physical L2 image of the original FINITE
detector. This is not the same as the smooth original trial. -/
def Step123NativeOutput.physicalFiniteImage
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  canonicalNativePhysicalIsometry σ o.aperture_pos
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    o.retained.state.detector

theorem Step123NativeOutput.physicalFiniteImage_unit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    ‖o.physicalFiniteImage‖ = 1 := by
  unfold Step123NativeOutput.physicalFiniteImage
  rw [(canonicalNativePhysicalIsometry σ o.aperture_pos
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).norm_map]
  exact o.retained.state.detector_unit

/-- Literal mass one of the unchanged infinite-convolution source;
not a numerical fit or a packet field asserted by the caller. -/
theorem Step123NativeOutput.originalSource_mass_one
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 :=
  universalSincSource_integral_one UniversalSinc.fixedScale_pos

/-- Actual detector retains both elementary pole neutralities. -/
theorem Step123NativeOutput.originalDetector_poles
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    canonicalPoleEvenFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        o.retained.state.detector) = 0 ∧
    canonicalPoleOddFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        o.retained.state.detector) = 0 :=
  nativePoleNeutralParityAmbient_poles σ _ _ o.retained.state.detector

/-- The original detector's full-complement Schur loss survives. -/
theorem Step123NativeOutput.originalDetector_schur_loss
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    let state := o.retained.state
    let J := nativeDetectorPredecessorEmbedding σ state.selection
    let y := isometricDetectorComplementCoordinate J state.detector
    y ≠ 0 ∧
      (inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y).re <
        -(Real.exp (β * fixedOriginalSincTrialAperture a)) / 2 := by
  have h := Step123NativeCorePacket.original_negative_schur σ o.retained
  exact ⟨h.1, h.2.2⟩

/-- The source/arithmetic view is derived from the one fixed original
prime field and its exact integer drive. It is not an arbitrary pair
of functions supplied to the output record. -/
def Step123NativeOutput.arithmeticView
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (nativeOriginalPrimeField, nativeOriginalIntegerDrive)

/-- The range/input view is the actual original Y and its own
correction.  Its stable L2 and causal assertions are separately
theorem-backed in NativeCompletedInput, not definitions of RH. -/
def Step123NativeOutput.rangeView
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (nativeCompletedInput, nativeCompletionCorrection)

/-- The structural view retains exactly the single selected state and
its full detector, forcing and exterior history. -/
def Step123NativeOutput.structuralView
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (o : Step123NativeOutput β σ a) :
    Step123NativeCorePacket σ
      (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (Real.exp (β * fixedOriginalSincTrialAperture a)) o.aperture_pos :=
  o.retained

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeOutput.physicalFiniteImage_unit
#print axioms Zeta23.CCM.Step123NativeOutput.originalSource_mass_one
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetector_poles
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetector_schur_loss
