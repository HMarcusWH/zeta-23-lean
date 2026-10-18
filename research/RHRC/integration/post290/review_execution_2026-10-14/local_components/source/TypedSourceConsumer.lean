import Zeta23.CCM.UniversalSincPhysicalBounds
import Zeta23.ExceptionalZero.UniversalSincActualVisibility
import Zeta23.CCM.FinitePhysicalNormalization
import Zeta23.CCM.OriginalDetectorPaddedFinitePhysicalUnitBridge
import Zeta23.CCM.OriginalDetectorPaddedFiniteNativeFormConcreteRate
import Zeta23.CCM.OriginalDetectorPaddedPhaseScalar
import Zeta23.CCM.OriginalDetectorOddPaddingIdentity

noncomputable section
open MeasureTheory Complex
open Zeta23.CCM Zeta23.ExceptionalZero

example {s : ℝ} (hs : 0 < s) (x : ℝ) :
    universalSincSource s x = s⁻¹ * universalSincSource 1 (x / s) :=
  universalSincSource_scale hs x

example {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (hv : v ≠ 0) :
    (∫ x : ℝ, ‖finitePhysicalSynthesis L K (finiteNormalizedCoefficients v) x‖ ^ 2) = 1 :=
  finitePhysicalSynthesis_normalized_energy hL K v hv

example (σ a : ℝ) (hL : 0 < fixedOriginalSincTrialAperture a) :
    originalDetectorPaddedFinitePhysicalUnit σ a hL =
      finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
          fixedOriginalSincLobeCenter hL) := by
  simpa only [finitePhysicalSynthesis] using
    originalDetectorPaddedFinitePhysicalUnit_eq_native_image σ a hL

example {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (L c : ℝ) (hL : 0 < L)
    (hv : originalDetectorPaddedFinitePhaseVector σ L c hL ≠ 0) :
    0 < originalDetectorPaddedPhaseNu L c hL + σ * originalDetectorPaddedPhaseOmega L c hL :=
  originalDetectorPaddedPhase_denominator_pos hσ L c hL hv

example (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith) =
      originalDetectorFinitePhaseUnitVector (-1) L c (by linarith) :=
  originalDetectorOddPadding_unitVector_eq c hL

#check universalSincPoleKilled_visible_at_offLine_zero
#check originalDetectorPaddedFinitePhysicalUnit_common_error_rates
#check originalDetectorPaddedPhase_scalar_quotient
#print axioms universalSincPoleKilled_visible_at_offLine_zero
#print axioms originalDetectorPaddedFinitePhysicalUnit_common_error_rates
#print axioms originalDetectorPaddedPhase_scalar_quotient
#print axioms originalDetectorOddPadding_normalizedPhysical_eq

