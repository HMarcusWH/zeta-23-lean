import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.OriginalDetectorPaddedFinitePhysicalUnitBridge
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeProducer

/-!
# Exact physical realization of the frozen padded original detector

This bridge is needed before using actual native finite and original
smooth errors in the same forcing estimate. It is NOT a numerical
approximation, selected-ground replacement or a declaration that
the smooth trial equals the finite image.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- The coefficient inclusion of the source's native parity unit vector
really is the normalized padded finite Euclidean coefficient vector. -/
theorem originalDetectorPaddedNativeUnit_eq_unitCoefficients
    (σ : ReversalParity) {L : ℝ} (hL : 2 ≤ L) (c : ℝ) :
    canonicalNativeCoefficientInclusion σ L (originalDetectorQuarticCutoff L)
      (nativeOriginalDetectorPaddedUnit σ c hL) =
    originalDetectorPaddedFinitePhaseUnitVector
      (nativeOriginalDetectorPhaseSign σ) L c (by linarith) := by
  cases σ
  · simpa only [nativeOriginalDetectorPhaseSign, nativeOriginalDetectorPaddedUnit,
      canonicalNativeCoefficientInclusion_eq_ambient] using
        (originalDetectorPaddedFiniteEvenPhaseUnit_ambient c hL)
  · simpa only [nativeOriginalDetectorPhaseSign, nativeOriginalDetectorPaddedUnit,
      canonicalNativeCoefficientInclusion_eq_ambient] using
        (originalDetectorPaddedFiniteOddPhaseUnit_ambient c hL)

/-- N13: physical synthesis of the packet's ONE original detector
equals the actual true-normalized padded physical source. -/
theorem Step123NativeOutput.finitePhysicalSource_eq_originalPadded
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    finitePhysicalSynthesis
      (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (canonicalNativeCoefficientInclusion σ
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) =
      originalDetectorPaddedFinitePhysicalUnit
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos := by
  let L := fixedOriginalSincTrialAperture a
  let c := fixedOriginalSincLobeCenter
  have h2 : 2 ≤ L := by
    dsimp [L]
    linarith [out.aperture_gt_four]
  calc
    finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
        (canonicalNativeCoefficientInclusion σ L
          (originalDetectorQuarticCutoff L) out.retained.state.detector) =
      finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
        (canonicalNativeCoefficientInclusion σ L
          (originalDetectorQuarticCutoff L) (nativeOriginalDetectorPaddedUnit σ c h2)) := by
        rw [out.detector_source_eq]
    _ = finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
        (originalDetectorPaddedFinitePhaseUnitVector
          (nativeOriginalDetectorPhaseSign σ) L c out.aperture_pos) := by
        rw [originalDetectorPaddedNativeUnit_eq_unitCoefficients σ h2 c]
    _ = originalDetectorPaddedFinitePhysicalUnit
          (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos := by
        exact (originalDetectorPaddedFinitePhysicalUnit_eq_native_image
          (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos).symm

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedNativeUnit_eq_unitCoefficients
#print axioms Zeta23.CCM.Step123NativeOutput.finitePhysicalSource_eq_originalPadded
