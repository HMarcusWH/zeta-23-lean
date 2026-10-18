import Zeta23.CCM.FinitePhysicalNormalization
import Zeta23.CCM.OriginalDetectorPaddedFiniteNormalizedErrors

/-! Literal padded instantiation of the separately proved generic normalization. -/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

theorem originalDetectorPaddedFinitePhysicalUnit_eq_native_image
    (σ a : ℝ) (hL : 0 < fixedOriginalSincTrialAperture a) :
    originalDetectorPaddedFinitePhysicalUnit σ a hL =
      localizedFiniteVector (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff
          (fixedOriginalSincTrialAperture a) + 1)) ℂ)
          (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
            fixedOriginalSincLobeCenter hL)) := by
  unfold originalDetectorPaddedFinitePhysicalUnit originalDetectorPaddedFinitePhysicalNorm
    originalDetectorPaddedFiniteOriginalPhaseHard originalDetectorPaddedFinitePhaseUnitVector
  simp only [← Complex.ofReal_inv]
  simpa only [finitePhysicalSynthesis, finiteNormalizedCoefficients] using
    finitePhysicalSynthesis_cancel_original_normalization (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      fixedOriginalSincTrialNormalization fixedOriginalSincTrialNormalization_pos
      (originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a)
        fixedOriginalSincLobeCenter hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_eq_native_image
