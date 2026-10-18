import Zeta23.CCM.OriginalDetectorFinitePhaseNativeProducer
import Zeta23.CCM.DetectorRetainedSchurState

/-!
The existing literal finite source phase producers feed the actual retained
state constructor. The detector is retained by equality, separately from
the selected ground. These helpers concern the current unpadded finite
phase image; the positive padding producer remains its own obligation.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

theorem three_le_originalDetectorQuarticCutoff {L : ℝ} (hL : 2 ≤ L) :
    3 ≤ originalDetectorQuarticCutoff L := by
  have hsq : 4 ≤ L ^ 2 := by nlinarith
  have hfour : (3 : ℝ) ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 4)]
  have hc : L ^ 4 ≤ (Nat.ceil (L ^ 4) : ℝ) := Nat.le_ceil _
  exact_mod_cast hfour.trans hc

/-- The actual even source detector is the detector stored in the retained
packet; no selected-ground or inverse is supplied by the caller. -/
theorem exists_originalDetectorFiniteEvenPhase_retained_state
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorFinitePhaseData β 1 R,
      ∃ state : DetectorRetainedSchurState .even
        (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (Real.exp (β * fixedOriginalSincTrialAperture d.separation))
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) d.two_le_aperture),
        state.detector = originalDetectorFiniteEvenPhaseUnit fixedOriginalSincLobeCenter
          d.two_le_aperture := by
  obtain ⟨d, hu, hd⟩ := exists_originalDetectorFiniteEvenPhase_native_depth ρ hβ hβρ R
  let L := fixedOriginalSincTrialAperture d.separation
  let D := Real.exp (β * L)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) d.two_le_aperture
  have hKd : 3 ≤ originalDetectorQuarticCutoff L :=
    three_le_originalDetectorQuarticCutoff d.two_le_aperture
  obtain ⟨state, hs⟩ := exists_detectorRetainedSchurState_of_original_native_trial .even
    hL (originalDetectorQuarticCutoff L) hKd D (Real.exp_pos _)
    (originalDetectorFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture) hu hd
  exact ⟨d, state, hs⟩

/-- The odd phase has its own cofinal source construction and retains its
own detector, with no even choice or parity exclusion inserted. -/
theorem exists_originalDetectorFiniteOddPhase_retained_state
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorFinitePhaseData β (-1) R,
      ∃ state : DetectorRetainedSchurState .odd
        (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (Real.exp (β * fixedOriginalSincTrialAperture d.separation))
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) d.two_le_aperture),
        state.detector = originalDetectorFiniteOddPhaseUnit fixedOriginalSincLobeCenter
          d.two_le_aperture := by
  obtain ⟨d, hw, hd⟩ := exists_originalDetectorFiniteOddPhase_native_depth ρ hβ hβρ R
  let L := fixedOriginalSincTrialAperture d.separation
  let D := Real.exp (β * L)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) d.two_le_aperture
  have hKd : 3 ≤ originalDetectorQuarticCutoff L :=
    three_le_originalDetectorQuarticCutoff d.two_le_aperture
  obtain ⟨state, hs⟩ := exists_detectorRetainedSchurState_of_original_native_trial .odd
    hL (originalDetectorQuarticCutoff L) hKd D (Real.exp_pos _)
    (originalDetectorFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture) hw hd
  exact ⟨d, state, hs⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.three_le_originalDetectorQuarticCutoff
#print axioms Zeta23.CCM.exists_originalDetectorFiniteEvenPhase_retained_state
#print axioms Zeta23.CCM.exists_originalDetectorFiniteOddPhase_retained_state
