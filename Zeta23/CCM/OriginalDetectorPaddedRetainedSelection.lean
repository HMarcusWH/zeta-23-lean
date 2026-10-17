import Zeta23.CCM.OriginalDetectorAdmissibleSelector
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeProducer
import Zeta23.CCM.DetectorRetainedSchurState

/-!
Each requested source phase separately produces a cofinally late padded
native detector and its actual retained state. Both source phases are
normalized beyond one uniform threshold at the chosen aperture. A common
deep aperture is not required. The original detector remains equal to the
literal source vector; no source properties are assigned to its ground.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def nativeOriginalDetectorPhaseSign (sigma : ReversalParity) : ℝ :=
  match sigma with
  | .even => 1
  | .odd => -1

def nativeOriginalDetectorPaddedUnit (sigma : ReversalParity) (c : ℝ)
    {L : ℝ} (hL : 2 ≤ L) :
    nativePoleNeutralParitySpace sigma L (originalDetectorQuarticCutoff L) := by
  cases sigma
  · exact originalDetectorPaddedFiniteEvenPhaseUnit c hL
  · exact originalDetectorPaddedFiniteOddPhaseUnit c hL

theorem exists_nativeOriginalDetectorPaddedUnit_depth (sigma : ReversalParity)
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorPaddedFinitePhaseData β (nativeOriginalDetectorPhaseSign sigma) R,
      ‖nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture‖ = 1 ∧
      (inner ℂ (nativePoleNeutralParityCanonical sigma
        (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture))
        (nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture d.separation) := by
  cases sigma
  · exact exists_originalDetectorPaddedFiniteEvenPhase_native_depth ρ hβ hβρ R
  · exact exists_originalDetectorPaddedFiniteOddPhase_native_depth ρ hβ hβρ R

def OriginalDetectorPaddedFinitePhaseData.at_lower_threshold {β σ R R' : ℝ}
    (d : OriginalDetectorPaddedFinitePhaseData β σ R') (hR : R ≤ R') :
    OriginalDetectorPaddedFinitePhaseData β σ R where
  separation := d.separation
  aperture_pos := d.aperture_pos
  separation_gt_scale := d.separation_gt_scale
  late := (max_le_max_right 4 hR).trans_lt d.late
  image_threshold_paid := d.image_threshold_paid
  unit := d.unit
  depth := d.depth
  original_depth := d.original_depth

private theorem padded_quartic_cutoff_nonempty {L : ℝ} (hL : 2 ≤ L) :
    3 ≤ originalDetectorQuarticCutoff L := by
  have hsq : 4 ≤ L ^ 2 := by nlinarith
  have hfour : (3 : ℝ) ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 4)]
  have hc : L ^ 4 ≤ (Nat.ceil (L ^ 4) : ℝ) := Nat.le_ceil _
  exact_mod_cast hfour.trans hc

/-- No detector, ground, inverse, normalization, selector, or deep source
premise is supplied. The off-line zero produces the requested actual phase,
with both phase normalizations and the phase-independent native selector. -/
theorem exists_originalDetectorPaddedPhase_admissible_retained_state
    (sigma : ReversalParity) (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorPaddedFinitePhaseData β (nativeOriginalDetectorPhaseSign sigma) R,
      ∃ state : DetectorRetainedSchurState sigma
        (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (Real.exp (β * fixedOriginalSincTrialAperture d.separation)) d.aperture_pos,
        state.detector = nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter
          d.two_le_aperture ∧
        AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture d.separation)
          state.selection.eta state.selection.cutoff := by
  obtain ⟨Lu, hLu, hunit⟩ := exists_originalDetectorPaddedFinitePhase_unit_threshold
  obtain ⟨d0, hdunit, hddepth⟩ := exists_nativeOriginalDetectorPaddedUnit_depth
    sigma ρ hβ hβρ (max R Lu)
  let d := d0.at_lower_threshold (le_max_left R Lu)
  let L := fixedOriginalSincTrialAperture d.separation
  have hlarge : 4 < L := (le_max_right R 4).trans_lt d.late
  have hLuL : Lu ≤ L :=
    (le_max_right R Lu).trans ((le_max_left (max R Lu) 4).trans d0.late.le)
  have he := hunit 1 d.separation (Or.inl rfl) d.separation_gt_scale d.aperture_pos hLuL
  have ho := hunit (-1) d.separation (Or.inr rfl) d.separation_gt_scale d.aperture_pos hLuL
  have hKd : 3 ≤ originalDetectorQuarticCutoff L := padded_quartic_cutoff_nonempty d.two_le_aperture
  have hpUnit : ‖nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter
      d.two_le_aperture‖ = 1 := hdunit
  have hpDepth : (inner ℂ (nativePoleNeutralParityCanonical sigma L (originalDetectorQuarticCutoff L)
      (nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture))
      (nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
        -Real.exp (β * L) := hddepth
  obtain ⟨state, hstate⟩ := exists_detectorRetainedSchurState_of_original_native_trial sigma
    d.aperture_pos (originalDetectorQuarticCutoff L) hKd (Real.exp (β * L)) (Real.exp_pos _)
    (nativeOriginalDetectorPaddedUnit sigma fixedOriginalSincLobeCenter d.two_le_aperture) hpUnit hpDepth
  refine ⟨d, state, hstate, ?_⟩
  exact admissibleDetectorSelector_of_actual_ground hlarge he.1 ho.1 he.2 ho.2 state.selection

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_nativeOriginalDetectorPaddedUnit_depth
#print axioms Zeta23.CCM.exists_originalDetectorPaddedPhase_admissible_retained_state
