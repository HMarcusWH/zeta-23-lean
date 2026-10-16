import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseDepth

/-! # The actual even and odd native unit-depth source producers -/

noncomputable section

open Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorPaddedFiniteEvenPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L) :=
  ((‖originalDetectorPaddedFinitePhaseVector 1 L c (by linarith)‖⁻¹ : ℝ) : ℂ) •
    originalDetectorPaddedFiniteEvenPhase c hL

def originalDetectorPaddedFiniteOddPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralOddSubspace L (originalDetectorQuarticCutoff L) :=
  ((‖originalDetectorPaddedFinitePhaseVector (-1) L c (by linarith)‖⁻¹ : ℝ) : ℂ) •
    originalDetectorPaddedFiniteOddPhase c hL

theorem originalDetectorPaddedFiniteEvenPhaseUnit_ambient (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ((originalDetectorPaddedFiniteEvenPhaseUnit c hL).val.val : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff L + 1))) =
      originalDetectorPaddedFinitePhaseUnitVector 1 L c (by linarith) := rfl

theorem originalDetectorPaddedFiniteOddPhaseUnit_ambient (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ((originalDetectorPaddedFiniteOddPhaseUnit c hL).val.val : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff L + 1))) =
      originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith) := rfl

theorem norm_originalDetectorPaddedFiniteEvenPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ‖originalDetectorPaddedFiniteEvenPhaseUnit c hL‖ =
      ‖originalDetectorPaddedFinitePhaseUnitVector 1 L c (by linarith)‖ := rfl

theorem norm_originalDetectorPaddedFiniteOddPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ‖originalDetectorPaddedFiniteOddPhaseUnit c hL‖ =
      ‖originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith)‖ := rfl

theorem originalDetectorPaddedFiniteEvenPhaseUnit_energy (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    inner ℂ (poleNeutralEvenCompressedCanonical L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteEvenPhaseUnit c hL)) (originalDetectorPaddedFiniteEvenPhaseUnit c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseUnitVector 1 L c (by linarith)))
        (originalDetectorPaddedFinitePhaseUnitVector 1 L c (by linarith)) := by
  rw [inner_poleNeutralEvenCompressedCanonical_self]
  rfl

theorem originalDetectorPaddedFiniteOddPhaseUnit_energy (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    inner ℂ (poleNeutralOddCompressedCanonical L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteOddPhaseUnit c hL)) (originalDetectorPaddedFiniteOddPhaseUnit c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith)))
        (originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith)) := by
  rw [inner_poleNeutralOddCompressedCanonical_self]
  rfl

theorem OriginalDetectorPaddedFinitePhaseData.two_le_aperture {β σ R : ℝ}
    (d : OriginalDetectorPaddedFinitePhaseData β σ R) :
    2 ≤ fixedOriginalSincTrialAperture d.separation := by
  have h4 : 4 < fixedOriginalSincTrialAperture d.separation := (le_max_right R 4).trans_lt d.late
  linarith

/-- The requested even phase is constructed in the unchanged actual
native even pole-neutral carrier with its inherited metric and operator. -/
theorem exists_originalDetectorPaddedFiniteEvenPhase_native_depth
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorPaddedFinitePhaseData β 1 R,
      ‖originalDetectorPaddedFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture‖ = 1 ∧
      (inner ℂ (poleNeutralEvenCompressedCanonical (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (originalDetectorPaddedFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture))
        (originalDetectorPaddedFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture d.separation) := by
  obtain ⟨d⟩ := originalDetectorPaddedFinitePhase_producer ρ hβ hβρ (Or.inl rfl) R
  refine ⟨d, ?_, ?_⟩
  · rw [norm_originalDetectorPaddedFiniteEvenPhaseUnit]
    exact d.unit
  · rw [originalDetectorPaddedFiniteEvenPhaseUnit_energy]
    exact d.depth

/-- The requested odd phase is independently constructed at its own
cofinally late aperture, in the actual native odd pole-neutral carrier. -/
theorem exists_originalDetectorPaddedFiniteOddPhase_native_depth
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorPaddedFinitePhaseData β (-1) R,
      ‖originalDetectorPaddedFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture‖ = 1 ∧
      (inner ℂ (poleNeutralOddCompressedCanonical (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (originalDetectorPaddedFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture))
        (originalDetectorPaddedFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture d.separation) := by
  obtain ⟨d⟩ := originalDetectorPaddedFinitePhase_producer ρ hβ hβρ (Or.inr rfl) R
  refine ⟨d, ?_, ?_⟩
  · rw [norm_originalDetectorPaddedFiniteOddPhaseUnit]
    exact d.unit
  · rw [originalDetectorPaddedFiniteOddPhaseUnit_energy]
    exact d.depth

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteEvenPhaseUnit_ambient
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteOddPhaseUnit_ambient
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteEvenPhaseUnit_energy
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteOddPhaseUnit_energy
#print axioms Zeta23.CCM.exists_originalDetectorPaddedFiniteEvenPhase_native_depth
#print axioms Zeta23.CCM.exists_originalDetectorPaddedFiniteOddPhase_native_depth
