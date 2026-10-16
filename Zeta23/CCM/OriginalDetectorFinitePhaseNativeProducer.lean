import Zeta23.CCM.OriginalDetectorFinitePhaseDepth

/-! # The actual even and odd native unit-depth source producers -/

noncomputable section

open Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorFiniteEvenPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L) :=
  ((‖originalDetectorFinitePhaseVector 1 L c (by linarith)‖⁻¹ : ℝ) : ℂ) •
    originalDetectorFiniteEvenPhase c hL

def originalDetectorFiniteOddPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralOddSubspace L (originalDetectorQuarticCutoff L) :=
  ((‖originalDetectorFinitePhaseVector (-1) L c (by linarith)‖⁻¹ : ℝ) : ℂ) •
    originalDetectorFiniteOddPhase c hL

theorem originalDetectorFiniteEvenPhaseUnit_ambient (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ((originalDetectorFiniteEvenPhaseUnit c hL).val.val : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff L + 1))) =
      originalDetectorFinitePhaseUnitVector 1 L c (by linarith) := rfl

theorem originalDetectorFiniteOddPhaseUnit_ambient (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ((originalDetectorFiniteOddPhaseUnit c hL).val.val : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff L + 1))) =
      originalDetectorFinitePhaseUnitVector (-1) L c (by linarith) := rfl

theorem norm_originalDetectorFiniteEvenPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ‖originalDetectorFiniteEvenPhaseUnit c hL‖ =
      ‖originalDetectorFinitePhaseUnitVector 1 L c (by linarith)‖ := rfl

theorem norm_originalDetectorFiniteOddPhaseUnit (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ‖originalDetectorFiniteOddPhaseUnit c hL‖ =
      ‖originalDetectorFinitePhaseUnitVector (-1) L c (by linarith)‖ := rfl

theorem originalDetectorFiniteEvenPhaseUnit_energy (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    inner ℂ (poleNeutralEvenCompressedCanonical L (originalDetectorQuarticCutoff L)
      (originalDetectorFiniteEvenPhaseUnit c hL)) (originalDetectorFiniteEvenPhaseUnit c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorFinitePhaseUnitVector 1 L c (by linarith)))
        (originalDetectorFinitePhaseUnitVector 1 L c (by linarith)) := by
  rw [inner_poleNeutralEvenCompressedCanonical_self]
  rfl

theorem originalDetectorFiniteOddPhaseUnit_energy (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    inner ℂ (poleNeutralOddCompressedCanonical L (originalDetectorQuarticCutoff L)
      (originalDetectorFiniteOddPhaseUnit c hL)) (originalDetectorFiniteOddPhaseUnit c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorFinitePhaseUnitVector (-1) L c (by linarith)))
        (originalDetectorFinitePhaseUnitVector (-1) L c (by linarith)) := by
  rw [inner_poleNeutralOddCompressedCanonical_self]
  rfl

theorem OriginalDetectorFinitePhaseData.two_le_aperture {β σ R : ℝ}
    (d : OriginalDetectorFinitePhaseData β σ R) :
    2 ≤ fixedOriginalSincTrialAperture d.separation := by
  have h4 : 4 < fixedOriginalSincTrialAperture d.separation := (le_max_right R 4).trans_lt d.late
  linarith

/-- The requested even phase is constructed in the unchanged actual
native even pole-neutral carrier with its inherited metric and operator. -/
theorem exists_originalDetectorFiniteEvenPhase_native_depth
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorFinitePhaseData β 1 R,
      ‖originalDetectorFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture‖ = 1 ∧
      (inner ℂ (poleNeutralEvenCompressedCanonical (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (originalDetectorFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture))
        (originalDetectorFiniteEvenPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture d.separation) := by
  obtain ⟨d⟩ := originalDetectorFinitePhase_producer ρ hβ hβρ (Or.inl rfl) R
  refine ⟨d, ?_, ?_⟩
  · rw [norm_originalDetectorFiniteEvenPhaseUnit]
    exact d.unit
  · rw [originalDetectorFiniteEvenPhaseUnit_energy]
    exact d.depth

/-- The requested odd phase is independently constructed at its own
cofinally late aperture, in the actual native odd pole-neutral carrier. -/
theorem exists_originalDetectorFiniteOddPhase_native_depth
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorFinitePhaseData β (-1) R,
      ‖originalDetectorFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture‖ = 1 ∧
      (inner ℂ (poleNeutralOddCompressedCanonical (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (originalDetectorFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture))
        (originalDetectorFiniteOddPhaseUnit fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
          -Real.exp (β * fixedOriginalSincTrialAperture d.separation) := by
  obtain ⟨d⟩ := originalDetectorFinitePhase_producer ρ hβ hβρ (Or.inr rfl) R
  refine ⟨d, ?_, ?_⟩
  · rw [norm_originalDetectorFiniteOddPhaseUnit]
    exact d.unit
  · rw [originalDetectorFiniteOddPhaseUnit_energy]
    exact d.depth

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFiniteEvenPhaseUnit_ambient
#print axioms Zeta23.CCM.originalDetectorFiniteOddPhaseUnit_ambient
#print axioms Zeta23.CCM.originalDetectorFiniteEvenPhaseUnit_energy
#print axioms Zeta23.CCM.originalDetectorFiniteOddPhaseUnit_energy
#print axioms Zeta23.CCM.exists_originalDetectorFiniteEvenPhase_native_depth
#print axioms Zeta23.CCM.exists_originalDetectorFiniteOddPhase_native_depth
