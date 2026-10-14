import Zeta23.ExceptionalZero.UniversalSincOriginalPhaseDepth

/-!
# Canonical original-source phase-depth exports

The aperture is an output of the proved fixed-source construction. Each
phase is quantified separately; no common time or all-large-aperture claim
is made. Finite transport remains a separate construction.
-/

noncomputable section

open Set MeasureTheory Complex

namespace Zeta23.ExceptionalZero

theorem originalDetectorCorrelation_pos_excursions
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    {β : ℝ} (hβ : β < |(ρ : ℂ).re - 1 / 2|) (A M : ℝ) :
    ∃ a : ℝ, A < a ∧ M * Real.exp (2 * β * a) < fixedOriginalSincCorrelationReal a :=
  (fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
    ρ hoff hβ A M).1

theorem originalDetectorCorrelation_neg_excursions
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    {β : ℝ} (hβ : β < |(ρ : ℂ).re - 1 / 2|) (A M : ℝ) :
    ∃ a : ℝ, A < a ∧ fixedOriginalSincCorrelationReal a < -(M * Real.exp (2 * β * a)) :=
  (fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
    ρ hoff hβ A M).2

/-- Genuine normalized original trials at cofinally late output apertures. -/
theorem originalDetector_eachPhase_cofinal_depth
    (ρ : zetaZeroConfig.carrier) {β σ : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (hσ : σ = 1 ∨ σ = -1) (R : ℝ) :
    ∃ L : ℝ, max R 4 < L ∧ ∃ a : ℝ, L = fixedOriginalSincTrialAperture a ∧
      tsupport (fixedOriginalSincPhaseTrial σ a) ⊆ Icc 1 (L - 1) ∧
      (∫ x : ℝ, ‖fixedOriginalSincPhaseTrial σ a x‖ ^ 2) = 1 ∧
      (CCM.localizedWeilAdditiveRHS
        (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re ≤
          -Real.exp (β * L) := by
  obtain ⟨a, ha, hs, hn, he⟩ :=
    exists_fixedOriginalSincPhaseTrial_depth_of_off_line_zero ρ hβ hβρ hσ R
  exact ⟨fixedOriginalSincTrialAperture a, ha, a, rfl, hs, hn, he⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.originalDetectorCorrelation_pos_excursions
#print axioms Zeta23.ExceptionalZero.originalDetectorCorrelation_neg_excursions
#print axioms Zeta23.ExceptionalZero.originalDetector_eachPhase_cofinal_depth
