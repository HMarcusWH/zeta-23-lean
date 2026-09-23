import Zeta23.ExceptionalZero.OffLineGeneratedRetainedFamily
import Zeta23.CCM.GlobalParityBottomResidualState

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set
open Zeta23.CCM

/-!
# PR #247 — generated global-bottom residual states

There is only one mathematical state type: `GlobalBottomResidualState` in CCM.
This exceptional-zero module supplies provenance. A hypothetical off-line zeta
zero produces those residual states at arbitrarily large aperture.

No duplicate generated-state structure is maintained here.
-/

/-- A hypothetical off-line zero produces globally aligned residual states at
arbitrarily large retained apertures. -/
theorem
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GlobalBottomResidualState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  obtain ⟨s, rfl⟩ :=
    exists_globalBottomResidualState_of_wholeCell c
  exact ⟨Q, s, hlarge⟩

/-- Existential off-line-zero wrapper for the residual state. -/
theorem
    exists_arbitrarilyLarge_globalBottomResidualState_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ s : GlobalBottomResidualState Q,
        A < s.whole.retained.energy.firstBad.L := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
      ρ₀ hρ₀ A

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomResidualState_of_exists_offLine_zero
