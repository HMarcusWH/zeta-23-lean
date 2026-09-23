import Zeta23.ExceptionalZero.GlobalParityBottomGeneratedState
import Zeta23.CCM.GlobalParityBottomArithmeticTarget

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# PR #247 — active terminal reduction

The active route stops at a concrete `GlobalBottomArithmeticResidual`.  No
renamed universal exclusion or dominance gate is introduced here.  A future
closure must prove a specific unconditional arithmetic theorem about the
branch-constrained true-ground weight carried by this object.

RH remains OPEN.
-/

/-- A hypothetical off-line zero produces concrete branch-constrained
arithmetic residuals at arbitrarily large aperture. -/
theorem
    exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ a : GlobalBottomArithmeticResidual Q,
        A < a.state.aligned.firstBad.L := by
  obtain ⟨Q, s, hlarge⟩ :=
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
      ρ₀ hoff A
  obtain ⟨a⟩ := s.exists_arithmeticResidual
  exact ⟨Q, a, hlarge⟩

/-- Existential off-line-zero wrapper for the concrete arithmetic residual. -/
theorem
    exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ a : GlobalBottomArithmeticResidual Q,
        A < a.state.aligned.firstBad.L := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_offLine_zero
      ρ₀ hρ₀ A

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalBottomArithmeticResidual_of_exists_offLine_zero
