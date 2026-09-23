import Zeta23.ExceptionalZero.GlobalParityBottomTerminalTarget
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# PR #247 — conditional literal Mathlib RH seam

This module intentionally remains conditional.  It verifies that the new
global-bottom arithmetic target is the only missing premise needed to reach
Mathlib's literal `RiemannHypothesis` statement through the already-proved
nontrivial-zero statement seam.

There is no theorem of type `RiemannHypothesis` without premises in this file.
`GlobalBottomArithmeticClosure` remains OPEN.
-/

/-- The explicit open global-bottom arithmetic closure would imply Mathlib's
literal Riemann Hypothesis statement.  This theorem is conditional and is not a
proof of RH. -/
theorem riemannHypothesis_of_globalBottomArithmeticClosure
    (hclose : GlobalBottomArithmeticClosure) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs :
      IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  exact criticalLine_of_globalBottomArithmeticClosure hclose s hmem

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_globalBottomArithmeticClosure
