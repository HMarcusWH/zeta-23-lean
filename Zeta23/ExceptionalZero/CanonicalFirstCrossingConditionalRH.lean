import Zeta23.ExceptionalZero.CanonicalParityFirstCrossingShell
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt
import Zeta23.CCM.CanonicalFirstCrossingBarrier

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Audit-only conditional RH seam for the post-#278 first-crossing route

This module is deliberately NOT imported by `Zeta23.ExceptionalZero`.

It proves only that the two still-OPEN production first-crossing barriers would
be sufficient, together with the already-proved counterexample generator and
Mathlib statement seam, to establish literal `RiemannHypothesis`.

The barrier premises are not proved here.  This is a strength/wiring audit.
RH remains OPEN.
-/

theorem riemannHypothesis_of_firstCrossingBarriers
    (hinterior : CanonicalInteriorFirstCrossingBarrier)
    (hseam : CanonicalSeamFirstCrossingBarrier) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs :
      IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  by_contra hoff
  have hoff' :
      ((⟨s, hmem⟩ : zetaZeroConfig.carrier) : ℂ).re ≠ 1 / 2 := by
    simpa using hoff
  obtain ⟨c⟩ :=
    nonempty_canonicalParityFirstCrossingShell_of_offLine_zero
      (⟨s, hmem⟩ : zetaZeroConfig.carrier) hoff'
  exact no_canonicalParityFirstCrossingShell_of_barriers
    hinterior hseam c

/-- Sharper audit seam: the two production scalar regular-endpoint
barriers are already sufficient for literal Mathlib RH.  These premises remain
OPEN and are not imported by the active ExceptionalZero root. -/
theorem riemannHypothesis_of_regularEndpointBarriers
    (hinterior : CanonicalInteriorRegularEndpointBarrier)
    (hseam : CanonicalSeamRegularEndpointBarrier) :
    RiemannHypothesis :=
  riemannHypothesis_of_firstCrossingBarriers
    (canonicalInteriorFirstCrossingBarrier_of_regularEndpointBarrier hinterior)
    (canonicalSeamFirstCrossingBarrier_of_regularEndpointBarrier hseam)


end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_firstCrossingBarriers
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_regularEndpointBarriers
