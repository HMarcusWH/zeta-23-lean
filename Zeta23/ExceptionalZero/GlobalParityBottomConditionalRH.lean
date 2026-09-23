import Zeta23.ExceptionalZero.GlobalParityBottomArithmeticEquivalenceAudit

noncomputable section

namespace Zeta23.ExceptionalZero

/-!
# PR #247 — audit-only conditional RH seam

This compatibility module is not imported by the active #247 route.  It
records only the already-audited fact that the historical universal arithmetic
closure would imply RH.  The active route stops earlier at
`GlobalBottomArithmeticResidual`.
-/

theorem riemannHypothesis_of_legacyGlobalBottomArithmeticClosure
    (hclose : LegacyGlobalBottomArithmeticClosure) :
    RiemannHypothesis :=
  legacyGlobalBottomArithmeticClosure_iff_riemannHypothesis.mp hclose

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_legacyGlobalBottomArithmeticClosure
