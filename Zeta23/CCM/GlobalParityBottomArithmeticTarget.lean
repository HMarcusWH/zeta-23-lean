import Zeta23.CCM.GlobalParityBottomPrimeRemainder

noncomputable section

namespace Zeta23.CCM

/-!
# PR #247 — explicit RH-strength arithmetic target

PR #246 identified the exact prime-remainder dominance equivalent to
nonnegativity of the complete source energy.  A global-bottom residual state
carries a concrete negative-energy zero-shift witness, so it carries the exact
strict failure of that dominance.

This file names the remaining arithmetic closure proposition instead of hiding
it behind a generic "final gate".  The proposition is OPEN here.  Proving it
unconditionally for every residual state would immediately exclude every
residual state and is therefore RH-strength once composed with the generated
off-line-zero route.
-/

/-- Prime-remainder dominance specialized to the exact zero-shift witness
carried by one global-bottom residual state. -/
def GlobalBottomResidualPrimeDominance
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) : Prop :=
  canonicalPrimeFreeBudget
      s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      s.zeroShiftWitness ≤
    -canonicalPrimeRemainderEnergy
      s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      s.zeroShiftWitness

/-- Every actual residual state violates its specialized prime-remainder
dominance, exactly because its aligned zero-shift witness has negative channel
energy. -/
theorem GlobalBottomResidualState.not_primeDominance
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    ¬ GlobalBottomResidualPrimeDominance s := by
  intro hdom
  have hfail := s.zeroShift_primeRemainder_failure
  exact (not_lt_of_ge hdom) hfail

/-- Explicit open arithmetic closure target.

No theorem proving this proposition is supplied in PR #247 at this stage. -/
def GlobalBottomArithmeticClosure : Prop :=
  ∀ Q : ℕ, ∀ s : GlobalBottomResidualState Q,
    GlobalBottomResidualPrimeDominance s

/-- The open arithmetic closure target would exclude every residual state. -/
theorem residual_exclusion_of_globalBottomArithmeticClosure
    (hclose : GlobalBottomArithmeticClosure) :
    ∀ Q : ℕ, ∀ s : GlobalBottomResidualState Q, False := by
  intro Q s
  exact s.not_primeDominance (hclose Q s)

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualPrimeDominance
#print axioms Zeta23.CCM.GlobalBottomResidualState.not_primeDominance
#print axioms Zeta23.CCM.GlobalBottomArithmeticClosure
#print axioms Zeta23.CCM.residual_exclusion_of_globalBottomArithmeticClosure
