import Zeta23.CCM.GlobalParityBottomPrimeWeight

noncomputable section

namespace Zeta23.CCM

/-!
# PR #247 — concrete branch-constrained arithmetic residual

This file deliberately does not introduce another universal closure gate.
Instead it packages exactly the object any future arithmetic theorem must
exclude: a globally aligned residual state, its strengthened branch package,
and the strict #246 prime-remainder failure on the same true ground vector.

The next missing theorem must be a specific unconditional arithmetic property
of this constrained weight.  No such property is assumed here.
-/

/-- Concrete arithmetic state left by the current reduction. -/
structure GlobalBottomArithmeticResidual (Q : ℕ) where
  state : GlobalBottomResidualState Q
  branchPackage : GlobalBottomBranchPackage state
  primeFailure :
    -canonicalPrimeRemainderEnergy
        state.aligned.firstBad.L
        (state.aligned.firstBad.Nstar + 1)
        (state.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (state.aligned.firstBad.Nstar + 1) + 1))) <
      canonicalPrimeFreeBudget
        state.aligned.firstBad.L
        (state.aligned.firstBad.Nstar + 1)
        (state.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (state.aligned.firstBad.Nstar + 1) + 1)))

/-- Every globally aligned residual state canonically produces the concrete
arithmetic residual. -/
theorem GlobalBottomResidualState.exists_arithmeticResidual
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    Nonempty (GlobalBottomArithmeticResidual Q) := by
  obtain ⟨pkg⟩ := s.exists_branchPackage
  exact ⟨{
    state := s
    branchPackage := pkg
    primeFailure := s.groundTrial_primeRemainder_failure
  }⟩

/-- The arithmetic residual exposes the same exact prime-weight integral; this
is a projection, not a new estimate. -/
theorem GlobalBottomArithmeticResidual.primeFailure_integral_form
    {Q : ℕ} (a : GlobalBottomArithmeticResidual Q) :
    -((1 / a.state.aligned.firstBad.L) *
        ∫ t in (0 : ℝ)..a.state.aligned.firstBad.L,
          weightedVonMangoldtSqrtRemainder (Real.exp t) *
            a.state.primeTestWeight t) <
      canonicalPrimeFreeBudget
        a.state.aligned.firstBad.L
        (a.state.aligned.firstBad.Nstar + 1)
        (a.state.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (a.state.aligned.firstBad.Nstar + 1) + 1))) := by
  rw [← a.state.primeRemainderEnergy_eq_weight_integral]
  exact a.primeFailure

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomArithmeticResidual
#print axioms Zeta23.CCM.GlobalBottomResidualState.exists_arithmeticResidual
#print axioms Zeta23.CCM.GlobalBottomArithmeticResidual.primeFailure_integral_form
