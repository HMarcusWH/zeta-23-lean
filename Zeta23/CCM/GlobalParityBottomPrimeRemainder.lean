import Zeta23.CCM.GlobalParityBottomResidualState
import Zeta23.CCM.CanonicalPrimeRemainder

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — prime-remainder normal form of a global-bottom residual state

The global-bottom reduction does not make the terminal arithmetic claim weaker
than RH.  What it does provide is a highly structured canonical state.  This
module translates the already-stored negative zero-shift channel witness of
that same state into the exact PR #246 weighted-Chebyshev remainder language.

No prime-remainder sign is asserted.  No contradiction is proved.
-/

/-- Exact zero-shift witness carried by a residual state's aligned negative
energy certificate. -/
def GlobalBottomResidualState.zeroShiftWitness
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    EuclideanSpace ℂ
      (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)) :=
  (cubicZeroShiftTrialVector
    s.aligned.firstBad.p
    s.aligned.firstBad.L
    s.aligned.firstBad.Nstar
    s.aligned.x₀ :
      EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))

/-- The residual state's zero-shift witness has strictly negative complete
canonical source-channel energy. -/
theorem GlobalBottomResidualState.zeroShift_channelEnergy_neg
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    canonicalSourceChannelEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        s.zeroShiftWitness < 0 := by
  simpa [GlobalBottomResidualState.zeroShiftWitness] using
    s.aligned.channelEnergyNeg

/-- Exact classical arithmetic consequence of the stored negative-energy
witness: the prime-free budget strictly exceeds minus the weighted Chebyshev
remainder energy.  This is a normal form of badness, not a contradiction. -/
theorem GlobalBottomResidualState.zeroShift_primeRemainder_failure
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    -canonicalPrimeRemainderEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        s.zeroShiftWitness <
      canonicalPrimeFreeBudget
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        s.zeroShiftWitness := by
  have hneg := s.zeroShift_channelEnergy_neg
  have hid :=
    canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
      s.aligned.firstBad.L_pos
      (s.aligned.firstBad.Nstar + 1)
      s.zeroShiftWitness
  rw [hid] at hneg
  linarith

/-- Equivalent orientation of the same exact failure. -/
theorem GlobalBottomResidualState.primeRemainder_plus_budget_pos
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    0 <
      canonicalPrimeRemainderEnergy
          s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1)
          s.zeroShiftWitness +
        canonicalPrimeFreeBudget
          s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1)
          s.zeroShiftWitness := by
  have h := s.zeroShift_primeRemainder_failure
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.zeroShift_channelEnergy_neg
#print axioms Zeta23.CCM.GlobalBottomResidualState.zeroShift_primeRemainder_failure
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeRemainder_plus_budget_pos
