import Zeta23.CCM.GlobalParityBottomGroundTrial
import Zeta23.CCM.CanonicalPrimeRemainder

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — prime-remainder normal form on the true global ground

The arithmetic witness is now the same globally selected cubic ground trial
that carries the #247 spectral constraints. No fallback to the historical
zero-shift witness appears in the active route.
-/

/-- Exact PR #246 consequence on the true global-ground vector. -/
theorem GlobalBottomResidualState.groundTrial_primeRemainder_failure
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    -canonicalPrimeRemainderEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) <
      canonicalPrimeFreeBudget
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) := by
  have hneg := s.groundTrial_channelEnergy_neg
  have hid :=
    canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
      s.aligned.firstBad.L_pos
      (s.aligned.firstBad.Nstar + 1)
      (s.groundTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))
  rw [hid] at hneg
  linarith

/-- Equivalent positive-sum orientation of the same exact failure. -/
theorem GlobalBottomResidualState.groundTrial_primeRemainder_plus_budget_pos
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    0 <
      canonicalPrimeRemainderEnergy
          s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1)
          (s.groundTrial : EuclideanSpace ℂ
            (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) +
        canonicalPrimeFreeBudget
          s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1)
          (s.groundTrial : EuclideanSpace ℂ
            (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) := by
  have h := s.groundTrial_primeRemainder_failure
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_primeRemainder_failure
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_primeRemainder_plus_budget_pos
