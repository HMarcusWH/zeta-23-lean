import Zeta23.CCM.GlobalParityBottomPrimeRemainder
import Zeta23.CCM.GlobalParityBottomBranchPackage
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# PR #247 — branch-constrained global-ground prime weight

The #246 remainder is tested against the derivative of the source-atom energy
of the true global-ground trial.  Branch geometry is carried separately by
`GlobalBottomBranchPackage` and is attached to the arithmetic residual in the
next layer.
-/

/-- Exact derivative weight seen by the prime remainder on the true ground. -/
def GlobalBottomResidualState.primeTestWeight
    {Q : ℕ} (s : GlobalBottomResidualState Q) (t : ℝ) : ℝ :=
  deriv
    (sourceAtomRealEnergy
      (s.aligned.firstBad.Nstar + 1)
      (s.groundTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))))
    (1 - t / s.aligned.firstBad.L)

/-- The true-ground prime-test weight is continuous. -/
theorem GlobalBottomResidualState.continuous_primeTestWeight
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    Continuous s.primeTestWeight := by
  have hsmooth :
      ContDiff ℝ ⊤
        (sourceAtomRealEnergy
          (s.aligned.firstBad.Nstar + 1)
          (s.groundTrial : EuclideanSpace ℂ
            (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))) :=
    contDiff_sourceAtomRealEnergy
      (s.aligned.firstBad.Nstar + 1)
      (s.groundTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))
  have hd := hsmooth.continuous_deriv (by simp)
  simpa [GlobalBottomResidualState.primeTestWeight] using
    hd.comp
      (continuous_const.sub
        (continuous_id.div_const s.aligned.firstBad.L))

/-- Exact prime-remainder pairing against the named true-ground weight. -/
theorem GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    canonicalPrimeRemainderEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
      (1 / s.aligned.firstBad.L) *
        ∫ t in (0 : ℝ)..s.aligned.firstBad.L,
          weightedVonMangoldtSqrtRemainder (Real.exp t) *
            s.primeTestWeight t := by
  rfl

/-- The true ground remains in the selected parity boundary-flat carrier. -/
theorem GlobalBottomResidualState.groundTrial_mem_boundaryFlat
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    (s.groundTrial : EuclideanSpace ℂ
      (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) ∈
      euclideanParityBoundaryFlatSubspace
        s.aligned.firstBad.p
        (s.aligned.firstBad.Nstar + 1) := by
  exact s.groundTrial.property

/-- The primitive source-atom energy of the ground vector vanishes at omega=0. -/
theorem GlobalBottomResidualState.ground_sourceAtomEnergy_zero
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    sourceAtomRealEnergy
        (s.aligned.firstBad.Nstar + 1)
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) 0 = 0 := by
  exact sourceAtomRealEnergy_zero
    (s.aligned.firstBad.Nstar + 1)
    (s.groundTrial : EuclideanSpace ℂ
      (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.continuous_primeTestWeight
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_mem_boundaryFlat
#print axioms Zeta23.CCM.GlobalBottomResidualState.ground_sourceAtomEnergy_zero
