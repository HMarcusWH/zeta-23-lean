import Zeta23.CCM.GlobalParityBottomPrimeRemainder
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# PR #247 — canonical prime test weight of a residual state

The #246 prime-remainder term tests the classical weighted-Chebyshev remainder
against the derivative of an exact source-atom energy.  This module names that
weight for a global-bottom residual state and records only unconditional
structural facts.

No estimate for the weighted-Chebyshev remainder is asserted.  Any theorem
excluding all generated residual states through this weight would be RH-strength.
-/

/-- Exact derivative weight seen by the prime remainder for the aligned
zero-shift witness. -/
def GlobalBottomResidualState.primeTestWeight
    {Q : ℕ}
    (s : GlobalBottomResidualState Q)
    (t : ℝ) : ℝ :=
  deriv
    (sourceAtomRealEnergy
      (s.aligned.firstBad.Nstar + 1)
      s.zeroShiftWitness)
    (1 - t / s.aligned.firstBad.L)

/-- The residual prime-test weight is continuous. -/
theorem GlobalBottomResidualState.continuous_primeTestWeight
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    Continuous s.primeTestWeight := by
  have hsmooth :
      ContDiff ℝ ⊤
        (sourceAtomRealEnergy
          (s.aligned.firstBad.Nstar + 1)
          s.zeroShiftWitness) :=
    contDiff_sourceAtomRealEnergy
      (s.aligned.firstBad.Nstar + 1)
      s.zeroShiftWitness
  have hd := hsmooth.continuous_deriv (by simp)
  simpa [GlobalBottomResidualState.primeTestWeight] using
    hd.comp
      (continuous_const.sub
        (continuous_id.div_const s.aligned.firstBad.L))

/-- The exact prime-remainder energy is the interval pairing against the named
residual weight. -/
theorem GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    canonicalPrimeRemainderEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        s.zeroShiftWitness =
      (1 / s.aligned.firstBad.L) *
        ∫ t in (0 : ℝ)..s.aligned.firstBad.L,
          weightedVonMangoldtSqrtRemainder (Real.exp t) *
            s.primeTestWeight t := by
  rfl

/-- The aligned zero-shift witness remains in its selected parity
boundary-flat carrier. -/
theorem GlobalBottomResidualState.zeroShiftWitness_mem_boundaryFlat
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    s.zeroShiftWitness ∈
      euclideanParityBoundaryFlatSubspace
        s.aligned.firstBad.p
        (s.aligned.firstBad.Nstar + 1) := by
  simpa [GlobalBottomResidualState.zeroShiftWitness] using
    (cubicZeroShiftTrialVector
      s.aligned.firstBad.p
      s.aligned.firstBad.L
      s.aligned.firstBad.Nstar
      s.aligned.x₀).property

/-- The primitive source-atom energy used by the residual weight vanishes at
the source endpoint omega=0. -/
theorem GlobalBottomResidualState.sourceAtomEnergy_zero
    {Q : ℕ}
    (s : GlobalBottomResidualState Q) :
    sourceAtomRealEnergy
        (s.aligned.firstBad.Nstar + 1)
        s.zeroShiftWitness 0 = 0 := by
  exact sourceAtomRealEnergy_zero
    (s.aligned.firstBad.Nstar + 1)
    s.zeroShiftWitness

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.continuous_primeTestWeight
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral
#print axioms Zeta23.CCM.GlobalBottomResidualState.zeroShiftWitness_mem_boundaryFlat
#print axioms Zeta23.CCM.GlobalBottomResidualState.sourceAtomEnergy_zero
