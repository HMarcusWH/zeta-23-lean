import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.DictionaryPoleLift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB02: canonical pole-prime discrepancy

This module rewrites the exact production pole/prime cancellation in a form
adapted to the regular first-bad state retained by FB-01.  The elementary
source matrix is reused directly; no parallel energy framework is introduced.

The endpoint source atom vanishes at `ω = 0`.  The source-atom energy is smooth
in its source coordinate, which permits one integration by parts on the pole
channel and an ordinary finite fundamental-theorem rewrite on the truncated
prime channel.  The final object is the finite cumulative pole-prime
discrepancy tested against the derivative of the exact source-atom energy.

No high-order boundary-flat jet, Riesz smoothing, discrepancy sign, positivity,
negative-root exclusion, finite-to-infinite closure, or RH theorem is claimed
here.
-/

/-- Existing matrix real energy specialized to one elementary source atom. -/
def sourceAtomRealEnergy
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : ℝ :=
  matrixRealEnergy (sourceMatrix ω K) x

@[simp] theorem sourceAtomRealEnergy_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceAtomRealEnergy K x 0 = 0 := by
  simp [sourceAtomRealEnergy]

/-- Source entries are smooth in the source coordinate. -/
@[fun_prop] theorem contDiff_sourceEntry
    (n m : ℤ) :
    ContDiff ℝ ⊤ (fun ω : ℝ => sourceEntry ω n m) := by
  by_cases hnm : n = m
  · subst m
    simp only [sourceEntry_self]
    unfold sourceDiagonal
    fun_prop
  · have heq :
        (fun ω : ℝ => sourceEntry ω n m) =
          fun ω =>
            (sourcePotential ω n - sourcePotential ω m) /
              (((n - m : ℤ) : ℂ)) := by
      funext ω
      exact sourceEntry_of_ne ω hnm
    rw [heq]
    unfold sourcePotential
    fun_prop

/-- The elementary source-atom real energy is `C^∞`.  This is intentionally
stronger than FB-02 needs so FB-03 can reuse the same smoothness spine for its
higher derivatives. -/
theorem contDiff_sourceAtomRealEnergy
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) := by
  unfold sourceAtomRealEnergy matrixRealEnergy quadraticForm
  simp only [sourceMatrix_apply]
  fun_prop

/-- Finite cumulative von-Mangoldt staircase on the same aperture horizon as
`canonicalPrimeMatrix`. -/
def canonicalPrimeCumulativeWeight (L t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    if Real.log q ≤ t then
      Λ q / Real.sqrt q
    else
      0

/-- Primitive whose derivative is the production pole density
`2 * cosh(t/2)`. -/
def canonicalPoleCumulativeWeight (t : ℝ) : ℝ :=
  4 * Real.sinh (t / 2)

/-- Cancellation-preserving finite pole-prime discrepancy. -/
def canonicalPolePrimeDiscrepancy (L t : ℝ) : ℝ :=
  canonicalPoleCumulativeWeight t - canonicalPrimeCumulativeWeight L t

/-- FB-02 arithmetic normal form before the remaining archimedean channels are
subtracted. -/
def canonicalPolePrimeDiscrepancyEnergy
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / L) *
    ∫ t in (0 : ℝ)..L,
      canonicalPolePrimeDiscrepancy L t *
        deriv (sourceAtomRealEnergy K x) (1 - t / L)

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiff_sourceAtomRealEnergy