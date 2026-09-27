import Zeta23.CCM.SourceContractionLocalized
import Zeta23.CCM.CanonicalPolePrimeDiscrepancy

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set

/-!
# Closure campaign A1: pole channel from the source-contraction bound

This module replaces a delicate entrywise pole estimate by the exact pole/source
integral already proved in the repository.  Once the elementary source atom is
uniformly bounded, the pole channel inherits a uniform lower integral bound.
No RH input and no parity restriction are used.
-/

/-- Exact coarse lower bound for the pole channel from any proved
source-contraction bound. -/
theorem canonicalPoleEnergy_lower_of_sourceContraction
    (hsrc : SourceContractionBound)
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    -(∫ t in (0 : ℝ)..L, 4 * Real.cosh (t / 2) * ‖x‖ ^ 2) ≤
      matrixRealEnergy (canonicalPoleMatrix L K) x := by
  rw [matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom hL K x]
  have hf : IntervalIntegrable
      (fun t : ℝ => -(4 * Real.cosh (t / 2) * ‖x‖ ^ 2))
      volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable
      (fun t : ℝ =>
        2 * Real.cosh (t / 2) *
          sourceAtomRealEnergy K x (1 - t / L))
      volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..L, -(4 * Real.cosh (t / 2) * ‖x‖ ^ 2)) ≤
        ∫ t in (0 : ℝ)..L,
          2 * Real.cosh (t / 2) *
            sourceAtomRealEnergy K x (1 - t / L) := by
    exact intervalIntegral.integral_mono_on hL.le hf hg fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have htL : t ≤ L := ht.2
      have hfrac0 : 0 ≤ t / L := div_nonneg ht0 hL.le
      have hfrac1 : t / L ≤ 1 := (div_le_one hL).2 htL
      have hω0 : 0 ≤ 1 - t / L := sub_nonneg.mpr hfrac1
      have hω1 : 1 - t / L ≤ 1 := by linarith
      have habs :=
        hsrc K (1 - t / L) hω0 hω1 x
      have hlow :
          -(2 * ‖x‖ ^ 2) ≤
            sourceAtomRealEnergy K x (1 - t / L) := by
        unfold sourceAtomRealEnergy
        exact neg_le_of_abs_le habs
      have hw : 0 ≤ 2 * Real.cosh (t / 2) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlow hw
      nlinarith
  simpa [intervalIntegral.integral_neg] using hmono

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPoleEnergy_lower_of_sourceContraction
