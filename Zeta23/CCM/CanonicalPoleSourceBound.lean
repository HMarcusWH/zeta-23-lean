import Mathlib.Analysis.Complex.Exponential
import Zeta23.CCM.SourceContraction
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

/-- In the frozen small-aperture range the hyperbolic weight is crudely
bounded by two.  The coarse constant is intentionally generous. -/
theorem cosh_half_le_two_of_small
    {L t : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (ht0 : 0 ≤ t) (htL : t ≤ L) :
    Real.cosh (t / 2) ≤ 2 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith
  have hxL : x ≤ (1 : ℝ) / 1024 := by
    dsimp [x]
    linarith
  have hx2 : x < 2 := by
    linarith
  have hexp :=
    Real.exp_le_two_add_div_two_sub hx0 hx2
  have hden : 0 < 2 - x := by linarith
  have hratio : (2 + x) / (2 - x) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hden]
    linarith
  have hexp2 : Real.exp x ≤ (2 : ℝ) :=
    le_trans hexp hratio
  have hexpneg : Real.exp (-x) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.cosh_eq]
  nlinarith

/-- A proved source-contraction bound yields a coarse but uniform pole bound
linear in the aperture.  This is enough for the tiny positive-base regime and
avoids the harder cubic pole estimate. -/
theorem canonicalPoleEnergy_ge_neg_eight_mul_L_of_sourceContraction
    (hsrc : SourceContractionBound)
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    -(8 * L) * ‖x‖ ^ 2 ≤
      matrixRealEnergy (canonicalPoleMatrix L K) x := by
  rw [matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom hL K x]
  have hconst : IntervalIntegrable
      (fun _ : ℝ => -(8 * ‖x‖ ^ 2)) volume 0 L :=
    continuous_const.intervalIntegrable 0 L
  have hintegrand : IntervalIntegrable
      (fun t : ℝ =>
        2 * Real.cosh (t / 2) *
          sourceAtomRealEnergy K x (1 - t / L))
      volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono :
      (∫ _t in (0 : ℝ)..L, -(8 * ‖x‖ ^ 2)) ≤
        ∫ t in (0 : ℝ)..L,
          2 * Real.cosh (t / 2) *
            sourceAtomRealEnergy K x (1 - t / L) := by
    exact intervalIntegral.integral_mono_on hL.le hconst hintegrand fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have htL : t ≤ L := ht.2
      have hfrac0 : 0 ≤ t / L := div_nonneg ht0 hL.le
      have hfrac1 : t / L ≤ 1 := (div_le_one hL).2 htL
      have hω0 : 0 ≤ 1 - t / L := sub_nonneg.mpr hfrac1
      have hω1 : 1 - t / L ≤ 1 := by linarith
      have habs := hsrc K (1 - t / L) hω0 hω1 x
      have hlow :
          -(2 * ‖x‖ ^ 2) ≤
            sourceAtomRealEnergy K x (1 - t / L) := by
        unfold sourceAtomRealEnergy
        exact neg_le_of_abs_le habs
      have hc0 : 0 ≤ Real.cosh (t / 2) := by positivity
      have hc2 : Real.cosh (t / 2) ≤ 2 :=
        cosh_half_le_two_of_small hL hsmall ht0 htL
      have hw : 0 ≤ 2 * Real.cosh (t / 2) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlow hw
      have hnorm : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
      nlinarith
  convert hmono using 1 <;> ring

/-- Coarse small-aperture pole lower bound used by the closure campaign. -/
def CanonicalPoleSmallApertureLowerBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      -(1 / 64 : ℝ) * ‖x‖ ^ 2 ≤
        matrixRealEnergy (canonicalPoleMatrix L K) x

theorem canonicalPoleSmallApertureLowerBound_of_sourceContraction
    (hsrc : SourceContractionBound) :
    CanonicalPoleSmallApertureLowerBound := by
  intro L hL hsmall K x
  have hpole :=
    canonicalPoleEnergy_ge_neg_eight_mul_L_of_sourceContraction
      hsrc hL hsmall K x
  have hnorm : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hcoef : 8 * L ≤ (1 : ℝ) / 64 := by
    linarith
  have hleft :
      -(1 / 64 : ℝ) * ‖x‖ ^ 2 ≤ -(8 * L) * ‖x‖ ^ 2 := by
    nlinarith
  exact le_trans hleft hpole

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPoleEnergy_lower_of_sourceContraction
#print axioms Zeta23.CCM.cosh_half_le_two_of_small
#print axioms Zeta23.CCM.canonicalPoleEnergy_ge_neg_eight_mul_L_of_sourceContraction
#print axioms Zeta23.CCM.canonicalPoleSmallApertureLowerBound_of_sourceContraction
