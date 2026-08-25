import Zeta23.CCM.DictionaryDeterministicRHS
import Zeta23.CCM.DictionaryResidualBranches

noncomputable section

namespace Zeta23.CCM

open Set
open scoped BigOperators

/-! # Scalar source tests for the finite dictionary

The production basis tests are divided differences of a single indexed source-test
family.  This factors the later pole and archimedean off-diagonal proofs through
one scalar functional evaluation per Fourier index instead of duplicating the
full two-index integral calculation.

No explicit formula or zero sum is invoked here.
-/

/-- Production-normalized physical test attached to one scalar source potential.
The clamped source coordinate automatically enforces compact support and evenness. -/
def dictionarySourceTest (n : ℤ) (L : ℝ) : ℝ → ℂ :=
  fun y => (1 / 2 : ℂ) * sourcePotential (dictionaryApertureCoord L y) n

@[simp] theorem dictionarySourceTest_neg (n : ℤ) (L y : ℝ) :
    dictionarySourceTest n L (-y) = dictionarySourceTest n L y := by
  simp [dictionarySourceTest, dictionaryApertureCoord]

/-- A scalar source test vanishes strictly outside a positive aperture. -/
theorem dictionarySourceTest_eq_zero_of_lt_abs
    {L y : ℝ} (hL : 0 < L) (hy : L < |y|) (n : ℤ) :
    dictionarySourceTest n L y = 0 := by
  unfold dictionarySourceTest
  rw [dictionaryApertureCoord_eq_zero_of_lt_abs hL hy]
  rw [sourcePotential_zero]
  simp

/-- Scalar source tests are supported in the same closed aperture as the full dictionary. -/
theorem dictionarySourceTest_support_subset
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Function.support (dictionarySourceTest n L) ⊆ Icc (-L) L := by
  intro y hy
  have habs : |y| ≤ L := by
    by_contra hnot
    have hlt : L < |y| := lt_of_not_ge hnot
    exact hy (dictionarySourceTest_eq_zero_of_lt_abs hL hlt n)
  exact abs_le.mp habs

/-- Scalar source tests have compact support. -/
theorem dictionarySourceTest_hasCompactSupport
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    HasCompactSupport (dictionarySourceTest n L) := by
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  by_contra hzero
  exact hy (dictionarySourceTest_support_subset hL n hzero)

/-- Scalar source tests are continuous; the clamp removes the aperture seam at source level. -/
theorem continuous_dictionarySourceTest
    (n : ℤ) (L : ℝ) : Continuous (dictionarySourceTest n L) := by
  unfold dictionarySourceTest sourcePotential
  fun_prop

/-- Inside a positive aperture the scalar source test is the expected truncated sine mode. -/
theorem dictionarySourceTest_eq_sine_of_abs_le
    {L y : ℝ} (hL : 0 < L) (hy : |y| ≤ L) (n : ℤ) :
    dictionarySourceTest n L y =
      ((-Real.sin (2 * Real.pi * (n : ℝ) * |y| / L) /
        (2 * Real.pi) : ℝ) : ℂ) := by
  unfold dictionarySourceTest
  rw [dictionaryApertureCoord_eq_one_sub_of_abs_le hL hy,
    sourcePotential_one_sub]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Every production basis test is exactly one half of the elementary source entry
at the clamped physical source coordinate. -/
theorem dictionaryBasisTest_eq_sourceEntry_clamped
    {L : ℝ} (hL : 0 < L) (n m : ℤ) (y : ℝ) :
    dictionaryBasisTest n m L y =
      (1 / 2 : ℂ) * sourceEntry (dictionaryApertureCoord L y) n m := by
  by_cases hy : |y| ≤ L
  · rw [dictionaryApertureCoord_eq_one_sub_of_abs_le hL hy]
    simp only [dictionaryBasisTest, kernel, hy, if_pos]
    rw [sourceEntry_one_sub_eq_qBasis n m |y| L]
  · have hlt : L < |y| := lt_of_not_ge hy
    rw [dictionaryBasisTest_eq_zero_of_lt_abs hlt,
      dictionaryApertureCoord_eq_zero_of_lt_abs hL hlt]
    simp

/-- Off the diagonal, multiplying a production basis test by its index difference
recovers the difference of the two scalar source tests. -/
theorem dictionaryBasisTest_displacement_eq_sourceTest_sub
    {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) (y : ℝ) :
    (((n - m : ℤ) : ℂ)) * dictionaryBasisTest n m L y =
      dictionarySourceTest n L y - dictionarySourceTest m L y := by
  rw [dictionaryBasisTest_eq_sourceEntry_clamped hL n m y,
    sourceEntry_of_ne _ hnm]
  unfold dictionarySourceTest
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hnmC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hnmZ
  field_simp [hnmC]

end Zeta23.CCM
