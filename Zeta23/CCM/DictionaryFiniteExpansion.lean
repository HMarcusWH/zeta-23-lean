import Zeta23.CCM.DictionaryPoleSource
import Zeta23.CCM.DictionaryArchEntries

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-! # Finite dictionary basis expansion

Phase I of the deterministic R003 completion.  This module performs only finite
algebraic expansion of the production dictionary into the basis family and the
corresponding finite `paperFT` expansion.  No channel lift is proved here.
-/

/-- Pointwise expansion of the full finite dictionary into the centered basis
family, valid both inside and outside the physical aperture. -/
theorem dictionaryTest_eq_basis_sum
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L y : ℝ) :
    dictionaryTest N u L y =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y * u j := by
  by_cases hy : |y| ≤ L
  · rw [dictionaryTest_eq_qBasisContract_of_abs_le N u hy]
    simp only [dictionaryBasisTest, kernel, hy, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · have hylt : L < |y| := lt_of_not_ge hy
    rw [dictionaryTest_eq_zero_of_lt_abs N u L y hylt]
    simp [dictionaryBasisTest_eq_zero_of_lt_abs hylt]

/-- Every basis test is continuous for positive aperture. -/
theorem continuous_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Continuous (dictionaryBasisTest n m L) := by
  unfold dictionaryBasisTest
  exact continuous_const.mul (kernel_continuous hL n m)

/-- Every basis test has compact support in the physical aperture. -/
theorem dictionaryBasisTest_hasCompactSupport
    {L : ℝ} (n m : ℤ) :
    HasCompactSupport (dictionaryBasisTest n m L) := by
  unfold dictionaryBasisTest
  exact (kernel_hasCompactSupport n m).mul_left

/-- The topological support of the full finite dictionary is contained in the
closed aperture interval.  This is the support certificate used before the
prime channel is truncated to a finite prime-power range. -/
theorem dictionaryTest_tsupport_subset
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) :
    tsupport (dictionaryTest N u L) ⊆ Icc (-L) L := by
  exact closure_minimal (dictionaryTest_support_subset N u L) isClosed_Icc

/-- The paper Fourier transform of the finite dictionary is the finite
coefficient contraction of the basis transforms.  Only finite sums are moved
through the integral. -/
theorem paperFT_dictionaryTest_eq_basis_sum
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTest N u L) z =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) z *
          u j := by
  rw [Zeta23.paperFT_def]
  have hfun :
      (fun y : ℝ => dictionaryTest N u L y * Complex.exp (Complex.I * z * y)) =
        fun y : ℝ => ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j := by
    funext y
    rw [dictionaryTest_eq_basis_sum N u L y]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  have hint (i j : Fin (2 * N + 1)) : Integrable
      (fun y : ℝ =>
        (starRingEnd ℂ) (u i) *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
            Complex.exp (Complex.I * z * y)) * u j) := by
    have hcont : Continuous
        (fun y : ℝ =>
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j) := by
      exact (continuous_const.mul
        ((continuous_dictionaryBasisTest hL _ _).mul (by fun_prop))).mul
          continuous_const
    have hcs : HasCompactSupport
        (fun y : ℝ =>
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j) := by
      exact (((dictionaryBasisTest_hasCompactSupport
        (centeredIndex N i) (centeredIndex N j)).mul_right).mul_left).mul_right
    exact hcont.integrable_of_hasCompactSupport hcs
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C,
    Zeta23.paperFT_def]

end Zeta23.CCM
