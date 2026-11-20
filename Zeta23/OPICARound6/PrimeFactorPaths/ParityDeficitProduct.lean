import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The contribution of opposite parity fluctuations to one-sided energy

The excess of one population and shortfall of the other determine the positive
signed square up to the square of their total discrepancy. All comparisons
are finite and allow arbitrary nonnegative weights on the chosen observations.
-/

namespace Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct

/-- The balanced excess and shortfall have coefficient four in the signed square. -/
theorem quadrant_remainder (e o : ℝ) :
    0 ≤ (max (e - o) 0)^2 - 4 * max e 0 * max (-o) 0 ∧
    (max (e - o) 0)^2 - 4 * max e 0 * max (-o) 0 ≤ (e + o)^2 := by
  rcases le_total 0 e with he | he
  · rcases le_total o 0 with ho | ho
    · rw [max_eq_left he, max_eq_left (neg_nonneg.mpr ho),
          max_eq_left (sub_nonneg.mpr (ho.trans he))]
      constructor <;> nlinarith [sq_nonneg (e + o)]
    · rw [max_eq_left he, max_eq_right (neg_nonpos.mpr ho)]
      rcases le_total o e with hd | hd
      · rw [max_eq_left (sub_nonneg.mpr hd)]
        constructor <;> nlinarith [mul_nonneg he ho, sq_nonneg (e - o)]
      · rw [max_eq_right (sub_nonpos.mpr hd)]
        constructor <;> nlinarith [sq_nonneg (e + o)]
  · rcases le_total 0 o with ho | ho
    · rw [max_eq_right he, max_eq_right (neg_nonpos.mpr ho),
          max_eq_right (sub_nonpos.mpr (he.trans ho))]
      constructor <;> nlinarith [sq_nonneg (e + o)]
    · rw [max_eq_right he, max_eq_left (neg_nonneg.mpr ho)]
      rcases le_total o e with hd | hd
      · rw [max_eq_left (sub_nonneg.mpr hd)]
        constructor <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos he ho, sq_nonneg (e - o)]
      · rw [max_eq_right (sub_nonpos.mpr hd)]
        constructor <;> nlinarith [sq_nonneg (e + o)]

/-- The signed-square approximation has a weighted sum of absolute errors. -/
theorem weighted_absolute_remainder {ι : Type*} (s : Finset ι) (e o w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * |(max (e i - o i) 0)^2 - 4 * max (e i) 0 * max (-o i) 0|) ≤
    ∑ i ∈ s, w i * (e i + o i)^2 := by
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hl, hu⟩ := quadrant_remainder (e i) (o i)
  rw [abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_left hu (hw i hi)

/-- The zero-total-discrepancy direction determines the coefficient uniquely. -/
theorem forced_coefficient (c : ℝ) (h : ∀ e o : ℝ,
    0 ≤ (max (e-o) 0)^2 - c * max e 0 * max (-o) 0 ∧
    (max (e-o) 0)^2 - c * max e 0 * max (-o) 0 ≤ (e+o)^2) : c = 4 := by
  have hx := h 1 (-1)
  norm_num at hx
  linarith [hx.1, hx.2]

end Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct
