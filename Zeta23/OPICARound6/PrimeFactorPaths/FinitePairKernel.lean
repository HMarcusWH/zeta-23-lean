import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel

variable {ι : Type*}

theorem one_moment (s : Finset ι) (a z : ι → ℝ) (k : ℕ) :
    (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (2 * z i * z j)^k := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All ordered pairs of signed real coefficients appear, including the diagonal. -/
theorem geometric_moments (s : Finset ι) (a z : ι → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * ∑ k ∈ Finset.range N, (2 * z i * z j)^k := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, mul_add, Finset.sum_add_distrib]
    rw [ih, one_moment]

theorem geometric_remainder (x : ℝ) (N : ℕ) (hx : x ≠ 1) :
    1 / (1 - x) = (∑ k ∈ Finset.range N, x^k) + x^N / (1 - x) := by
  have hn : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  calc
    1 / (1 - x) =
        ((∑ k ∈ Finset.range N, x^k) * (1-x) + x^N) / (1-x) := by
          rw [geom_sum_mul_neg, sub_add_cancel]
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hn]

/-- The rational Gram kernel splits exactly into finite square moments and its signed tail. -/
theorem rational_pair_remainder (s : Finset ι) (a z : ι → ℝ) (N : ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, 2 * z i * z j ≠ 1) :
    (∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (1 / (1 - 2 * z i * z j))) =
      (∑ k ∈ Finset.range N, (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2) +
        ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * ((2 * z i * z j)^N / (1 - 2 * z i * z j)) := by
  rw [geometric_moments, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_add, ← geometric_remainder _ _ (h i hi j hj)]

end Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel
