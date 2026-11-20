import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal

/-- Abel summation from a literal signed cumulative sequence, retaining the left boundary. -/
theorem abel_history (w A : ℕ → ℝ) {r L : ℕ} (h : r < L) :
    (∑ j ∈ Finset.Ioc r L, w j * (A j - A (j - 1))) =
      w L * A L - w (r + 1) * A r -
        ∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j) * A j := by
  refine Nat.le_induction ?_ ?_ L h
  · simp [Nat.Ioc_succ_singleton, mul_sub]
  · intro n hn ih
    rw [Finset.sum_Ioc_succ_top (Nat.le_of_succ_le hn), Finset.sum_Ico_succ_top hn, ih]
    simp only [Nat.add_one_sub_one]
    ring

/-- The boundary atom and all subsequent weight differences have total mass exactly w L. -/
theorem history_weight_total (w : ℕ → ℝ) {r L : ℕ} (h : r < L) :
    w (r + 1) + (∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j)) = w L := by
  refine Nat.le_induction ?_ ?_ L h
  · simp
  · intro n hn ih
    rw [Finset.sum_Ico_succ_top hn, ← add_assoc, ih]
    ring

/-- A one-sided bound on the actual signed history suffices under the stated weight signs. -/
theorem history_upper (w A : ℕ → ℝ) (bound : ℝ) {r L : ℕ} (h : r < L)
    (hbase : 0 ≤ w (r + 1)) (hsteps : ∀ j ∈ Finset.Ico (r + 1) L, w j ≤ w (j + 1))
    (hA : ∀ j ∈ Finset.Ico r L, A j ≤ bound) :
    w (r + 1) * A r + (∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j) * A j)
      ≤ w L * bound := by
  calc
    _ ≤ w (r + 1) * bound +
        ∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j) * bound := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hA r (Finset.mem_Ico.mpr ⟨le_rfl, h⟩)) hbase
      · apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj₁, hj₂⟩ := Finset.mem_Ico.mp hj
        exact mul_le_mul_of_nonneg_left (hA j (Finset.mem_Ico.mpr ⟨by omega, hj₂⟩))
          (sub_nonneg.mpr (hsteps j hj))
    _ = w L * bound := by rw [← Finset.sum_mul, ← add_mul, history_weight_total w h]

/-- A finite positive past with a rowwise gain budget propagates a one-sided upper. -/
theorem renewal_upper (a error : ℕ → ℝ) (kernel : ℕ → ℕ → ℝ) (bound : ℝ)
    (hrec : ∀ n, a n ≤ error n + ∑ j ∈ Finset.range n, kernel n j * a j)
    (hpos : ∀ n j, j < n → 0 ≤ kernel n j)
    (hbudget : ∀ n, error n + (∑ j ∈ Finset.range n, kernel n j) * bound ≤ bound) :
    ∀ n, a n ≤ bound := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply (hrec n).trans
    calc
      _ ≤ error n + ∑ j ∈ Finset.range n, kernel n j * bound := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (ih j (Finset.mem_range.mp hj))
          (hpos n j (Finset.mem_range.mp hj))
      _ ≤ bound := by rw [← Finset.sum_mul]; exact hbudget n

end Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal
