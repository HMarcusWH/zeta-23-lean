import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra

/-- The exact cost used at each eligible native observation. -/
theorem opposed_eq_charge_minus_discrepancy (e o : ℝ) :
    4 * max e 0 * max (-o) 0 = max ((max (e-o) 0)^2 - (e+o)^2) 0 := by
  rcases le_total 0 e with he | he <;> rcases le_total o 0 with ho | ho
  · rw [max_eq_left he, max_eq_left (neg_nonneg.mpr ho),
        max_eq_left (sub_nonneg.mpr (ho.trans he)), max_eq_left]
    · ring
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos he ho]
  · rw [max_eq_left he, max_eq_right (neg_nonpos.mpr ho), mul_zero]
    rcases le_total o e with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right]
      nlinarith [mul_nonneg he ho]
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right]
      nlinarith [sq_nonneg (e+o)]
  · rw [max_eq_right he, mul_zero, zero_mul]
    rcases le_total o e with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right]
      nlinarith [mul_nonneg_of_nonpos_of_nonpos he ho]
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right]
      nlinarith [sq_nonneg (e+o)]
  · rw [max_eq_right he, mul_zero, zero_mul, max_eq_right (sub_nonpos.mpr (he.trans ho)),
        max_eq_right]
    nlinarith [sq_nonneg (e+o)]

inductive Charges where
  | leaf (charge : ℤ)
  | fork (left right : Charges)

def Charges.total : Charges → ℤ
  | .leaf z => z
  | .fork l r => l.total + r.total

/-- There is one branch on which every charge meets its depth-dependent threshold. -/
def Charges.highBranch (b : ℤ) (k : ℕ) : Charges → Prop
  | .leaf z => b ≤ (2:ℤ)^k * z
  | .fork l r => b ≤ (2:ℤ)^k * (l.total + r.total) ∧
      (l.highBranch b (k+1) ∨ r.highBranch b (k+1))

theorem Charges.branch_of_total (t : Charges) (b : ℤ) (k : ℕ)
    (h : b ≤ (2:ℤ)^k * t.total) : t.highBranch b k := by
  induction t generalizing k with
  | leaf z => exact h
  | fork l r ihl ihr =>
    refine ⟨h, ?_⟩
    change b ≤ (2:ℤ)^k * (l.total + r.total) at h
    rcases le_total l.total r.total with hle | hle
    · right
      apply ihr
      rw [pow_succ]
      nlinarith [mul_nonneg (show (0:ℤ) ≤ 2^k by positivity) (sub_nonneg.mpr hle)]
    · left
      apply ihl
      rw [pow_succ]
      nlinarith [mul_nonneg (show (0:ℤ) ≤ 2^k by positivity) (sub_nonneg.mpr hle)]

inductive Observations where
  | leaf (cost : ℝ)
  | fork (cost : ℝ) (left right : Observations)

/-- The largest minimum along a branch, with stopping available after delay k. -/
noncomputable def Observations.value : Observations → ℕ → ℝ
  | .leaf v, _ => v
  | .fork v l r, 0 => min v (max (l.value 0) (r.value 0))
  | .fork _ l r, k+1 => max (l.value k) (r.value k)

/-- A complete cover either takes the current eligible cell or covers both children. -/
def Observations.canCover (limit : ℝ) : Observations → ℕ → Prop
  | .leaf v, _ => v ≤ limit
  | .fork v l r, 0 => v ≤ limit ∨ (l.canCover limit 0 ∧ r.canCover limit 0)
  | .fork _ l r, k+1 => l.canCover limit k ∧ r.canCover limit k

def Observations.hasHighPath (limit : ℝ) : Observations → ℕ → Prop
  | .leaf v, _ => limit < v
  | .fork v l r, 0 => limit < v ∧ (l.hasHighPath limit 0 ∨ r.hasHighPath limit 0)
  | .fork _ l r, k+1 => l.hasHighPath limit k ∨ r.hasHighPath limit k

theorem Observations.value_le_iff_cover (t : Observations) (limit : ℝ) (k : ℕ) :
    t.value k ≤ limit ↔ t.canCover limit k := by
  induction t generalizing k with
  | leaf v => rfl
  | fork v l r ihl ihr =>
    cases k <;> simp only [value, canCover, min_le_iff, max_le_iff, ihl, ihr]

theorem Observations.lt_value_iff_highPath (t : Observations) (limit : ℝ) (k : ℕ) :
    limit < t.value k ↔ t.hasHighPath limit k := by
  induction t generalizing k with
  | leaf v => rfl
  | fork v l r ihl ihr =>
    cases k <;> simp only [value, hasHighPath, lt_min_iff, lt_max_iff, ihl, ihr]

theorem Observations.no_cover_iff_highPath (t : Observations) (limit : ℝ) (k : ℕ) :
    ¬ t.canCover limit k ↔ t.hasHighPath limit k := by
  rw [← t.value_le_iff_cover, not_le, t.lt_value_iff_highPath]

end Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra
