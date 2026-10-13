import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

noncomputable section

namespace Zeta23.CCM

/-!
A finite spectral separator with the exact midpoint-grid radius.

The n forbidden values can cover at most n of n+1 grid points through open
radius-g intervals, since neighboring grid points are exactly 2g apart.
The surviving point has non-strict distance at least g from every value.
Repeated forbidden values cause no difficulty; no all-eigenvalue count is
used. Native bottom instantiation belongs to the threshold module.
-/

theorem exists_finite_real_gap_selector (n : ℕ) (a b : ℝ) (hab : a < b)
    (x : Fin n → ℝ) :
    ∃ eta : ℝ, a < eta ∧ eta < b ∧
      ∀ i : Fin n, (b - a) / (2 * ((n : ℝ) + 1)) ≤ |eta - x i| := by
  classical
  let g : ℝ := (b - a) / (2 * ((n : ℝ) + 1))
  let p : Fin (n + 1) → ℝ := fun j => a + (2 * (j.val : ℝ) + 1) * g
  have hg : 0 < g := by dsimp [g]; positivity
  have hden : 2 * ((n : ℝ) + 1) ≠ 0 := by positivity
  have hw : 2 * ((n : ℝ) + 1) * g = b - a := by
    dsimp [g]
    field_simp [hden] <;> ring
  have hdomain (j : Fin (n + 1)) : a < p j ∧ p j < b := by
    have hj0 : 0 ≤ (j.val : ℝ) := by positivity
    have hjn : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hupper : (2 * (j.val : ℝ) + 1) * g ≤ (2 * (n : ℝ) + 1) * g :=
      mul_le_mul_of_nonneg_right (by linarith) hg.le
    have hlower : 0 < (2 * (j.val : ℝ) + 1) * g := mul_pos (by linarith) hg
    dsimp [p]
    constructor <;> nlinarith
  by_contra hnone
  have hcover (j : Fin (n + 1)) : ∃ i : Fin n, |p j - x i| < g := by
    by_contra hmiss
    have hall (i : Fin n) : g ≤ |p j - x i| :=
      le_of_not_gt (fun hi => hmiss ⟨i, hi⟩)
    exact hnone ⟨p j, (hdomain j).1, (hdomain j).2, hall⟩
  let f : Fin (n + 1) → Fin n := fun j => Classical.choose (hcover j)
  have hf (j : Fin (n + 1)) : |p j - x (f j)| < g := Classical.choose_spec (hcover j)
  have hinj : Function.Injective f := by
    intro j k hjk
    have hj := abs_lt.mp (hf j)
    have hk := abs_lt.mp (hf k)
    rw [hjk] at hj
    have hdist : -(2 * g) < p j - p k ∧ p j - p k < 2 * g := by
      constructor <;> linarith [hj.1, hj.2, hk.1, hk.2]
    rcases lt_trichotomy j.val k.val with hlt | heq | hgt
    · have hs : (j.val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hm := mul_le_mul_of_nonneg_right hs hg.le
      dsimp [p] at hdist
      nlinarith [hdist.1]
    · exact Fin.ext heq
    · have hs : (k.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      have hm := mul_le_mul_of_nonneg_right hs hg.le
      dsimp [p] at hdist
      nlinarith [hdist.2]
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_finite_real_gap_selector
