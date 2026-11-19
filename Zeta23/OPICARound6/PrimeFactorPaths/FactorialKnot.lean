import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot

/-- The coefficient at the actual positive integer j in the factorial filter. -/
def weight (m j : ℕ) : ℤ := if m ∣ j then 1 - (m : ℤ) else 1

/-- The finite ramp at n, with source indices j=k+1 from 1 through n. -/
def ramp (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, weight m (k+1) * ((n : ℤ) - (k+1 : ℕ))

private theorem residue_step (m n : ℕ) (hm : 0 < m) :
    (n % m + 1 = m ∧ (n+1) % m = 0) ∨
    ((n+1) % m = n % m + 1 ∧ ¬m ∣ n+1) := by
  have hstep : (n+1) % m = (n % m + 1) % m := (Nat.mod_add_mod n m 1).symm
  have hlt := Nat.mod_lt n hm
  by_cases h : n % m + 1 = m
  · exact Or.inl ⟨h, by rw [hstep, h, Nat.mod_self]⟩
  · have hs : n % m + 1 < m := by omega
    have he : (n+1) % m = n % m + 1 := hstep.trans (Nat.mod_eq_of_lt hs)
    exact Or.inr ⟨he, by intro hd; have hz := Nat.mod_eq_zero_of_dvd hd; omega⟩

theorem weight_prefix (m n : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range n, weight m (k+1)) = (n % m : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases residue_step m n hm with ⟨hw, hz⟩ | ⟨he, hd⟩
    · have hd := Nat.dvd_of_mod_eq_zero hz
      simp only [weight, if_pos hd, hz, Nat.cast_zero]
      omega
    · simp only [weight, if_neg hd, he, Nat.cast_add, Nat.cast_one]

theorem ramp_increment (m n : ℕ) (hm : 0 < m) :
    ramp m (n+1) = ramp m n + (n % m : ℕ) := by
  rw [← weight_prefix m n hm]
  unfold ramp
  rw [Finset.sum_range_succ, ← Finset.sum_add_distrib]
  simp only [sub_self, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

theorem twice_ramp_at_knot (m n : ℕ) (hm : 0 < m) :
    2 * ramp m n = ((m : ℤ)-1) * n - (n % m : ℕ) * ((m : ℤ) - (n % m : ℕ)) := by
  induction n with
  | zero => simp [ramp]
  | succ n ih =>
    rw [ramp_increment m n hm]
    rcases residue_step m n hm with ⟨hw, hz⟩ | ⟨he, _⟩
    · have hz' : ((n % m : ℕ) : ℤ) + 1 = (m : ℤ) := by exact_mod_cast hw
      rw [hz]
      simp only [Nat.cast_succ, Nat.cast_zero]
      rw [←hz'] at ih ⊢
      linear_combination ih
    · rw [he]
      simp only [Nat.cast_succ]
      linear_combination ih

theorem calibrated_residue {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (n : ℕ) (hm : ∀ i ∈ s, 0 < m i)
    (hcal : (∑ i ∈ s, a i * ((m i : ℝ) - 1)) = 2) :
    (n : ℝ) - 1 - (∑ i ∈ s, a i * (ramp (m i) n : ℝ)) =
      -1 + (1/2 : ℝ) * ∑ i ∈ s, a i * (n % m i : ℕ) * ((m i : ℝ) - (n % m i : ℕ)) := by
  have hsum :
      2 * (∑ i ∈ s, a i * (ramp (m i) n : ℝ)) =
      n * (∑ i ∈ s, a i * ((m i : ℝ) - 1)) -
      ∑ i ∈ s, a i * (n % m i : ℕ) * ((m i : ℝ) - (n % m i : ℕ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have h : (2 : ℝ) * (ramp (m i) n : ℝ) =
        ((m i : ℝ)-1) * n - (n % m i : ℕ) * ((m i : ℝ) - (n % m i : ℕ)) := by
      have hZ := congrArg (fun z : ℤ => (z : ℝ)) (twice_ramp_at_knot (m i) n (hm i hi))
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_one] using hZ
    linear_combination (a i) * h
  rw [hcal] at hsum
  linarith

end Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot
