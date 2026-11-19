import Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost

open Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea

noncomputable section

def cost (n : ℕ) : ℝ := ∑ q ∈ n.primeFactors, (q : ℝ) * Real.log q

def integerScore (n : ℕ) : ℝ := (Real.log n) ^ 2 / 2 - cost n + 2

private def atom (x : ℝ) (q : ℕ) : ℝ := (x - q) * Real.log q

/-- The product of distinct prime factors accounts for the full mass of a squarefree integer. -/
theorem log_eq_sum_primeFactors {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ q ∈ n.primeFactors, Real.log q := by
  calc
    Real.log n = Real.log ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) := by
      rw [Nat.prod_primeFactors_of_squarefree hn]
    _ = _ := by
      rw [Nat.cast_prod, Real.log_prod]
      intro q hq
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero

private theorem ramp_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    rampArea x = (∑ q ∈ Nat.primesLE ⌊x⌋₊, atom x q) - (x ^ 2 - 4) / 2 := by
  unfold rampArea
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqx : (q : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (Nat.mem_primesLE.mp hq).1
  simp only [atom, max_eq_left (sub_nonneg.mpr hqx)]

private theorem factor_sum {n : ℕ} (hn : Squarefree n) (x : ℝ) :
    (∑ q ∈ n.primeFactors, atom x q) = x * Real.log n - cost n := by
  rw [log_eq_sum_primeFactors hn, cost, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun q _ ↦ sub_mul x (q : ℝ) (Real.log q))

/-- The exact cost of missing low primes and including high primes, at any comparison location. -/
theorem mismatch_identity {n : ℕ} (hn : Squarefree n) {x : ℝ} (hx : 0 ≤ x) :
    rampArea x - integerScore n + (x - Real.log n) ^ 2 / 2 =
      (∑ q ∈ Nat.primesLE ⌊x⌋₊ \ n.primeFactors, (x - q) * Real.log q) +
      ∑ q ∈ n.primeFactors \ Nat.primesLE ⌊x⌋₊, ((q : ℝ) - x) * Real.log q := by
  let s := n.primeFactors
  let t := Nat.primesLE ⌊x⌋₊
  have hs := Finset.sum_inter_add_sum_sdiff s t (atom x)
  have ht := Finset.sum_inter_add_sum_sdiff t s (atom x)
  rw [Finset.inter_comm t s] at ht
  have flipped : (∑ q ∈ s \ t, ((q : ℝ) - x) * Real.log q) =
      -(∑ q ∈ s \ t, atom x q) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    unfold atom
    ring
  change _ = (∑ q ∈ t \ s, atom x q) + ∑ q ∈ s \ t, ((q : ℝ) - x) * Real.log q
  rw [flipped, ramp_eq_sum hx, integerScore]
  change (∑ q ∈ t, atom x q) - (x ^ 2 - 4) / 2 -
    ((Real.log n) ^ 2 / 2 - cost n + 2) + (x - Real.log n) ^ 2 / 2 = _
  have hsum : (∑ q ∈ s, atom x q) = x * Real.log n - cost n := factor_sum hn x
  linear_combination hs - ht + hsum

/-- A squarefree integer's actual subset score never exceeds the full ramp at its log mass. -/
theorem squarefree_score_le_ramp {n : ℕ} (hn : Squarefree n) :
    integerScore n ≤ rampArea (Real.log n) := by
  let z := Real.log (n : ℝ)
  have hz : 0 ≤ z := Real.log_natCast_nonneg n
  have ident := mismatch_identity hn hz
  have missing : 0 ≤ ∑ q ∈ Nat.primesLE ⌊z⌋₊ \ n.primeFactors, (z - q) * Real.log q := by
    apply Finset.sum_nonneg
    intro q hq
    have hqx := (Nat.le_floor_iff hz).mp (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hq).1).1
    exact mul_nonneg (sub_nonneg.mpr hqx) (Real.log_natCast_nonneg q)
  have extra : 0 ≤ ∑ q ∈ n.primeFactors \ Nat.primesLE ⌊z⌋₊, ((q : ℝ) - z) * Real.log q := by
    apply Finset.sum_nonneg
    intro q hq
    obtain ⟨hm, hnot⟩ := Finset.mem_sdiff.mp hq
    have hqz : ¬ (q : ℝ) ≤ z := fun h ↦ hnot (Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff hz).mpr h, Nat.prime_of_mem_primeFactors hm⟩)
    exact mul_nonneg (sub_nonneg.mpr (lt_of_not_ge hqz).le) (Real.log_natCast_nonneg q)
  have bound := (add_nonneg missing extra)
  rw [← ident] at bound
  change integerScore n ≤ rampArea z
  change 0 ≤ rampArea z - integerScore n + (z - z) ^ 2 / 2 at bound
  simpa [sub_nonneg] using bound

/-- At a full prime prefix both mismatch sums vanish. -/
theorem primorial_recovers_ramp {x : ℝ} (hx : 0 ≤ x) :
    rampArea x = integerScore (primorial ⌊x⌋₊) - (x - Real.log (primorial ⌊x⌋₊)) ^ 2 / 2 := by
  have h := mismatch_identity (squarefree_primorial ⌊x⌋₊) hx
  rw [primeFactors_primorial] at h
  simp only [Finset.sdiff_self, Finset.sum_empty, zero_add] at h
  linarith only [h]

/-- The independent strict finite inequality on squarefree integers suffices above x = 5. -/
theorem negative_ramp_of_integer_inequality
    (h : ∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n)
    {x : ℝ} (hx : 5 ≤ x) : rampArea x < 0 := by
  have hx₀ : 0 ≤ x := by linarith
  have hfloor : 5 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx₀).mpr (by exact_mod_cast hx)
  have hsize : 8 ≤ primorial ⌊x⌋₊ :=
    le_trans (by decide : 8 ≤ primorial 5) (primorial_mono hfloor)
  have hcost := h _ hsize (squarefree_primorial ⌊x⌋₊)
  rw [primorial_recovers_ramp hx₀, integerScore]
  nlinarith only [hcost, sq_nonneg (x - Real.log (primorial ⌊x⌋₊))]

/-- The finite initial interval uses only the ordinary primes two and three. -/
theorem negative_ramp_below_five {x : ℝ} (hx : 2 < x) (h5 : x < 5) : rampArea x < 0 := by
  have hx₀ : 0 ≤ x := by linarith
  have hf : ⌊x⌋₊ ≤ 4 := by
    have h : ⌊x⌋₊ < 5 := (Nat.floor_lt hx₀).mpr (by exact_mod_cast h5)
    omega
  have hmass : (∑ q ∈ Nat.primesLE ⌊x⌋₊, Real.log q) ≤ Real.log 6 := by
    rw [← Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_log_primorial]
    apply Real.log_le_log (Nat.cast_pos.mpr (primorial_pos _))
    have hf₆ : primorial ⌊x⌋₊ ≤ 6 :=
      (primorial_mono hf).trans (by decide : primorial 4 ≤ 6)
    exact_mod_cast hf₆
  have hlog : Real.log 6 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 1 - 5 / 2), Real.exp_one_gt_d9]
  have hlinear : (∑ q ∈ Nat.primesLE ⌊x⌋₊, atom x q) ≤ (x - 2) * Real.log 6 := by
    calc
      _ ≤ ∑ q ∈ Nat.primesLE ⌊x⌋₊, (x - 2) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        have h₂ : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.mem_primesLE.mp hq).2.two_le
        exact mul_le_mul_of_nonneg_right (sub_le_sub_left h₂ x) (Real.log_natCast_nonneg q)
      _ = _ := Finset.mul_sum .. |>.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hx.le)
  rw [ramp_eq_sum hx₀]
  have hmid : Real.log 6 < (x + 2) / 2 := by linarith
  nlinarith only [hlinear, mul_lt_mul_of_pos_left hmid (sub_pos.mpr hx)]

/-- Exact equivalence between the two strict inequalities over their full stated domains. -/
theorem negative_ramp_iff_integer_inequality :
    (∀ x : ℝ, 2 < x → rampArea x < 0) ↔
    (∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n) := by
  constructor
  · intro har n hn8 hsq
    have height : (2 : ℝ) < Real.log (n : ℝ) := by
      have h8 : (2 : ℝ) < Real.log (8 : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num1
        linarith [Real.log_two_gt_d9]
      exact h8.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hn8))
    have h := (squarefree_score_le_ramp hsq).trans_lt (har _ height)
    unfold integerScore at h
    linarith
  · intro h n hn
    rcases lt_or_ge n 5 with hsmall | hlarge
    · exact negative_ramp_below_five hn hsmall
    · exact negative_ramp_of_integer_inequality h hlarge

end
end Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
