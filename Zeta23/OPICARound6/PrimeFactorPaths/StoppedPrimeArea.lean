import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea

noncomputable section

/-- First spatial moment of the ordinary-prime logarithmic weights up to and including p. -/
def weightedPosition (p : ℕ) : ℝ :=
  ∑ q ∈ Nat.primesLE p, (q : ℝ) * Real.log q

/-- The full ordinary-prime ramp at x. Every prime above x has zero ramp. -/
def rampArea (x : ℝ) : ℝ :=
  (∑ q ∈ Nat.primesLE ⌊x⌋₊, max (x - (q : ℝ)) 0 * Real.log q) - (x ^ 2 - 4) / 2

def score (p : ℕ) : ℝ := Chebyshev.theta p ^ 2 / 2 - weightedPosition p + 2

/-- The endpoints are actual ordinary primes with no intervening prime. -/
structure PrimeGap (p r : ℕ) : Prop where
  left_prime : p.Prime
  right_prime : r.Prime
  lt : p < r
  next_le : ∀ q : ℕ, q.Prime → p < q → r ≤ q

/-- All primes in the active ramp are precisely the primes up to the left endpoint. -/
theorem active_primes_in_gap {p r : ℕ} (gap : PrimeGap p r) {x : ℝ}
    (hpx : (p : ℝ) ≤ x) (hxr : x < (r : ℝ)) :
    Nat.primesLE ⌊x⌋₊ = Nat.primesLE p := by
  have hx : 0 ≤ x := (Nat.cast_nonneg p).trans hpx
  ext q
  rw [Nat.mem_primesLE, Nat.mem_primesLE, Nat.le_floor_iff hx]
  constructor
  · rintro ⟨hqx, hq⟩
    refine ⟨?_, hq⟩
    by_contra! hpq
    have hrq : (r : ℝ) ≤ q := by exact_mod_cast gap.next_le q hq hpq
    exact (not_lt_of_ge (hrq.trans hqx)) hxr
  · rintro ⟨hqp, hq⟩
    exact ⟨(Nat.cast_le.mpr hqp).trans hpx, hq⟩

/-- The score minus the squared distance is the exact finite area throughout the true gap. -/
theorem completed_square_in_gap {p r : ℕ} (gap : PrimeGap p r) {x : ℝ}
    (hpx : (p : ℝ) ≤ x) (hxr : x < (r : ℝ)) :
    rampArea x = score p - (x - Chebyshev.theta p) ^ 2 / 2 := by
  unfold rampArea
  rw [active_primes_in_gap gap hpx hxr]
  have expand :
      (∑ q ∈ Nat.primesLE p, max (x - (q : ℝ)) 0 * Real.log q) =
        x * Chebyshev.theta p - weightedPosition p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, weightedPosition, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hqx : (q : ℝ) ≤ x := (Nat.cast_le.mpr (Nat.mem_primesLE.mp hq).1).trans hpx
    rw [max_eq_left (sub_nonneg.mpr hqx), sub_mul]
  rw [expand, score]
  ring

/-- At an interior eligible stop the score is attained, uniquely on the half-open prime gap. -/
theorem stopping_point_unique_max {p r : ℕ} (gap : PrimeGap p r)
    (hleft : (p : ℝ) < Chebyshev.theta p) (hright : Chebyshev.theta p < r) :
    rampArea (Chebyshev.theta p) = score p ∧
      ∀ x : ℝ, (p : ℝ) ≤ x → x < r → x ≠ Chebyshev.theta p →
        rampArea x < rampArea (Chebyshev.theta p) := by
  have attained : rampArea (Chebyshev.theta p) = score p := by
    simpa using completed_square_in_gap gap hleft.le hright
  refine ⟨attained, ?_⟩
  intro x hpx hxr hne
  rw [completed_square_in_gap gap hpx hxr, attained]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

end
end Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea
