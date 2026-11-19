import Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral

open Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
open MeasureTheory

noncomputable section

/-- Abel summation of the full ordinary-prime logarithmic weights up to a real endpoint. -/
theorem integral_theta_eq_first_moment {x : ℝ} (hx : 2 ≤ x) :
    (∫ u in 2..x, Chebyshev.theta u) =
      x * Chebyshev.theta x - weightedPosition ⌊x⌋₊ := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n else 0
  have mass_sum (y : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊y⌋₊, a n) = Chebyshev.theta y := by
    simp [a, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have weighted : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) * a n) = weightedPosition ⌊x⌋₊ := by
    unfold weightedPosition
    simp [a, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter, mul_ite]
  have hd : ∀ u ∈ Set.Icc 2 x, DifferentiableAt ℝ (fun y : ℝ ↦ y) u :=
    fun _ _ ↦ differentiableAt_id
  have hi : IntegrableOn (deriv fun y : ℝ ↦ y) (Set.Icc 2 x) := by simp
  have h := sum_mul_eq_sub_integral_mul₁ a (by simp [a]) (by simp [a])
    x hd hi
  rw [← intervalIntegral.integral_of_le hx] at h
  simp only [deriv_id'', one_mul, weighted, mass_sum] at h
  linarith only [h]

/-- The area is the interval integral of the genuine Mathlib Chebyshev function. -/
theorem integral_theta_sub_id_eq_rampArea {x : ℝ} (hx : 2 ≤ x) :
    (∫ u in 2..x, (Chebyshev.theta u - u)) = rampArea x := by
  have split_integral : (∫ u in 2..x, (Chebyshev.theta u - u)) =
      (∫ u in 2..x, Chebyshev.theta u) - (∫ u in 2..x, u) :=
    intervalIntegral.integral_sub Chebyshev.theta_mono.intervalIntegrable
      (continuous_id.intervalIntegrable 2 x)
  rw [split_integral, integral_theta_eq_first_moment hx, integral_id]
  unfold rampArea weightedPosition
  rw [Chebyshev.theta_eq_sum_primesLE, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hsum :
      (∑ q ∈ Nat.primesLE ⌊x⌋₊, (x * Real.log q - (q : ℝ) * Real.log q)) =
        ∑ q ∈ Nat.primesLE ⌊x⌋₊, max (x - (q : ℝ)) 0 * Real.log q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqx : (q : ℝ) ≤ x :=
      (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp (Nat.mem_primesLE.mp hq).1
    rw [max_eq_left (sub_nonneg.mpr hqx), sub_mul]
  rw [hsum]
  ring

/-- The exact ordinary-prime integral sign criterion and the squarefree condition coincide. -/
theorem integral_negative_iff_squarefree_prime_cost :
    (∀ x : ℝ, 2 < x → (∫ u in 2..x, (Chebyshev.theta u - u)) < 0) ↔
    (∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n) := by
  rw [← negative_ramp_iff_integer_inequality]
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ by
    rw [integral_theta_sub_id_eq_rampArea hx.le]

end
end Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral
