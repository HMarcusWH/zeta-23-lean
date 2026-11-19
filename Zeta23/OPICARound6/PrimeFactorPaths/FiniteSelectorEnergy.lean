import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy

variable {ι : Type*}

/-- Positive-part squaring on the real interval of radius H. -/
theorem posSq_sub_le (u v H : ℝ) (hu : |u| ≤ H) (hv : |v| ≤ H) :
    |(max u 0) ^ 2 - (max v 0) ^ 2| ≤ 2 * H * |u - v| := by
  have h0 : 0 ≤ H := (abs_nonneg u).trans hu
  have hum : max u 0 ≤ H := max_le ((le_abs_self u).trans hu) h0
  have hvm : max v 0 ≤ H := max_le ((le_abs_self v).trans hv) h0
  have hsum : max u 0 + max v 0 ≤ 2 * H := by
    rw [two_mul]
    exact add_le_add hum hvm
  have hfactor : (max u 0)^2 - (max v 0)^2 =
      (max u 0 + max v 0) * (max u 0 - max v 0) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))]
  exact mul_le_mul hsum (abs_max_sub_max_le_abs u v 0) (abs_nonneg _)
    (mul_nonneg (by norm_num) h0)

/-- Signed node weights and varying heights are allowed. A polarity of absolute
value one simultaneously covers positive and negative excess. -/
theorem signed_weight_energy_comparison (s : Finset ι) (w u v H : ι → ℝ)
    (pol : ℝ) (hpol : |pol| = 1) (hu : ∀ i ∈ s, |u i| ≤ H i)
    (hv : ∀ i ∈ s, |v i| ≤ H i) :
    |(∑ i ∈ s, w i * (max (pol * u i) 0)^2) -
      (∑ i ∈ s, w i * (max (pol * v i) 0)^2)| ≤
      ∑ i ∈ s, |w i| * (2 * H i * |u i-v i|) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i hi
  rw [← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h₁ : |pol * u i| ≤ H i := by simpa only [abs_mul, hpol, one_mul] using hu i hi
  have h₂ : |pol * v i| ≤ H i := by simpa only [abs_mul, hpol, one_mul] using hv i hi
  have h := posSq_sub_le (pol * u i) (pol * v i) (H i) h₁ h₂
  rwa [← mul_sub, abs_mul, hpol, one_mul] at h

/-- The comparison on the original nonnegative graph weights. -/
theorem weighted_energy_comparison (s : Finset ι) (w u v H : ι → ℝ)
    (pol : ℝ) (hpol : |pol| = 1) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, |u i| ≤ H i) (hv : ∀ i ∈ s, |v i| ≤ H i) :
    |(∑ i ∈ s, w i * (max (pol * u i) 0)^2) -
      (∑ i ∈ s, w i * (max (pol * v i) 0)^2)| ≤
      ∑ i ∈ s, w i * (2 * H i * |u i-v i|) := by
  apply (signed_weight_energy_comparison s w u v H pol hpol hu hv).trans_eq
  exact Finset.sum_congr rfl fun i hi => by rw [abs_of_nonneg (hw i hi)]

/-- The squared weighted distance contracts under either one-sided selector. -/
theorem weighted_sq_distance_le (s : Finset ι) (w u v : ι → ℝ)
    (pol : ℝ) (hpol : |pol| = 1) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (max (pol * u i) 0 - max (pol * v i) 0)^2) ≤
      ∑ i ∈ s, w i * (u i-v i)^2 := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  apply sq_le_sq.mpr
  have h := abs_max_sub_max_le_abs (pol * u i) (pol * v i) 0
  rwa [← mul_sub, abs_mul, hpol, one_mul] at h

end Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy
