import Zeta23.CCM.NativePositiveCompletionMass

/-!
# Exact integrals of the actual logarithmic floor cells

These integrals and their finite telescoping sum concern the unchanged
native positive completion. The infinite tail bound and the rational
605/621 comparison are separate obligations.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Interval

namespace Zeta23.CCM

private theorem mul_rpow_sub_one {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x * x ^ (r - 1) = x ^ r := by
  calc
    _ = x ^ (1 : ℝ) * x ^ (r - 1) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + (r - 1)) := (Real.rpow_add hx _ _).symm
    _ = _ := by congr 1; ring

/-- Integrate a literal native logarithmic cell; endpoints are null sets. -/
theorem nativePositiveCompletionLogDensity_cell_integral {n : ℕ} (hn : 0 < n) :
    (∫ u : ℝ in (n : ℝ)..((n : ℝ) + 1), nativePositiveCompletionLogDensity u) =
      (2 / 3 : ℝ) * ((1 - 2 * (n : ℝ)) * (n : ℝ) ^ (-1 / 2 : ℝ) +
        2 * (n : ℝ) * ((n : ℝ) + 1) ^ (-1 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnone : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro hz
    exact (not_le_of_gt hnpos) hz.1
  have h5 : IntervalIntegrable (fun u : ℝ => u ^ (-5 / 2 : ℝ)) volume
      (n : ℝ) ((n : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have h3 : IntervalIntegrable (fun u : ℝ => u ^ (-3 / 2 : ℝ)) volume
      (n : ℝ) ((n : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have heq :
      (∫ u : ℝ in (n : ℝ)..((n : ℝ) + 1), nativePositiveCompletionLogDensity u) =
        ∫ u : ℝ in (n : ℝ)..((n : ℝ) + 1),
          (n : ℝ) * ((n : ℝ) + 1) * u ^ (-5 / 2 : ℝ) -
            (n : ℝ) * u ^ (-3 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro u hu
    rw [nativePositiveCompletionLogDensity_cell hn hu.1.le hu.2]
    have hcollapse : u * u ^ (-5 / 2 : ℝ) = u ^ (-3 / 2 : ℝ) := by
      simpa only [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num] using
        mul_rpow_sub_one (hnpos.trans hu.1) (-3 / 2)
    calc
      _ = (n : ℝ) * ((n : ℝ) + 1) * u ^ (-5 / 2 : ℝ) -
            (n : ℝ) * (u * u ^ (-5 / 2 : ℝ)) := by ring
      _ = _ := by rw [hcollapse]
  rw [heq, intervalIntegral.integral_sub (h5.const_mul _) (h3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩),
    integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  norm_num only
  have hncollapse : (n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) =
      (n : ℝ) ^ (-1 / 2 : ℝ) := by
    simpa only [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] using
      mul_rpow_sub_one hnpos (-1 / 2)
  have hn1collapse : ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-3 / 2 : ℝ) =
      ((n : ℝ) + 1) ^ (-1 / 2 : ℝ) := by
    simpa only [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] using
      mul_rpow_sub_one hnone (-1 / 2)
  calc
    _ = (2 / 3 : ℝ) * (((n : ℝ) + 1) *
          ((n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)) -
        (n : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-3 / 2 : ℝ))) -
        2 * (n : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) +
        2 * (n : ℝ) * ((n : ℝ) + 1) ^ (-1 / 2 : ℝ) := by ring
    _ = _ := by rw [hncollapse, hn1collapse]; ring

private theorem nativePositiveCompletionLogDensity_intervalIntegrable_cell
    {n : ℕ} (hn : 0 < n) :
    IntervalIntegrable nativePositiveCompletionLogDensity volume
      (n : ℝ) ((n : ℝ) + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  exact nativePositiveCompletionLogDensity_integrableOn.mono_set
    (fun u hu => hn1.trans_lt hu.1)

private theorem nativePositiveCompletion_cell_sum (N : ℕ) :
    (∑ k ∈ range N, (2 / 3 : ℝ) *
      ((1 - 2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) +
        2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ (-1 / 2 : ℝ))) =
      (2 / 3 : ℝ) * (2 * (N : ℝ) * ((N : ℝ) + 1) ^ (-1 / 2 : ℝ) -
        ∑ k ∈ range N, ((k : ℝ) + 1) ^ (-1 / 2 : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    push_cast
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    ring

/-- The exact finite head, obtained from actual interval integrals. -/
theorem nativePositiveCompletionLogDensity_head_integral (N : ℕ) :
    (∫ u : ℝ in (1 : ℝ)..((N : ℝ) + 1), nativePositiveCompletionLogDensity u) =
      (2 / 3 : ℝ) * (2 * (N : ℝ) * ((N : ℝ) + 1) ^ (-1 / 2 : ℝ) -
        ∑ k ∈ range N, ((k : ℝ) + 1) ^ (-1 / 2 : ℝ)) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := nativePositiveCompletionLogDensity) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1) (n := N)
    (fun k hk => by
      have h := nativePositiveCompletionLogDensity_intervalIntegrable_cell
        (n := k + 1) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using h)
  have hcells :
      (∑ k ∈ range N, ∫ u : ℝ in ((k : ℝ) + 1)..(((k + 1 : ℕ) : ℝ) + 1),
        nativePositiveCompletionLogDensity u) =
        ∑ k ∈ range N, (2 / 3 : ℝ) *
          ((1 - 2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) +
            2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ (-1 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have h := nativePositiveCompletionLogDensity_cell_integral (n := k + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  have hsum' : (∫ u : ℝ in (1 : ℝ)..((N : ℝ) + 1),
      nativePositiveCompletionLogDensity u) =
      ∑ k ∈ range N, (2 / 3 : ℝ) *
        ((1 - 2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) +
          2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ (-1 / 2 : ℝ)) := by
    simpa only [Nat.cast_zero, zero_add] using hsum.symm.trans hcells
  exact hsum'.trans (nativePositiveCompletion_cell_sum N)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_cell_integral
#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_head_integral
