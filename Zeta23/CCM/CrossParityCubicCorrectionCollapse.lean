import Zeta23.CCM.CrossParityQuotientTransport
import Mathlib.NumberTheory.Bernoulli

noncomputable section

namespace Zeta23.CCM

open Matrix Set Finset
open scoped BigOperators ComplexConjugate

/-!
# Cross-parity cubic correction collapse

The post-#223 exact-algebra audit exposed that the two odd predecessor
corrections used by the centered-index transport and by the cubic generator
are not independent.  This module proves that relation in the native finite
geometry before composing it with any aperture, source matrix, first-bad
certificate, or RH-directed assumption.
-/

private theorem sum_range_pow_one_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 1) =
      (m : ℚ) * (m - 1 : ℚ) / 2 := by
  rw [Finset.sum_range_pow]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sum_range_pow_two_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 2) =
      (m : ℚ) * (m - 1 : ℚ) * (2 * m - 1 : ℚ) / 6 := by
  rw [Finset.sum_range_pow]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sum_range_pow_three_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 3) =
      ((m : ℚ) * (m - 1 : ℚ) / 2) ^ 2 := by
  rw [Finset.sum_range_pow]
  norm_num [Finset.sum_range_succ]
  ring

private theorem sum_range_pow_four_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 4) =
      (m : ℚ) * (m - 1 : ℚ) * (2 * m - 1 : ℚ) *
        (3 * m ^ 2 - 3 * m - 1 : ℚ) / 30 := by
  rw [Finset.sum_range_pow]
  norm_num [Finset.sum_range_succ]
  ring

private theorem centered_square_sum_rat (N : ℕ) :
    (∑ i : Fin (2 * N + 1),
        (((i.1 : ℚ) - (N : ℚ)) ^ 2)) =
      (N : ℚ) * (N + 1 : ℚ) * (2 * N + 1 : ℚ) / 3 := by
  rw [Fin.sum_univ_eq_sum_range]
  simp_rw [sub_sq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_range_pow_two_rat, sum_range_pow_one_rat]
  simp
  ring

private theorem centered_fourth_sum_rat (N : ℕ) :
    (∑ i : Fin (2 * N + 1),
        (((i.1 : ℚ) - (N : ℚ)) ^ 4)) =
      (N : ℚ) * (N + 1 : ℚ) * (2 * N + 1 : ℚ) *
        (3 * N ^ 2 + 3 * N - 1 : ℚ) / 15 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hexpand (k : ℕ) :
      ((k : ℚ) - (N : ℚ)) ^ 4 =
        (k : ℚ) ^ 4 -
          4 * (N : ℚ) * (k : ℚ) ^ 3 +
          6 * (N : ℚ) ^ 2 * (k : ℚ) ^ 2 -
          4 * (N : ℚ) ^ 3 * (k : ℚ) +
          (N : ℚ) ^ 4 := by ring
  simp_rw [hexpand]
  repeat' rw [Finset.sum_add_distrib]
  repeat' rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_range_pow_four_rat, sum_range_pow_three_rat,
    sum_range_pow_two_rat, sum_range_pow_one_rat]
  simp
  ring

end Zeta23.CCM
