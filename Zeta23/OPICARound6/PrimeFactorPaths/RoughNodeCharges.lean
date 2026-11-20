import Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! # Selector comparison for actual rough Möbius charges

The cutoff is strict. The definition includes the empty prime-factor set at one,
and the arithmetic Möbius function gives zero to nonsquarefree labels.
Nodes can overlap across tree levels. Removing a set of vertices affects all
its incident nodes. These finite comparisons leave the survivor estimate open.
-/

namespace Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges

open scoped ArithmeticFunction.Moebius

/-- The full signed interaction of a two-bit population after subtracting its marginals. -/
theorem contingency_covariance (a b c d : ℝ) :
    (a+b+c+d)*(a-b-c+d) - (a+b-c-d)*(a-b+c-d) = 4*(a*d-b*c) := by
  ring

noncomputable def roughSign (y n : ℕ) : ℝ :=
  if ∀ p ∈ n.primeFactors, y < p then (μ n : ℤ) else 0

noncomputable def charge (y : ℕ) (labels : Finset ℕ) : ℝ :=
  ∑ n ∈ labels, roughSign y n

/-- The full sign of a rough label factors across any coprime split. -/
theorem roughSign_factor {y d m : ℕ} (hcop : Nat.Coprime d m)
    (hrough : ∀ p ∈ (d * m).primeFactors, y < p) :
    roughSign y (d * m) = (μ d : ℝ) * (μ m : ℝ) := by
  rw [roughSign, if_pos hrough,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, Int.cast_mul]

/-- At every threshold the two factor-count parities multiply to the whole genuine sign. -/
theorem roughSign_split_parity {y n : ℕ} (z : ℕ) (hsq : Squarefree n)
    (hrough : ∀ p ∈ n.primeFactors, y < p) :
    roughSign y n = (-1 : ℝ) ^ (n.primeFactors.filter (· ≤ z)).card *
      (-1 : ℝ) ^ (n.primeFactors.filter (z < ·)).card := by
  have hω : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
    rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).mpr hsq,
      ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.primeFactors) (fun p => p ≤ z)
  simp only [not_le] at hsplit
  rw [roughSign, if_pos hrough, ArithmeticFunction.moebius_apply_of_squarefree hsq,
    Int.cast_pow, Int.cast_neg, Int.cast_one, hω, ← hsplit, pow_add]

theorem abs_roughSign_le_one (y n : ℕ) : |roughSign y n| ≤ 1 := by
  unfold roughSign
  split_ifs
  · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · norm_num

theorem abs_charge_le_card (y : ℕ) (labels : Finset ℕ) :
    |charge y labels| ≤ labels.card := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ n ∈ labels, |roughSign y n| ≤ ∑ _n ∈ labels, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => abs_roughSign_le_one y n
    _ = labels.card := by simp

/-- Partition the original signed charges exactly, including unused potential partners. -/
theorem charge_sub_survivors (y : ℕ) (labels removed : Finset ℕ) :
    charge y labels - charge y (labels \ removed) = charge y (labels ∩ removed) := by
  have h := labels.sum_inter_add_sum_sdiff removed (roughSign y)
  unfold charge
  exact sub_eq_iff_eq_add.mpr h.symm

/-- The absolute changes are summed individually over all nodes at either polarity.
No probabilistic property of the removal rule is needed for this finite statement. -/
theorem selector_energy_loss {ι : Type*} (nodes : Finset ι) (labels : ι → Finset ℕ)
    (removed : Finset ℕ) (y : ℕ) (w : ι → ℝ) (hw : ∀ j ∈ nodes, 0 ≤ w j)
    (pol : ℝ) (hpol : |pol| = 1) :
    ∑ j ∈ nodes, w j *
      |(max (pol * charge y (labels j)) 0)^2 -
       (max (pol * charge y (labels j \ removed)) 0)^2| ≤
    ∑ j ∈ nodes, w j * (2 * (labels j).card * |charge y (labels j ∩ removed)|) := by
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  have hfull : |pol * charge y (labels j)| ≤ (labels j).card := by
    simpa only [abs_mul, hpol, one_mul] using abs_charge_le_card y (labels j)
  have hsurv : |pol * charge y (labels j \ removed)| ≤ (labels j).card := by
    rw [abs_mul, hpol, one_mul]
    exact (abs_charge_le_card y _).trans
      (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := labels j) (t := removed)))
  have h := FiniteSelectorEnergy.posSq_sub_le _ _ _ hfull hsurv
  rwa [← mul_sub, abs_mul, hpol, one_mul, charge_sub_survivors] at h

end Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges
