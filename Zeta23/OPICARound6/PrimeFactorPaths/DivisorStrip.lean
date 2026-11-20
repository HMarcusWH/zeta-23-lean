import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The signed cofactor coefficient wherever the truncated inverse is Möbius. -/
def residual (L n : ℕ) : ℤ := -(∑ d ∈ n.divisors, if d ≤ L then μ d else 0)

/-- For every prime occurring exactly once, only boundary divisors of its complement survive. -/
theorem residual_prime_mul {p n : ℕ} (hp : p.Prime) (hc : p.Coprime n) (L : ℕ) :
    residual L (p * n) =
      -(∑ d ∈ n.divisors, if d ≤ L ∧ L < p * d then μ d else 0) := by
  unfold residual
  congr 1
  rw [hc.divisors_mul, Finset.sum_map]
  change (∑ z ∈ (p.divisors ×ˢ n.divisors).attach,
    (fun xy : ℕ × ℕ ↦ if xy.1 * xy.2 ≤ L then μ (xy.1 * xy.2) else 0) z.val) = _
  rw [Finset.sum_attach (p.divisors ×ˢ n.divisors)
      (fun xy : ℕ × ℕ ↦ if xy.1 * xy.2 ≤ L then μ (xy.1 * xy.2) else 0),
    Finset.sum_product, hp.divisors]
  simp only [Finset.mem_singleton, hp.ne_one.symm, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [isMultiplicative_moebius.map_mul_of_coprime
    (hc.coprime_dvd_right (Nat.mem_divisors.mp hd).1), moebius_apply_prime hp, neg_one_mul]
  have hdp : d ≤ p * d := Nat.le_mul_of_pos_left d hp.pos
  split_ifs <;> omega

/-- Each nonzero coefficient supplies a genuine divisor carrying nonzero Möbius weight in the strip. -/
theorem exists_divisor_of_residual_ne_zero {p n L : ℕ} (hp : p.Prime) (hc : p.Coprime n)
    (h : residual L (p * n) ≠ 0) :
    ∃ d ∈ n.divisors, d ≤ L ∧ L < p * d ∧ μ d ≠ 0 := by
  by_contra! hnone
  apply h
  rw [residual_prime_mul hp hc, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro d hd
  split_ifs with hcond
  · exact hnone d hd hcond.1 hcond.2
  · rfl

end Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip
