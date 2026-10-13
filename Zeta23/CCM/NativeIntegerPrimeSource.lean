import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Push

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-!
Exact coefficient-level native integer/prime compatibility. These theorems do
not construct the convolution fields X and U: that analytic part of M15 remains
open. The zero coefficient is included, rather than pretending the divisor sum
at zero determines an arbitrary function's value there.
-/

def nativeIntegerCoefficient (n : ℕ) : ℝ := 1 / Real.sqrt n

def nativePrimeCoefficient (n : ℕ) : ℝ := Λ n / Real.sqrt n

def nativeIntegerDriveCoefficient (n : ℕ) : ℝ := Real.log n / Real.sqrt n

theorem native_divisor_coefficient_identity (n : ℕ) :
    ∑ d ∈ n.divisors, Λ d = Real.log n :=
  ArithmeticFunction.vonMangoldt_sum

/-- The complete native divisor law fixes every arithmetic coefficient. -/
theorem native_primeCoefficients_unique (f : ArithmeticFunction ℝ)
    (hf : ∀ n, ∑ d ∈ n.divisors, f d = Real.log n) :
    f = ArithmeticFunction.vonMangoldt := by
  have hmul : f * (ζ : ArithmeticFunction ℝ) = ArithmeticFunction.log := by
    ext n
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.log_apply] using hf n
  calc
    f = (f * (ζ : ArithmeticFunction ℝ)) * (μ : ArithmeticFunction ℝ) := by
      rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
    _ = ArithmeticFunction.log * (μ : ArithmeticFunction ℝ) := by rw [hmul]
    _ = ArithmeticFunction.vonMangoldt := ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

/-- A modified prime model cannot satisfy the complete unchanged divisor law. -/
theorem native_modifiedCoefficient_breaks_divisor_identity
    (f : ArithmeticFunction ℝ) (h : f ≠ ArithmeticFunction.vonMangoldt) :
    ∃ n, (∑ d ∈ n.divisors, f d) ≠ Real.log n := by
  by_contra hnone
  push_neg at hnone
  exact h (native_primeCoefficients_unique f hnone)

theorem native_weighted_divisor_coefficient_identity (n : ℕ) :
    ∑ d ∈ n.divisors, Λ d / Real.sqrt n = nativeIntegerDriveCoefficient n := by
  rw [← Finset.sum_div, native_divisor_coefficient_identity]
  rfl

end Zeta23.CCM
