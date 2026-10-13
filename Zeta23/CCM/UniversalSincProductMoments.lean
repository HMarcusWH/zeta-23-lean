import Zeta23.CCM.UniversalSincDetectorInverse
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Quantitative polynomial moments of the actual infinite sinc product

The positive-half-line Gamma integral with power `1/2`, followed by reflection,
evaluates the exact Gevrey envelope. The existing bound for the original infinite
product then supplies an integrated factorial bound. A separate elementary
factorial comparison expresses the same bound in Gevrey-order-two form.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM.UniversalSinc

/-- The positive decay scale already present in the actual product bound. -/
def gevreyMomentScale (s : ℝ) : ℝ :=
  (Real.log 2 / 2) * Real.sqrt s

theorem gevreyMomentScale_pos {s : ℝ} (hs : 0 < s) :
    0 < gevreyMomentScale s :=
  mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (Real.sqrt_pos.mpr hs)

/-- Exact integral of the polynomial square-root-exponential envelope on the
positive half-line. The factor two is the Jacobian in the Gamma substitution. -/
theorem polynomial_sqrt_decay_Ioi_integral (m : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-b * Real.sqrt x)) =
      2 * (Nat.factorial (2 * m + 1) : ℝ) / b ^ (2 * m + 2) := by
  have hraw := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (q := (m : ℝ)) (b := b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m]) hb
  have harg : ((m : ℝ) + 1) / (1 / 2 : ℝ) =
      ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hexponent : -((m : ℝ) + 1) / (1 / 2 : ℝ) =
      -((2 * m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg, hexponent, Real.rpow_neg hb.le, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at hraw
  norm_num only at hraw
  have heval :
      (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-b * Real.sqrt x)) =
        (b ^ (2 * m + 2))⁻¹ * 2 * (Nat.factorial (2 * m + 1) : ℝ) := by
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using hraw
  exact heval.trans (by ring)

/-- Reflection doubles the positive-half-line envelope integral. -/
theorem polynomial_sqrt_decay_integral (m : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ m * Real.exp (-b * Real.sqrt |x|)) =
      4 * (Nat.factorial (2 * m + 1) : ℝ) / b ^ (2 * m + 2) := by
  calc
    _ = 2 * ∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-b * Real.sqrt x) :=
      integral_comp_abs
    _ = _ := by rw [polynomial_sqrt_decay_Ioi_integral m hb]; ring

/-- Every actual product moment has the explicit factorial bound obtained
from its proved Gevrey envelope. The constant eight consists of the envelope
factor two, reflection factor two, and Gamma-substitution factor two. -/
theorem product_norm_moment_integral_le_factorial {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖) ≤
      8 * (Nat.factorial (2 * m + 1) : ℝ) /
        (gevreyMomentScale s) ^ (2 * m + 2) := by
  have hb := gevreyMomentScale_pos hs
  have henv := (integrable_polynomial_sqrt_decay m hb).const_mul (2 : ℝ)
  have hpoint (x : ℝ) : |x| ^ m * ‖product s (x : ℂ)‖ ≤
      2 * (|x| ^ m * Real.exp (-gevreyMomentScale s * Real.sqrt |x|)) := by
    have hp := product_norm_ofReal_le_gevrey hs x
    have hphase : -(Real.log 2 / 2) * Real.sqrt (s * |x|) =
        -gevreyMomentScale s * Real.sqrt |x| := by
      rw [Real.sqrt_mul hs.le]
      unfold gevreyMomentScale
      ring
    rw [hphase] at hp
    exact (mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg x) m)).trans_eq
      (by ring)
  calc
    _ ≤ ∫ x : ℝ, 2 *
        (|x| ^ m * Real.exp (-gevreyMomentScale s * Real.sqrt |x|)) :=
      integral_mono (integrable_product_ofReal_norm_moment hs m) henv hpoint
    _ = 2 * ∫ x : ℝ, |x| ^ m *
        Real.exp (-gevreyMomentScale s * Real.sqrt |x|) := integral_const_mul _ _
    _ = _ := by rw [polynomial_sqrt_decay_integral m hb]; ring

/-- Elementary factorial growth sufficient for Gevrey order two. -/
theorem factorial_two_mul_add_one_le (m : ℕ) :
    Nat.factorial (2 * m + 1) ≤ 12 ^ m * (Nat.factorial m) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hindex : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    have hcoeff : (2 * m + 3) * (2 * m + 2) ≤ 12 * (m + 1) ^ 2 := by
      nlinarith
    calc
      Nat.factorial (2 * (m + 1) + 1) =
          (2 * m + 3) * (2 * m + 2) * Nat.factorial (2 * m + 1) := by
        rw [hindex, Nat.factorial_succ, Nat.factorial_succ]
        ring
      _ ≤ (2 * m + 3) * (2 * m + 2) * (12 ^ m * (Nat.factorial m) ^ 2) :=
        Nat.mul_le_mul_left _ ih
      _ ≤ (12 * (m + 1) ^ 2) * (12 ^ m * (Nat.factorial m) ^ 2) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = 12 ^ (m + 1) * (Nat.factorial (m + 1)) ^ 2 := by
        rw [pow_succ, Nat.factorial_succ]
        ring

/-- Integrated Gevrey-order-two growth for the actual product. This controls
the Fourier moments themselves; derivative transport is a further theorem. -/
theorem product_norm_moment_integral_le_gevrey {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖) ≤
      (8 / (gevreyMomentScale s) ^ 2) *
        (12 / (gevreyMomentScale s) ^ 2) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
  have hb := gevreyMomentScale_pos hs
  have hfactorial : (Nat.factorial (2 * m + 1) : ℝ) ≤
      (12 : ℝ) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
    exact_mod_cast factorial_two_mul_add_one_le m
  calc
    _ ≤ 8 * (Nat.factorial (2 * m + 1) : ℝ) /
        (gevreyMomentScale s) ^ (2 * m + 2) :=
      product_norm_moment_integral_le_factorial hs m
    _ ≤ 8 * ((12 : ℝ) ^ m * (Nat.factorial m : ℝ) ^ 2) /
        (gevreyMomentScale s) ^ (2 * m + 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactorial (by norm_num)) (pow_nonneg hb.le _)
    _ = _ := by
      rw [pow_add, pow_mul, div_pow]
      field_simp [hb.ne'] <;> ring

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.polynomial_sqrt_decay_Ioi_integral
#print axioms Zeta23.CCM.UniversalSinc.polynomial_sqrt_decay_integral
#print axioms Zeta23.CCM.UniversalSinc.product_norm_moment_integral_le_factorial
#print axioms Zeta23.CCM.UniversalSinc.factorial_two_mul_add_one_le
#print axioms Zeta23.CCM.UniversalSinc.product_norm_moment_integral_le_gevrey
