import Zeta23.CCM.DictionaryTentTransform
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section

namespace Zeta23.CCM

open Complex

/-!
# Critical-strip decay of the canonical dictionary tent

The exact transform from `DictionaryTentTransform` has a removable value at the
origin and, away from the origin, a literal `z^2` denominator.  This file turns
that closed form into the quadratic strip estimate needed by the inherited zero
summability machinery.

No explicit formula is invoked here.
-/

/-- Elementary complex-cosine growth bound used by the tent transform. -/
private theorem norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hplus : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [Complex.mul_re]
    exact neg_le_abs z.im
  have hminus : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [Complex.mul_re]
    exact le_abs_self z.im
  have htwo : 2 * ‖Complex.cos z‖ ≤ 2 * Real.exp |z.im| := by
    calc
      2 * ‖Complex.cos z‖ = ‖(2 : ℂ) * Complex.cos z‖ := by
        simp
      _ = ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ := by
        rw [Complex.two_cos]
      _ ≤ ‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp |z.im| := by linarith
  linarith

/-- On the critical strip, the cosine numerator has an aperture-only bound. -/
private theorem norm_one_sub_cos_L_mul_le
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hstrip : |z.im| ≤ 1 / 2) :
    ‖(1 : ℂ) - Complex.cos ((L : ℂ) * z)‖ ≤ 1 + Real.exp (L / 2) := by
  have him : |(((L : ℂ) * z).im)| ≤ L / 2 := by
    have himul : (((L : ℂ) * z).im) = L * z.im := by
      simp [Complex.mul_im]
    rw [himul, abs_mul, abs_of_pos hL]
    nlinarith
  have hcos : ‖Complex.cos ((L : ℂ) * z)‖ ≤ Real.exp (L / 2) := by
    calc
      ‖Complex.cos ((L : ℂ) * z)‖
          ≤ Real.exp |(((L : ℂ) * z).im)| := norm_cos_le_exp_abs_im _
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr him
  calc
    ‖(1 : ℂ) - Complex.cos ((L : ℂ) * z)‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.cos ((L : ℂ) * z)‖ := norm_sub_le _ _
    _ ≤ 1 + Real.exp (L / 2) := by simpa using add_le_add_left hcos 1

/-- Critical-strip quadratic decay in the same multiplied form used by the
existing smooth-test `paperFT` estimates.  The removable node is harmless
because the left side vanishes at `z = 0`. -/
theorem norm_paperFT_dictionaryTent_mul_sq_le
    {L : ℝ} (hL : 0 < L) (z : ℂ) (hstrip : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (dictionaryTent L) z‖ * ‖z‖ ^ 2
      ≤ 2 * (1 + Real.exp (L / 2)) / L := by
  by_cases hz : z = 0
  · subst z
    simp
    positivity
  · rw [paperFT_dictionaryTent_of_ne_zero hL hz]
    have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hden : ‖(L : ℂ) * z ^ 2‖ = L * ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow]
      simp [abs_of_pos hL]
    have hnum :
        ‖(2 : ℂ) * ((1 : ℂ) - Complex.cos ((L : ℂ) * z))‖
          ≤ 2 * (1 + Real.exp (L / 2)) := by
      rw [norm_mul]
      norm_num
      exact mul_le_mul_of_nonneg_left
        (norm_one_sub_cos_L_mul_le hL hstrip) (by norm_num)
    rw [norm_div, hden]
    calc
      ‖(2 : ℂ) * ((1 : ℂ) - Complex.cos ((L : ℂ) * z))‖ /
              (L * ‖z‖ ^ 2) * ‖z‖ ^ 2
          = ‖(2 : ℂ) * ((1 : ℂ) - Complex.cos ((L : ℂ) * z))‖ / L := by
              field_simp [hL.ne', hzNorm]
      _ ≤ 2 * (1 + Real.exp (L / 2)) / L :=
        div_le_div_of_nonneg_right hnum hL.le

end Zeta23.CCM
