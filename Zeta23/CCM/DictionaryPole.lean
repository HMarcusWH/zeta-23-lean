import Zeta23.CCM.DictionaryDeterministicRHS
import Zeta23.CCM.DictionaryTentTransform
import Zeta23.CCM.Displacement

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators Interval

/-- Fourier frequency attached to an integer dictionary index. -/
def dictionaryFrequency (n : ℤ) (L : ℝ) : ℝ :=
  2 * Real.pi * (n : ℝ) / L

/-- On the diagonal, the production half-kernel is exactly the canonical tent
modulated by the corresponding cosine mode. -/
theorem dictionaryBasisTest_diag_eq_tent_cos
    {L : ℝ} (hL : 0 < L) (n : ℤ) (y : ℝ) :
    dictionaryBasisTest n n L y =
      dictionaryTent L y * ((Real.cos (dictionaryFrequency n L * y) : ℝ) : ℂ) := by
  by_cases hy : |y| ≤ L
  · have hfreq :
        2 * Real.pi * (n : ℝ) * |y| / L = dictionaryFrequency n L * |y| := by
      unfold dictionaryFrequency
      field_simp [hL.ne']
      ring
    have hcos :
        Real.cos (dictionaryFrequency n L * |y|) =
          Real.cos (dictionaryFrequency n L * y) := by
      by_cases hy0 : 0 ≤ y
      · rw [abs_of_nonneg hy0]
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        rw [abs_of_nonpos hy0']
        rw [show dictionaryFrequency n L * -y = -(dictionaryFrequency n L * y) by ring,
          Real.cos_neg]
    rw [dictionaryTent_eq_one_sub_abs_div_of_abs_le hL hy]
    simp only [dictionaryBasisTest, kernel, hy, if_pos, qBasis]
    rw [hfreq, hcos]
    push_cast
    ring
  · have hlt : L < |y| := lt_of_not_ge hy
    rw [dictionaryBasisTest_eq_zero_of_lt_abs hlt,
      dictionaryTent_eq_zero_of_lt_abs hL hlt]
    simp

private theorem integrable_dictionaryTent_exp
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Integrable (fun y : ℝ => dictionaryTent L y * Complex.exp (I * z * y)) := by
  have hcont : Continuous
      (fun y : ℝ => dictionaryTent L y * Complex.exp (I * z * y)) := by
    fun_prop
  apply hcont.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  have hlt : L < |y| := by
    by_contra hnot
    have habs : |y| ≤ L := le_of_not_gt hnot
    exact hy (abs_le.mp habs)
  rw [dictionaryTent_eq_zero_of_lt_abs hL hlt]
  simp

/-- Native complex-frequency modulation identity for the canonical tent. -/
theorem paperFT_dictionaryTent_mul_cos
    {L : ℝ} (hL : 0 < L) (a : ℝ) (z : ℂ) :
    Zeta23.paperFT
        (fun y : ℝ => dictionaryTent L y * ((Real.cos (a * y) : ℝ) : ℂ)) z =
      (Zeta23.paperFT (dictionaryTent L) (z + (a : ℂ)) +
        Zeta23.paperFT (dictionaryTent L) (z - (a : ℂ))) / 2 := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, Zeta23.paperFT_def]
  have hp := integrable_dictionaryTent_exp hL (z + (a : ℂ))
  have hm := integrable_dictionaryTent_exp hL (z - (a : ℂ))
  have hpoint : ∀ y : ℝ,
      (dictionaryTent L y * ((Real.cos (a * y) : ℝ) : ℂ)) *
          Complex.exp (I * z * y) =
        (1 / 2 : ℂ) *
          (dictionaryTent L y * Complex.exp (I * (z + (a : ℂ)) * y) +
            dictionaryTent L y * Complex.exp (I * (z - (a : ℂ)) * y)) := by
    intro y
    rw [Complex.ofReal_cos]
    unfold Complex.cos
    have hplus :
        Complex.exp (((a * y : ℝ) : ℂ) * I) * Complex.exp (I * z * y) =
          Complex.exp (I * (z + (a : ℂ)) * y) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hminus :
        Complex.exp (-(((a * y : ℝ) : ℂ)) * I) * Complex.exp (I * z * y) =
          Complex.exp (I * (z - (a : ℂ)) * y) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      dictionaryTent L y *
            ((Complex.exp (((a * y : ℝ) : ℂ) * I) +
              Complex.exp (-(((a * y : ℝ) : ℂ)) * I)) / 2) *
            Complex.exp (I * z * y) =
          (1 / 2 : ℂ) * dictionaryTent L y *
            (Complex.exp (((a * y : ℝ) : ℂ) * I) * Complex.exp (I * z * y) +
              Complex.exp (-(((a * y : ℝ) : ℂ)) * I) * Complex.exp (I * z * y)) := by
            ring
      _ = (1 / 2 : ℂ) *
          (dictionaryTent L y * Complex.exp (I * (z + (a : ℂ)) * y) +
            dictionaryTent L y * Complex.exp (I * (z - (a : ℂ)) * y)) := by
            rw [hplus, hminus]
            ring
  calc
    (∫ y : ℝ,
        (dictionaryTent L y * ((Real.cos (a * y) : ℝ) : ℂ)) *
          Complex.exp (I * z * y)) =
        ∫ y : ℝ, (1 / 2 : ℂ) *
          (dictionaryTent L y * Complex.exp (I * (z + (a : ℂ)) * y) +
            dictionaryTent L y * Complex.exp (I * (z - (a : ℂ)) * y)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          exact hpoint y
    _ = (1 / 2 : ℂ) *
        ((∫ y : ℝ, dictionaryTent L y * Complex.exp (I * (z + (a : ℂ)) * y)) +
          ∫ y : ℝ, dictionaryTent L y * Complex.exp (I * (z - (a : ℂ)) * y)) := by
          rw [Zeta23.integral_const_mul_C, MeasureTheory.integral_add hp hm]
    _ = ((∫ y : ℝ, dictionaryTent L y * Complex.exp (I * (z + (a : ℂ)) * y)) +
          ∫ y : ℝ, dictionaryTent L y * Complex.exp (I * (z - (a : ℂ)) * y)) / 2 := by
          ring

end Zeta23.CCM
