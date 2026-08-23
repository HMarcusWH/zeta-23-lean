import Zeta23.CCM.DictionaryPole

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators Interval

private theorem paperFT_dictionaryTent_neg
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTent L) (-z) =
      Zeta23.paperFT (dictionaryTent L) z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [paperFT_dictionaryTent_of_ne_zero hL (neg_ne_zero.mpr hz),
      paperFT_dictionaryTent_of_ne_zero hL hz]
    rw [show (L : ℂ) * -z = -((L : ℂ) * z) by ring, Complex.cos_neg]
    ring

private theorem dictionaryFrequency_mul_L
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    L * dictionaryFrequency n L = (n : ℝ) * (2 * Real.pi) := by
  unfold dictionaryFrequency
  field_simp [hL.ne']
  ring

private theorem sin_dictionaryFrequency_period
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.sin (L * dictionaryFrequency n L) = 0 := by
  rw [dictionaryFrequency_mul_L hL n]
  have hs := Real.sin_int_mul_pi (2 * n)
  convert hs using 1 <;> push_cast <;> ring

private theorem cos_dictionaryFrequency_period
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.cos (L * dictionaryFrequency n L) = 1 := by
  rw [dictionaryFrequency_mul_L hL n]
  simpa using Real.cos_int_mul_two_pi n

private theorem cos_dictionaryPole_shift_plus
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Complex.cos
        ((L : ℂ) * (Complex.I / 2 + (dictionaryFrequency n L : ℂ))) =
      (Real.cosh (L / 2) : ℂ) := by
  have harg :
      (L : ℂ) * (Complex.I / 2 + (dictionaryFrequency n L : ℂ)) =
        ((L * dictionaryFrequency n L : ℝ) : ℂ) +
          ((L / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_add_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  rw [cos_dictionaryFrequency_period hL n, sin_dictionaryFrequency_period hL n]
  simp

private theorem cos_dictionaryPole_shift_minus
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Complex.cos
        ((L : ℂ) * (Complex.I / 2 - (dictionaryFrequency n L : ℂ))) =
      (Real.cosh (L / 2) : ℂ) := by
  have h := cos_dictionaryPole_shift_plus hL (-n)
  convert h using 1 <;> unfold dictionaryFrequency <;> push_cast <;> ring

private theorem one_sub_cosh_half_eq_neg_two_sinh_sq (L : ℝ) :
    1 - Real.cosh (L / 2) = -2 * Real.sinh (L / 4) ^ 2 := by
  have h1 := Real.cosh_two_mul (L / 4)
  have h2 := Real.cosh_sq_sub_sinh_sq (L / 4)
  rw [show 2 * (L / 4) = L / 2 by ring] at h1
  nlinarith

/-- The diagonal pole channel is exactly the existing finite CCM pole component.
This is the first exact normalization gate after the shifted-tent reduction. -/
theorem dictionaryPoleRHS_basis_diag
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryPoleRHS (dictionaryBasisTest n n L) =
      ((poleComponent n n L : ℝ) : ℂ) := by
  have hplus :
      Complex.I / 2 + (dictionaryFrequency n L : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hminus :
      Complex.I / 2 - (dictionaryFrequency n L : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hnegPlus :
      -Complex.I / 2 - (dictionaryFrequency n L : ℂ) =
        -(Complex.I / 2 + (dictionaryFrequency n L : ℂ)) := by
    ring
  have hnegMinus :
      -Complex.I / 2 + (dictionaryFrequency n L : ℂ) =
        -(Complex.I / 2 - (dictionaryFrequency n L : ℂ)) := by
    ring
  rw [dictionaryPoleRHS_basis_diag_eq_tent_shifts hL n]
  rw [hnegMinus, paperFT_dictionaryTent_neg hL,
    hnegPlus, paperFT_dictionaryTent_neg hL]
  rw [paperFT_dictionaryTent_of_ne_zero hL hplus,
    paperFT_dictionaryTent_of_ne_zero hL hminus]
  rw [cos_dictionaryPole_shift_plus hL n,
    cos_dictionaryPole_shift_minus hL n]
  have hhyper :
      (1 - (Real.cosh (L / 2) : ℂ)) =
        ((-2 * Real.sinh (L / 4) ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast one_sub_cosh_half_eq_neg_two_sinh_sq L
  rw [hhyper]
  have hd :
      0 < L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
    positivity
  unfold dictionaryFrequency poleComponent
  dsimp
  push_cast
  field_simp [hL.ne', ne_of_gt hd]
  ring

end Zeta23.CCM
