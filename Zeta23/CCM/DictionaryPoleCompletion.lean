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

private theorem sin_dictionaryFrequency_period
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.sin (L * dictionaryFrequency n L) = 0 := by
  rw [dictionaryFrequency_mul_L hL n]
  simpa using Real.sin_add_int_mul_two_pi 0 n

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
  have hfreq : dictionaryFrequency (-n) L = -dictionaryFrequency n L := by
    unfold dictionaryFrequency
    push_cast
    ring
  have h := cos_dictionaryPole_shift_plus hL (-n)
  rw [hfreq] at h
  simpa [sub_eq_add_neg] using h

private theorem one_sub_cosh_half_eq_neg_two_sinh_sq (L : ℝ) :
    1 - Real.cosh (L / 2) = -2 * Real.sinh (L / 4) ^ 2 := by
  have h1 := Real.cosh_two_mul (L / 4)
  have h2 := Real.cosh_sq_sub_sinh_sq (L / 4)
  rw [show 2 * (L / 4) = L / 2 by ring] at h1
  nlinarith

private theorem shifted_reciprocal_sq_sum (a : ℝ) :
    ((Complex.I / 2 + (a : ℂ)) ^ 2)⁻¹ +
        ((Complex.I / 2 - (a : ℂ)) ^ 2)⁻¹ =
      2 * ((a : ℂ) ^ 2 - 1 / 4) /
        (((a : ℂ) ^ 2 + 1 / 4) ^ 2) := by
  have hp : Complex.I / 2 + (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hm : Complex.I / 2 - (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hsum :
      (Complex.I / 2 + (a : ℂ)) ^ 2 +
          (Complex.I / 2 - (a : ℂ)) ^ 2 =
        2 * ((a : ℂ) ^ 2 - 1 / 4) := by
    calc
      (Complex.I / 2 + (a : ℂ)) ^ 2 +
          (Complex.I / 2 - (a : ℂ)) ^ 2 =
          2 * (Complex.I / 2) ^ 2 + 2 * (a : ℂ) ^ 2 := by ring
      _ = 2 * ((a : ℂ) ^ 2 - 1 / 4) := by
        rw [Complex.I_sq]
        ring
  have hprodBase :
      (Complex.I / 2 + (a : ℂ)) *
          (Complex.I / 2 - (a : ℂ)) =
        -((a : ℂ) ^ 2 + 1 / 4) := by
    calc
      (Complex.I / 2 + (a : ℂ)) *
          (Complex.I / 2 - (a : ℂ)) =
          (Complex.I / 2) ^ 2 - (a : ℂ) ^ 2 := by ring
      _ = -((a : ℂ) ^ 2 + 1 / 4) := by
        rw [Complex.I_sq]
        ring
  have hprod :
      (Complex.I / 2 + (a : ℂ)) ^ 2 *
          (Complex.I / 2 - (a : ℂ)) ^ 2 =
        ((a : ℂ) ^ 2 + 1 / 4) ^ 2 := by
    rw [← mul_pow, hprodBase]
    ring
  calc
    ((Complex.I / 2 + (a : ℂ)) ^ 2)⁻¹ +
        ((Complex.I / 2 - (a : ℂ)) ^ 2)⁻¹ =
      ((Complex.I / 2 - (a : ℂ)) ^ 2 +
          (Complex.I / 2 + (a : ℂ)) ^ 2) /
        ((Complex.I / 2 + (a : ℂ)) ^ 2 *
          (Complex.I / 2 - (a : ℂ)) ^ 2) := by
      field_simp [hp, hm] <;> ring
    _ = 2 * ((a : ℂ) ^ 2 - 1 / 4) /
        (((a : ℂ) ^ 2 + 1 / 4) ^ 2) := by
      rw [add_comm, hsum, hprod]

private theorem shifted_tent_pole_algebra
    (L a s : ℝ) (hL : L ≠ 0) :
    2 * ((-2 * s ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 + (a : ℂ)) ^ 2) +
      2 * ((-2 * s ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 - (a : ℂ)) ^ 2) =
      ((8 * s ^ 2 / L * (1 / 4 - a ^ 2) / (a ^ 2 + 1 / 4) ^ 2 : ℝ) : ℂ) := by
  have hp : Complex.I / 2 + (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hm : Complex.I / 2 - (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  calc
    2 * ((-2 * s ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 + (a : ℂ)) ^ 2) +
      2 * ((-2 * s ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 - (a : ℂ)) ^ 2) =
        (-4 * (s : ℂ) ^ 2 / (L : ℂ)) *
          (((Complex.I / 2 + (a : ℂ)) ^ 2)⁻¹ +
            ((Complex.I / 2 - (a : ℂ)) ^ 2)⁻¹) := by
      field_simp [hL, hp, hm] <;> ring
    _ = (-4 * (s : ℂ) ^ 2 / (L : ℂ)) *
        (2 * ((a : ℂ) ^ 2 - 1 / 4) /
          (((a : ℂ) ^ 2 + 1 / 4) ^ 2)) := by
      rw [shifted_reciprocal_sq_sum a]
    _ = ((8 * s ^ 2 / L * (1 / 4 - a ^ 2) /
          (a ^ 2 + 1 / 4) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring

private theorem diagonal_pole_real_algebra
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    8 * Real.sinh (L / 4) ^ 2 / L *
        (1 / 4 - dictionaryFrequency n L ^ 2) /
        (dictionaryFrequency n L ^ 2 + 1 / 4) ^ 2 =
      poleComponent n n L := by
  have hd :
      0 < L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
    positivity
  unfold dictionaryFrequency poleComponent
  dsimp
  push_cast
  field_simp [hL.ne', ne_of_gt hd] <;> ring

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
  calc
    2 * ((-2 * Real.sinh (L / 4) ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 + (dictionaryFrequency n L : ℂ)) ^ 2) +
      2 * ((-2 * Real.sinh (L / 4) ^ 2 : ℝ) : ℂ) /
          ((L : ℂ) * (Complex.I / 2 - (dictionaryFrequency n L : ℂ)) ^ 2) =
        ((8 * Real.sinh (L / 4) ^ 2 / L *
          (1 / 4 - dictionaryFrequency n L ^ 2) /
          (dictionaryFrequency n L ^ 2 + 1 / 4) ^ 2 : ℝ) : ℂ) :=
      shifted_tent_pole_algebra L (dictionaryFrequency n L)
        (Real.sinh (L / 4)) hL.ne'
    _ = ((poleComponent n n L : ℝ) : ℂ) := by
      exact_mod_cast diagonal_pole_real_algebra hL n

end Zeta23.CCM
