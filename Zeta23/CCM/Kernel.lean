import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

namespace Zeta23.CCM

open Complex

/-- The one-sided truncated-character correlation used by the finite CCM matrix.
The argument order `(n,m)` matches matrix-entry order in the research implementation. -/
def qBasis (n m : ℤ) (y L : ℝ) : ℝ :=
  if h : n = m then
    2 * (1 - y / L) * Real.cos (2 * Real.pi * (n : ℝ) * y / L)
  else
    (Real.sin (2 * Real.pi * (n : ℝ) * y / L)
      - Real.sin (2 * Real.pi * (m : ℝ) * y / L)) /
      (Real.pi * ((m - n : ℤ) : ℝ))

/-- Even two-sided compactly truncated CCM/Weil test. -/
def kernel (n m : ℤ) (L : ℝ) : ℝ → ℂ := fun y =>
  if |y| ≤ L then (qBasis n m |y| L : ℂ) else 0

@[simp] theorem qBasis_zero (n m : ℤ) (L : ℝ) :
    qBasis n m 0 L = if n = m then 2 else 0 := by
  by_cases h : n = m
  · simp [qBasis, h]
  · simp [qBasis, h]

@[simp] theorem kernel_neg (n m : ℤ) (L y : ℝ) :
    kernel n m L (-y) = kernel n m L y := by
  simp [kernel, abs_neg]

@[simp] theorem kernel_zero {L : ℝ} (hL : 0 ≤ L) (n m : ℤ) :
    kernel n m L 0 = if n = m then (2 : ℂ) else 0 := by
  simp [kernel, hL, qBasis_zero]

/-- Outside the aperture the two-sided kernel vanishes identically. -/
theorem kernel_eq_zero_of_lt_abs {n m : ℤ} {L y : ℝ} (h : L < |y|) :
    kernel n m L y = 0 := by
  simp [kernel, not_le.mpr h]

end Zeta23.CCM
