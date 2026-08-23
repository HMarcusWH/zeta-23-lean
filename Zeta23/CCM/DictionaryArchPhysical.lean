import Zeta23.CCM.DictionaryPoleSource

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-! # Physical-space normalization of the dictionary archimedean channel

This file is deliberately zero-free.  It isolates the finite-part physical-space
functional whose later gamma/digamma bridge must reproduce.  The purpose is to
lock the source and diagonal normalization independently of that analytic bridge.
-/

/-- Physical-space archimedean functional for a test supported in `[-L,L]`.
The subtraction by `k 0 * exp (-x/2)` is the finite-part regularization at the
origin; `wCorrection` is the remaining aperture-dependent constant. -/
def dictionaryArchPhysicalRHS (k : ℝ → ℂ) (L : ℝ) : ℂ :=
  (-2 : ℂ) * ∫ x in (0 : ℝ)..L,
      (k x - k 0 * (Real.exp (-x / 2) : ℂ)) * (archDensity x : ℂ)
    - ((2 * wCorrection L : ℝ) : ℂ) * k 0

@[simp] theorem dictionarySourceTest_zero
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionarySourceTest n L 0 = 0 := by
  unfold dictionarySourceTest
  have hcoord : dictionaryApertureCoord L 0 = 1 := by
    simp [dictionaryApertureCoord, hL.ne']
  rw [hcoord, sourcePotential_one]
  simp

/-- The physical archimedean functional on one scalar source test is exactly
`alphaL`.  This is the normalization target for the later gamma/digamma bridge. -/
theorem dictionaryArchPhysicalRHS_sourceTest
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryArchPhysicalRHS (dictionarySourceTest n L) L =
      ((alphaL n L : ℝ) : ℂ) := by
  rw [dictionaryArchPhysicalRHS, dictionarySourceTest_zero hL n]
  simp only [zero_mul, sub_zero]
  unfold alphaL
  rw [intervalIntegral.integral_ofReal]
  have hInt :
      (∫ x in (0 : ℝ)..L,
        dictionarySourceTest n L x * (archDensity x : ℂ)) =
      (((-1 / (2 * Real.pi) : ℝ) *
        ∫ x in (0 : ℝ)..L,
          (if x = 0 then
            if n = 0 then 0 else Real.pi * (n : ℝ) / L
          else
            Real.sin (2 * Real.pi * (n : ℝ) * x / L) * archDensity x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIoc_of_le hL.le] at hx
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hxne : x ≠ 0 := ne_of_gt hx.1
    have habs : |x| ≤ L := by simpa [abs_of_nonneg hx0] using hx.2
    rw [dictionarySourceTest_eq_sine_of_abs_le hL habs n]
    simp [abs_of_nonneg hx0, hxne]
    push_cast
    ring
  rw [hInt]
  push_cast
  ring

end Zeta23.CCM
