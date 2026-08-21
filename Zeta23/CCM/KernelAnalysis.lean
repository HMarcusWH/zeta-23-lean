import Zeta23.CCM.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set

/-- For fixed Fourier indices and aperture, the one-sided CCM basis is continuous in its
physical-space argument. -/
theorem qBasis_continuous (n m : ℤ) (L : ℝ) :
    Continuous (fun y : ℝ => qBasis n m y L) := by
  by_cases h : n = m
  · simp [qBasis, h]
    fun_prop
  · simp [qBasis, h]
    fun_prop

/-- The one-sided basis vanishes at the aperture endpoint.  This endpoint cancellation is
what makes the compactly truncated two-sided kernel continuous. -/
theorem qBasis_aperture_eq_zero {L : ℝ} (hL : L ≠ 0) (n m : ℤ) :
    qBasis n m L L = 0 := by
  by_cases h : n = m
  · subst m
    simp [qBasis, hL]
  · unfold qBasis
    rw [if_neg h]
    have hn : 2 * Real.pi * (n : ℝ) * L / L = (((2 * n : ℤ) : ℝ) * Real.pi) := by
      field_simp [hL]
      push_cast
      ring
    have hm : 2 * Real.pi * (m : ℝ) * L / L = (((2 * m : ℤ) : ℝ) * Real.pi) := by
      field_simp [hL]
      push_cast
      ring
    rw [hn, hm]
    simp

/-- The pointwise support of the two-sided CCM kernel is contained in its closed aperture. -/
theorem kernel_support_subset {L : ℝ} (hL : 0 ≤ L) (n m : ℤ) :
    Function.support (kernel n m L) ⊆ Set.Icc (-L) L := by
  intro y hy
  have habs : |y| ≤ L := by
    by_contra hnot
    have hlt : L < |y| := lt_of_not_ge hnot
    exact hy (kernel_eq_zero_of_lt_abs (n := n) (m := m) (L := L) (y := y) hlt)
  exact abs_le.mp habs

/-- The CCM kernel has compact support for every nonnegative aperture. -/
theorem kernel_hasCompactSupport {L : ℝ} (hL : 0 ≤ L) (n m : ℤ) :
    HasCompactSupport (kernel n m L) := by
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-L) L)) ?_
  intro y hy
  apply kernel_eq_zero_of_lt_abs (n := n) (m := m) (L := L) (y := y)
  by_contra hnot
  have habs : |y| ≤ L := le_of_not_gt hnot
  exact hy (abs_le.mp habs)

/-- For positive aperture the truncated two-sided CCM kernel is continuous, including at the
cutoff points `±L`. -/
theorem kernel_continuous {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Continuous (kernel n m L) := by
  unfold kernel
  apply Continuous.if_le
  · exact Complex.continuous_ofReal.comp ((qBasis_continuous n m L).comp continuous_abs)
  · exact continuous_const
  · exact continuous_abs
  · exact continuous_const
  · intro y hy
    have hL0 : L ≠ 0 := ne_of_gt hL
    rw [hy]
    simp [qBasis_aperture_eq_zero hL0]

/-- Continuous compact support makes every positive-aperture CCM kernel Bochner-integrable. -/
theorem kernel_integrable {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (kernel n m L) :=
  (kernel_continuous hL n m).integrable_of_hasCompactSupport
    (kernel_hasCompactSupport hL.le n m)

/-- The CCM kernel is real-valued even though it is represented as a complex-valued Weil test. -/
@[simp] theorem kernel_im (n m : ℤ) (L y : ℝ) :
    (kernel n m L y).im = 0 := by
  unfold kernel
  split <;> simp

end Zeta23.CCM
