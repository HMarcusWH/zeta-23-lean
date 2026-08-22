import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-!
# Canonical tent channel of the finite dictionary

PR #38 proved that the rank-one-regularized residual is a `C_c^2` test.  The
only remaining nonsmooth channel in the real finite dictionary is therefore the
universal tent

`tau_L(y) = max 0 (1 - |y| / L)`.

This file keeps that object literally identical to the already-used
`dictionaryApertureCoord`; no competing normalization is introduced.  All
support statements require `0 < L`, because the clamped-coordinate expression
is not compactly supported for negative aperture.

No explicit formula is invoked here.
-/

/-- Complex-valued canonical tent in the codomain used by `Zeta23.paperFT`. -/
def dictionaryTent (L : ℝ) : ℝ → ℂ :=
  fun y => (dictionaryApertureCoord L y : ℂ)

@[simp] theorem dictionaryTent_apply (L y : ℝ) :
    dictionaryTent L y = (dictionaryApertureCoord L y : ℂ) := rfl

@[simp] theorem dictionaryTent_zero (L : ℝ) :
    dictionaryTent L 0 = 1 := by
  simp [dictionaryTent, dictionaryApertureCoord]

@[simp] theorem dictionaryTent_neg (L y : ℝ) :
    dictionaryTent L (-y) = dictionaryTent L y := by
  simp [dictionaryTent, dictionaryApertureCoord]

@[simp] theorem dictionaryTent_right_endpoint {L : ℝ} (hL : 0 < L) :
    dictionaryTent L L = 0 := by
  simp [dictionaryTent, dictionaryApertureCoord, abs_of_pos hL, hL.ne']

@[simp] theorem dictionaryTent_left_endpoint {L : ℝ} (hL : 0 < L) :
    dictionaryTent L (-L) = 0 := by
  rw [dictionaryTent_neg]
  exact dictionaryTent_right_endpoint hL

/-- Inside a positive aperture the clamped coordinate is the ordinary affine tent. -/
theorem dictionaryTent_eq_one_sub_abs_div_of_abs_le
    {L y : ℝ} (hL : 0 < L) (hy : |y| ≤ L) :
    dictionaryTent L y = ((1 - |y| / L : ℝ) : ℂ) := by
  have hdiv : |y| / L ≤ 1 := (div_le_one hL).2 hy
  have hnonneg : 0 ≤ 1 - |y| / L := sub_nonneg.mpr hdiv
  simp [dictionaryTent, dictionaryApertureCoord, max_eq_right hnonneg]

/-- Outside a positive aperture the tent vanishes. -/
theorem dictionaryTent_eq_zero_of_lt_abs
    {L y : ℝ} (hL : 0 < L) (hy : L < |y|) :
    dictionaryTent L y = 0 := by
  have hdiv : 1 < |y| / L := (one_lt_div hL).2 hy
  have hnonpos : 1 - |y| / L ≤ 0 := le_of_lt (sub_neg.mpr hdiv)
  simp [dictionaryTent, dictionaryApertureCoord, max_eq_left hnonpos]

/-- The support of the tent lies strictly between the two zero endpoints. -/
theorem dictionaryTent_support_subset_Ioo
    {L : ℝ} (hL : 0 < L) :
    Function.support (dictionaryTent L) ⊆ Ioo (-L) L := by
  intro y hy
  have habs_le : |y| ≤ L := by
    by_contra h
    have hlt : L < |y| := lt_of_not_ge h
    exact hy (dictionaryTent_eq_zero_of_lt_abs hL hlt)
  have habs_ne : |y| ≠ L := by
    intro hEq
    have hzero : dictionaryTent L y = 0 := by
      rw [dictionaryTent_eq_one_sub_abs_div_of_abs_le hL habs_le, hEq]
      simp [hL.ne']
    exact hy hzero
  have habs_lt : |y| < L := lt_of_le_of_ne habs_le habs_ne
  exact abs_lt.mp habs_lt

/-- Closed-interval support form used by compact-support APIs. -/
theorem dictionaryTent_support_subset_Icc
    {L : ℝ} (hL : 0 < L) :
    Function.support (dictionaryTent L) ⊆ Icc (-L) L :=
  (dictionaryTent_support_subset_Ioo hL).trans Ioo_subset_Icc_self

/-- The canonical tent has compact support for every positive aperture. -/
theorem dictionaryTent_hasCompactSupport
    {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (dictionaryTent L) := by
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  by_contra hzero
  exact hy (dictionaryTent_support_subset_Icc hL hzero)

@[fun_prop] theorem continuous_dictionaryTent (L : ℝ) :
    Continuous (dictionaryTent L) := by
  unfold dictionaryTent
  fun_prop

/-- Compact support plus continuity gives the whole-line integrability needed by `paperFT`. -/
theorem integrable_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (dictionaryTent L) :=
  (continuous_dictionaryTent L).integrable_of_hasCompactSupport
    (dictionaryTent_hasCompactSupport hL)

/-- Positive-half affine form. -/
theorem dictionaryTent_eq_one_sub_div_of_mem_Icc
    {L y : ℝ} (hL : 0 < L) (hy : y ∈ Icc (0 : ℝ) L) :
    dictionaryTent L y = ((1 - y / L : ℝ) : ℂ) := by
  rw [dictionaryTent_eq_one_sub_abs_div_of_abs_le hL]
  · rw [abs_of_nonneg hy.1]
  · rw [abs_of_nonneg hy.1]
    exact hy.2

/-- Negative-half affine form. -/
theorem dictionaryTent_eq_one_add_div_of_mem_Icc
    {L y : ℝ} (hL : 0 < L) (hy : y ∈ Icc (-L) (0 : ℝ)) :
    dictionaryTent L y = ((1 + y / L : ℝ) : ℂ) := by
  rw [dictionaryTent_eq_one_sub_abs_div_of_abs_le hL]
  · rw [abs_of_nonpos hy.2]
    push_cast
    ring
  · rw [abs_of_nonpos hy.2]
    linarith [hy.1]

end Zeta23.CCM
