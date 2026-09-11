import Zeta23.CCM.CanonicalApertureHolomorphy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1d: scalar logarithm branch control

The removable aperture factor is analytic on `complexArchSafeStrip`.  To use
the principal logarithm on the same connected strip we must also prove that the
factor never meets the branch cut.  The stronger statement below shows that
its real part is strictly positive throughout the strip.

Away from zero the production factor is

  z * (exp z + 1) / (exp z - 1).

Writing `z = x + i y` gives the exact real-part numerator

  x * (exp(x)^2 - 1) + 2 * y * exp(x) * sin(y).

Both summands are nonnegative for `|y| < pi`; at least one is strictly positive
when `z != 0`.  The removable value at zero is `2`.

No determinant, sign of a CCM quadratic form, negative-root exclusion, or RH
claim is made here.
-/

private theorem exp_ne_one_of_mem_complexArchSafeStrip_of_ne_zero
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) (hz0 : z ≠ 0) :
    Complex.exp z ≠ 1 := by
  intro hexp
  have hb : -Real.pi < z.im ∧ z.im < Real.pi := abs_lt.mp hz
  have hzeroLower : -Real.pi < (0 : ℂ).im := by
    simpa using Real.pi_pos
  have hzeroUpper : (0 : ℂ).im ≤ Real.pi := by
    simp [Real.pi_pos.le]
  have hEq : z = 0 :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      hb.1 hb.2.le hzeroLower hzeroUpper (by simpa using hexp)
  exact hz0 hEq

private theorem real_mul_exp_sq_sub_one_pos
    {x : ℝ} (hx : x ≠ 0) :
    0 < x * (Real.exp x ^ 2 - 1) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have he0 : 0 < Real.exp x := Real.exp_pos x
    have he1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hxneg
    have hesq : Real.exp x ^ 2 < 1 := by nlinarith
    nlinarith
  · have he0 : 0 < Real.exp x := Real.exp_pos x
    have he1 : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hxpos
    have hesq : 1 < Real.exp x ^ 2 := by nlinarith
    nlinarith

private theorem real_mul_sin_nonneg_of_abs_lt_pi
    {y : ℝ} (hy : |y| < Real.pi) :
    0 ≤ y * Real.sin y := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rcases lt_or_gt_of_ne hy0 with hyneg | hypos
    · have hsin : Real.sin y < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hyneg (abs_lt.mp hy).1
      exact mul_nonneg_of_nonpos_of_nonpos hyneg.le hsin.le
    · have hsin : 0 < Real.sin y :=
        Real.sin_pos_of_pos_of_lt_pi hypos (abs_lt.mp hy).2
      exact mul_nonneg hypos.le hsin.le

private theorem real_mul_sin_pos_of_abs_lt_pi_of_ne_zero
    {y : ℝ} (hy : |y| < Real.pi) (hy0 : y ≠ 0) :
    0 < y * Real.sin y := by
  rcases lt_or_gt_of_ne hy0 with hyneg | hypos
  · exact mul_pos_of_neg_of_neg hyneg
      (Real.sin_neg_of_neg_of_neg_pi_lt hyneg (abs_lt.mp hy).1)
  · exact mul_pos hypos
      (Real.sin_pos_of_pos_of_lt_pi hypos (abs_lt.mp hy).2)

/-- Exact real-part formula for the production scalar factor away from its
exponential denominator zeros. -/
theorem complexApertureScalarFactor_re_formula
    {z : ℂ} (hexp : Complex.exp z ≠ 1) :
    (complexApertureScalarFactor z).re =
      (z.re * (Real.exp z.re ^ 2 - 1) +
          2 * z.im * Real.exp z.re * Real.sin z.im) /
        Complex.normSq (Complex.exp z - 1) := by
  have hsub : Complex.exp z - 1 ≠ 0 := sub_ne_zero.mpr hexp
  have hden : Complex.normSq (Complex.exp z - 1) ≠ 0 :=
    (Complex.normSq_pos.mpr hsub).ne'
  unfold complexApertureScalarFactor
  rw [Complex.mul_re, Complex.div_re, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.exp_re, Complex.exp_im,
    add_zero, sub_zero]
  field_simp [hden]
  nlinarith [Real.sin_sq_add_cos_sq z.im]

/-- The production scalar factor has strictly positive real part throughout the
punctured safe strip. -/
theorem complexApertureScalarFactor_re_pos_of_mem_strip_of_ne_zero
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) (hz0 : z ≠ 0) :
    0 < (complexApertureScalarFactor z).re := by
  have hexp := exp_ne_one_of_mem_complexArchSafeStrip_of_ne_zero hz hz0
  rw [complexApertureScalarFactor_re_formula hexp]
  have hden : 0 < Complex.normSq (Complex.exp z - 1) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hexp)
  have hysin : 0 ≤ z.im * Real.sin z.im :=
    real_mul_sin_nonneg_of_abs_lt_pi hz
  have hsecond :
      0 ≤ 2 * z.im * Real.exp z.re * Real.sin z.im := by
    have he : 0 < Real.exp z.re := Real.exp_pos z.re
    have htmp : 0 ≤ 2 * Real.exp z.re * (z.im * Real.sin z.im) :=
      mul_nonneg (mul_nonneg (by norm_num) he.le) hysin
    nlinarith
  have hnum :
      0 < z.re * (Real.exp z.re ^ 2 - 1) +
        2 * z.im * Real.exp z.re * Real.sin z.im := by
    by_cases hx0 : z.re = 0
    · have hy0 : z.im ≠ 0 := by
        intro hy0
        apply hz0
        apply Complex.ext <;> simp [hx0, hy0]
      have hypos : 0 < z.im * Real.sin z.im :=
        real_mul_sin_pos_of_abs_lt_pi_of_ne_zero hz hy0
      have he : 0 < Real.exp z.re := Real.exp_pos z.re
      have hsecondPos :
          0 < 2 * z.im * Real.exp z.re * Real.sin z.im := by
        have htmp : 0 < 2 * Real.exp z.re * (z.im * Real.sin z.im) :=
          mul_pos (mul_pos (by norm_num) he) hypos
        nlinarith
      rw [hx0]
      norm_num at hsecondPos ⊢
      exact hsecondPos
    · have hfirst : 0 < z.re * (Real.exp z.re ^ 2 - 1) :=
        real_mul_exp_sq_sub_one_pos hx0
      linarith
  exact div_pos hnum hden

/-- The removable factor lies in the principal logarithm slit plane throughout
the full safe strip. -/
theorem complexApertureScalarFactorRemovable_mem_slitPlane_of_mem_strip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    complexApertureScalarFactorRemovable z ∈ Complex.slitPlane := by
  by_cases hz0 : z = 0
  · subst z
    exact complexApertureScalarFactorRemovable_zero_mem_slitPlane
  · rw [complexApertureScalarFactorRemovable_eq_complexApertureScalarFactor hz0,
      Complex.mem_slitPlane_iff]
    exact Or.inl
      (complexApertureScalarFactor_re_pos_of_mem_strip_of_ne_zero hz hz0)

/-- The principal logarithm of the removable scalar factor is analytic on the
entire common strip. -/
theorem analyticOnNhd_log_complexApertureScalarFactorRemovable_strip :
    AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.log (complexApertureScalarFactorRemovable z))
      complexArchSafeStrip := by
  intro z hz
  exact (analyticOnNhd_complexApertureScalarFactorRemovable_strip z hz).clog
    (complexApertureScalarFactorRemovable_mem_slitPlane_of_mem_strip hz)

/-- Consequently the removable scalar remainder is analytic on the entire
common strip. -/
theorem analyticOnNhd_complexApertureScalarRemainderRemovable_strip :
    AnalyticOnNhd ℂ
      complexApertureScalarRemainderRemovable
      complexArchSafeStrip := by
  intro z hz
  unfold complexApertureScalarRemainderRemovable
  exact (analyticOnNhd_log_complexApertureScalarFactorRemovable_strip z hz).sub
    analyticAt_const

end Zeta23.CCM

#print axioms Zeta23.CCM.complexApertureScalarFactor_re_formula
#print axioms Zeta23.CCM.complexApertureScalarFactor_re_pos_of_mem_strip_of_ne_zero
#print axioms Zeta23.CCM.complexApertureScalarFactorRemovable_mem_slitPlane_of_mem_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexApertureScalarRemainderRemovable_strip
