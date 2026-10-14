import Zeta23.CCM.OriginalSincWeightedPoleMoments

/-!
# The literal pole-killed native source has both signs

The original density is nonnegative. Its twice pole-killed real source j
has nonzero ordinary mass and a zero positive exponential moment, so j
cannot inherit that positivity. These are actual source statements with
no zero, detector, spectral, or numerical premise.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

private theorem originalSignSource_compact : HasCompactSupport nativeOriginalSource := by
  apply HasCompactSupport.intro
    (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
  exact fun x hx => nativeOriginalSource_supported x hx

theorem nativeOriginalSource_not_nonnegative : ¬ (∀ x : ℝ, 0 ≤ nativeOriginalSource x) := by
  intro hnonneg
  let a : ℝ := Real.exp (-UniversalSinc.fixedScale / 2)
  have ha : 0 < a := Real.exp_pos _
  have hweight : Integrable (fun x : ℝ => Real.exp (-x / 2) * nativeOriginalSource x) :=
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-x / 2))).mul
      nativeOriginalSource_contDiff.continuous).integrable_of_hasCompactSupport
        originalSignSource_compact.mul_left
  have hpoint (x : ℝ) : a * nativeOriginalSource x ≤
      Real.exp (-x / 2) * nativeOriginalSource x := by
    by_cases hx : x ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
    · apply mul_le_mul_of_nonneg_right _ (hnonneg x)
      apply Real.exp_le_exp.mpr
      linarith [hx.2]
    · rw [nativeOriginalSource_supported x hx]
      simp only [mul_zero, le_refl]
  have hbound := integral_mono (nativeOriginalSource_integrable.const_mul a) hweight hpoint
  rw [integral_const_mul, nativeOriginalSource_integral,
    nativeOriginalSource_weighted_elementary_moments.2.1] at hbound
  exact (not_le_of_gt (mul_pos ha (by norm_num : (0 : ℝ) < 1 / 16))) hbound

theorem exists_nativeOriginalSource_negative : ∃ x : ℝ, nativeOriginalSource x < 0 := by
  have h := nativeOriginalSource_not_nonnegative
  push Not at h
  exact h

theorem nativeOriginalSource_not_nonpositive : ¬ (∀ x : ℝ, nativeOriginalSource x ≤ 0) := by
  intro hnonpos
  have hbound : (∫ x : ℝ, nativeOriginalSource x) ≤ 0 := integral_nonpos hnonpos
  rw [nativeOriginalSource_integral] at hbound
  norm_num at hbound

theorem exists_nativeOriginalSource_positive : ∃ x : ℝ, 0 < nativeOriginalSource x := by
  have h := nativeOriginalSource_not_nonpositive
  push Not at h
  exact h

/-- Even the ordinary nonzero mass forbids a zero L1 source norm. -/
theorem nativeOriginalSource_integral_abs_ge_mass :
    (1 / 16 : ℝ) ≤ ∫ x : ℝ, |nativeOriginalSource x| := by
  have h := norm_integral_le_integral_norm (μ := (volume : Measure ℝ)) nativeOriginalSource
  rw [nativeOriginalSource_integral] at h
  simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalSource_not_nonnegative
#print axioms Zeta23.CCM.exists_nativeOriginalSource_negative
#print axioms Zeta23.CCM.nativeOriginalSource_not_nonpositive
#print axioms Zeta23.CCM.exists_nativeOriginalSource_positive
#print axioms Zeta23.CCM.nativeOriginalSource_integral_abs_ge_mass
