import Zeta23.CCM.DictionaryTent

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-! # Exact transform of the canonical dictionary tent

The proof stays in the project's native complex-frequency convention

`paperFT f z = ∫ y, f y * exp (I*z*y)`.

The affine branches are expanded into the zeroth and first exponential moments.
The first moment is evaluated from the explicit primitive

`((y/c) - 1/c^2) * exp(c*y)`.

The pinned Mathlib revision exposes two definitionally equal real scalar-action
paths on `ℂ` once inner-product imports are present.  The primitive derivative is
therefore elaborated under `with_reducible_and_instances`, exactly as Mathlib's
own instance-diamond regression tests do.  The value at `z=0` is computed
separately from the real triangle area and then coerced to `ℂ`.
-/

private def mulExpPrimitive (c : ℂ) (y : ℝ) : ℂ :=
  ((y : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * y)

private theorem hasDerivAt_mulExpPrimitive
    {c : ℂ} (hc : c ≠ 0) (y : ℝ) :
    HasDerivAt (mulExpPrimitive c)
      ((y : ℂ) * Complex.exp (c * y)) y := by
  have hdiv : HasDerivAt (fun t : ℝ => (t : ℂ) / c) (1 / c) y := by
    with_reducible_and_instances
      simpa only [mul_one] using
        (((hasDerivAt_id (y : ℂ)).div_const c).comp_ofReal)
  have hleft : HasDerivAt
      (fun t : ℝ => (t : ℂ) / c - 1 / c ^ 2) (1 / c) y :=
    hdiv.sub_const _
  have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c y := by
    with_reducible_and_instances
      simpa only [mul_one] using
        (((hasDerivAt_id (y : ℂ)).const_mul c).comp_ofReal)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t))
      (c * Complex.exp (c * y)) y := by
    with_reducible_and_instances
      convert (Complex.hasDerivAt_exp (c * (y : ℂ))).comp y hlin using 1
      · ring
      · ring
  have hprod := hleft.mul hexp
  change HasDerivAt
    (fun t : ℝ => ((t : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * t))
    ((y : ℂ) * Complex.exp (c * y)) y
  with_reducible_and_instances
    convert hprod using 1
    field_simp [hc]
    ring

private theorem intervalIntegral_mul_exp
    {a b : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ y in a..b, (y : ℂ) * Complex.exp (c * y)) =
      mulExpPrimitive c b - mulExpPrimitive c a := by
  have hint : IntervalIntegrable
      (fun y : ℝ => (y : ℂ) * Complex.exp (c * y)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := mulExpPrimitive c)
    (f' := fun y : ℝ => (y : ℂ) * Complex.exp (c * y))
    (fun y _ => hasDerivAt_mulExpPrimitive hc y) hint

private theorem intervalIntegral_positiveTent_exp
    {L : ℝ} (hL : 0 < L) {c : ℂ} (hc : c ≠ 0) :
    (∫ y in 0..L, ((1 - y / L : ℝ) : ℂ) * Complex.exp (c * y)) =
      -1 / c + (Complex.exp (c * L) - 1) / ((L : ℂ) * c ^ 2) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hLc0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  have hExpCont : Continuous (fun y : ℝ => Complex.exp (c * y)) := by fun_prop
  have hMulCont : Continuous
      (fun y : ℝ => (y : ℂ) * Complex.exp (c * y)) := by fun_prop
  have hdecomp :
      (∫ y in 0..L, ((1 - y / L : ℝ) : ℂ) * Complex.exp (c * y)) =
        (∫ y in 0..L, Complex.exp (c * y)) -
          ∫ y in 0..L, (1 / (L : ℂ)) * ((y : ℂ) * Complex.exp (c * y)) := by
    rw [← intervalIntegral.integral_sub
      (hExpCont.intervalIntegrable 0 L)
      ((hMulCont.const_mul (1 / (L : ℂ))).intervalIntegrable 0 L)]
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    push_cast
    field_simp [hL0, hLc0]
    ring
  rw [hdecomp, integral_exp_mul_complex hc,
    intervalIntegral.integral_const_mul, intervalIntegral_mul_exp hc]
  simp [mulExpPrimitive]
  field_simp [hL0, hLc0, hc]

private theorem intervalIntegral_negativeTent_exp
    {L : ℝ} (hL : 0 < L) {c : ℂ} (hc : c ≠ 0) :
    (∫ y in -L..0, ((1 + y / L : ℝ) : ℂ) * Complex.exp (c * y)) =
      1 / c + (Complex.exp (-(c * L)) - 1) / ((L : ℂ) * c ^ 2) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hLc0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  have hExpCont : Continuous (fun y : ℝ => Complex.exp (c * y)) := by fun_prop
  have hMulCont : Continuous
      (fun y : ℝ => (y : ℂ) * Complex.exp (c * y)) := by fun_prop
  have hdecomp :
      (∫ y in -L..0, ((1 + y / L : ℝ) : ℂ) * Complex.exp (c * y)) =
        (∫ y in -L..0, Complex.exp (c * y)) +
          ∫ y in -L..0, (1 / (L : ℂ)) * ((y : ℂ) * Complex.exp (c * y)) := by
    rw [← intervalIntegral.integral_add
      (hExpCont.intervalIntegrable (-L) 0)
      ((hMulCont.const_mul (1 / (L : ℂ))).intervalIntegrable (-L) 0)]
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    push_cast
    field_simp [hL0, hLc0]
    ring
  rw [hdecomp, integral_exp_mul_complex hc,
    intervalIntegral.integral_const_mul, intervalIntegral_mul_exp hc]
  simp [mulExpPrimitive]
  field_simp [hL0, hLc0, hc]

private theorem intervalIntegral_positiveTent_area_real
    {L : ℝ} (hL : 0 < L) :
    (∫ y in 0..L, (1 - y / L : ℝ)) = L / 2 := by
  have hdiv : IntervalIntegrable (fun y : ℝ => y / L) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub intervalIntegrable_const hdiv,
    integral_one, intervalIntegral.integral_div, integral_id]
  field_simp [hL.ne']
  ring

private theorem intervalIntegral_negativeTent_area_real
    {L : ℝ} (hL : 0 < L) :
    (∫ y in -L..0, (1 + y / L : ℝ)) = L / 2 := by
  have hdiv : IntervalIntegrable (fun y : ℝ => y / L) volume (-L) 0 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const hdiv,
    integral_one, intervalIntegral.integral_div, integral_id]
  field_simp [hL.ne']
  ring

private theorem intervalIntegral_positiveTent_area
    {L : ℝ} (hL : 0 < L) :
    (∫ y in 0..L, ((1 - y / L : ℝ) : ℂ)) = (L / 2 : ℝ) := by
  rw [intervalIntegral.integral_ofReal, intervalIntegral_positiveTent_area_real hL]

private theorem intervalIntegral_negativeTent_area
    {L : ℝ} (hL : 0 < L) :
    (∫ y in -L..0, ((1 + y / L : ℝ) : ℂ)) = (L / 2 : ℝ) := by
  rw [intervalIntegral.integral_ofReal, intervalIntegral_negativeTent_area_real hL]

private theorem tentExp_support_subset_Ioc
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Function.support
      (fun y : ℝ => dictionaryTent L y * Complex.exp (I * z * y)) ⊆
      Ioc (-L) L := by
  intro y hy
  have ht : dictionaryTent L y ≠ 0 := by
    intro hzero
    apply hy
    change dictionaryTent L y * Complex.exp (I * z * y) = 0
    rw [hzero, zero_mul]
  have hmem := dictionaryTent_support_subset_Ioo hL ht
  exact ⟨hmem.1, hmem.2.le⟩

/-- Whole-line paper transform reduced exactly to the aperture interval. -/
theorem paperFT_dictionaryTent_eq_interval
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTent L) z =
      ∫ y in -L..L, dictionaryTent L y * Complex.exp (I * z * y) := by
  rw [Zeta23.paperFT_def]
  exact (intervalIntegral.integral_eq_integral_of_support_subset
    (tentExp_support_subset_Ioc hL z)).symm

/-- Exact transform value at the removable node `z=0`, proved from the triangle area. -/
theorem paperFT_dictionaryTent_zero
    {L : ℝ} (hL : 0 < L) :
    Zeta23.paperFT (dictionaryTent L) 0 = (L : ℂ) := by
  rw [paperFT_dictionaryTent_eq_interval hL]
  have hcont : Continuous (fun y : ℝ => dictionaryTent L y) :=
    continuous_dictionaryTent L
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hcont.intervalIntegrable (-L) 0) (hcont.intervalIntegrable 0 L)
  have hleft :
      (∫ y in -L..0, dictionaryTent L y) =
        ∫ y in -L..0, ((1 + y / L : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    rw [dictionaryTent_eq_one_add_div_of_mem_Icc hL]
    simpa [uIcc_of_le (by linarith : -L ≤ (0 : ℝ))] using hy
  have hright :
      (∫ y in 0..L, dictionaryTent L y) =
        ∫ y in 0..L, ((1 - y / L : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    rw [dictionaryTent_eq_one_sub_div_of_mem_Icc hL]
    simpa [uIcc_of_le hL.le] using hy
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [← hsplit, hleft, hright,
    intervalIntegral_negativeTent_area hL,
    intervalIntegral_positiveTent_area hL]
  push_cast
  ring

/-- Exact complex-frequency transform away from the removable node. -/
theorem paperFT_dictionaryTent_of_ne_zero
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (dictionaryTent L) z =
      2 * (1 - Complex.cos ((L : ℂ) * z)) / ((L : ℂ) * z ^ 2) := by
  rw [paperFT_dictionaryTent_eq_interval hL]
  let c : ℂ := I * z
  have hc : c ≠ 0 := mul_ne_zero I_ne_zero hz
  have hcont : Continuous
      (fun y : ℝ => dictionaryTent L y * Complex.exp (c * y)) := by
    dsimp [c]
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hcont.intervalIntegrable (-L) 0) (hcont.intervalIntegrable 0 L)
  have hleft :
      (∫ y in -L..0, dictionaryTent L y * Complex.exp (c * y)) =
        ∫ y in -L..0, ((1 + y / L : ℝ) : ℂ) * Complex.exp (c * y) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    change dictionaryTent L y * Complex.exp (c * y) =
      ((1 + y / L : ℝ) : ℂ) * Complex.exp (c * y)
    rw [dictionaryTent_eq_one_add_div_of_mem_Icc hL]
    simpa [uIcc_of_le (by linarith : -L ≤ (0 : ℝ))] using hy
  have hright :
      (∫ y in 0..L, dictionaryTent L y * Complex.exp (c * y)) =
        ∫ y in 0..L, ((1 - y / L : ℝ) : ℂ) * Complex.exp (c * y) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    change dictionaryTent L y * Complex.exp (c * y) =
      ((1 - y / L : ℝ) : ℂ) * Complex.exp (c * y)
    rw [dictionaryTent_eq_one_sub_div_of_mem_Icc hL]
    simpa [uIcc_of_le hL.le] using hy
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have harg : c * (L : ℂ) = ((L : ℂ) * z) * I := by
    dsimp [c]
    ring
  have hc_sq : c ^ 2 = -(z ^ 2) := by
    dsimp [c]
    rw [mul_pow, I_sq]
    ring
  change (∫ y in -L..L,
    dictionaryTent L y * Complex.exp (c * y)) = _
  rw [← hsplit, hleft, hright,
    intervalIntegral_negativeTent_exp hL hc,
    intervalIntegral_positiveTent_exp hL hc]
  rw [harg, hc_sq]
  unfold Complex.cos
  have hnegI : -(((L : ℂ) * z) * I) = (-(L : ℂ) * z) * I := by
    ring
  rw [hnegI]
  field_simp [hL0, hz] <;> ring

/-- Total closed form, with the removable node represented explicitly. -/
def dictionaryTentTransformClosed (L : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then (L : ℂ)
  else 2 * (1 - Complex.cos ((L : ℂ) * z)) / ((L : ℂ) * z ^ 2)

/-- The canonical tent transform equals its explicit total closed form. -/
theorem paperFT_dictionaryTent
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTent L) z =
      dictionaryTentTransformClosed L z := by
  by_cases hz : z = 0
  · subst z
    simp [dictionaryTentTransformClosed, paperFT_dictionaryTent_zero hL]
  · simp [dictionaryTentTransformClosed, hz,
      paperFT_dictionaryTent_of_ne_zero hL hz]

end Zeta23.CCM