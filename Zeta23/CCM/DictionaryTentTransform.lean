import Zeta23.CCM.DictionaryTent

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-! # Exact transform of the canonical dictionary tent

The proof stays in the project's native complex-frequency convention

`paperFT f z = ∫ y, f y * exp (I*z*y)`.

For `z ≠ 0` we split at the fold `y=0` and integrate the two affine-exponential
branches. The value at `z=0` is proved separately from the geometric area; no
removable-singularity shortcut is used.
-/

private def positiveTentAffine (L : ℝ) (y : ℝ) : ℂ :=
  1 - (y : ℂ) / (L : ℂ)

private def negativeTentAffine (L : ℝ) (y : ℝ) : ℂ :=
  1 + (y : ℂ) / (L : ℂ)

private theorem hasDerivAt_positiveTentAffine
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt (positiveTentAffine L) (-(1 / (L : ℂ))) y := by
  change HasDerivAt
    (fun t : ℝ => 1 - (t : ℂ) / (L : ℂ)) (-(1 / (L : ℂ))) y
  have hdiv : HasDerivAt (fun t : ℝ => (t : ℂ) / (L : ℂ)) (1 / (L : ℂ)) y := by
    simpa only [mul_one] using
      (((hasDerivAt_id (y : ℂ)).div_const (L : ℂ)).comp_ofReal)
  exact HasDerivAt.const_sub (1 : ℂ) hdiv

private theorem hasDerivAt_negativeTentAffine
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt (negativeTentAffine L) (1 / (L : ℂ)) y := by
  change HasDerivAt
    (fun t : ℝ => 1 + (t : ℂ) / (L : ℂ)) (1 / (L : ℂ)) y
  have hdiv : HasDerivAt (fun t : ℝ => (t : ℂ) / (L : ℂ)) (1 / (L : ℂ)) y := by
    simpa only [mul_one] using
      (((hasDerivAt_id (y : ℂ)).div_const (L : ℂ)).comp_ofReal)
  exact hdiv.const_add (1 : ℂ)

private theorem hasDerivAt_exp_mul_div
    {c : ℂ} (hc : c ≠ 0) (y : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c)
      (Complex.exp (c * y)) y := by
  conv => congr
  rw [← mul_div_cancel_right₀ (Complex.exp (c * y)) hc]
  apply ((Complex.hasDerivAt_exp _).comp y _).div_const c
  simpa only [mul_one] using!
    ((hasDerivAt_id (y : ℂ)).const_mul _).comp_ofReal

private theorem intervalIntegral_positiveTent_exp
    {L : ℝ} (hL : 0 < L) {c : ℂ} (hc : c ≠ 0) :
    (∫ y in 0..L, positiveTentAffine L y * Complex.exp (c * y)) =
      -1 / c + (Complex.exp (c * L) - 1) / ((L : ℂ) * c ^ 2) := by
  have hExpCont : Continuous (fun y : ℝ => Complex.exp (c * y)) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := L)
    (u := positiveTentAffine L) (u' := fun _ : ℝ => -(1 / (L : ℂ)))
    (v := fun y : ℝ => Complex.exp (c * y) / c)
    (v' := fun y : ℝ => Complex.exp (c * y))
    (fun y _ => hasDerivAt_positiveTentAffine hL y)
    (fun y _ => hasDerivAt_exp_mul_div hc y)
    (intervalIntegrable_const)
    (hExpCont.intervalIntegrable 0 L)
  have hfun :
      (fun y : ℝ => (-(1 / (L : ℂ))) * (Complex.exp (c * y) / c)) =
        fun y : ℝ => (-(1 / (L : ℂ)) / c) * Complex.exp (c * y) := by
    funext y
    ring
  have hlast :
      (∫ y in 0..L, (-(1 / (L : ℂ))) * (Complex.exp (c * y) / c)) =
        (-(1 / (L : ℂ)) / c) * ((Complex.exp (c * L) - 1) / c) := by
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    simp
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hparts, hlast]
  unfold positiveTentAffine
  simp
  field_simp [hL0, hc] <;> ring

private theorem intervalIntegral_negativeTent_exp
    {L : ℝ} (hL : 0 < L) {c : ℂ} (hc : c ≠ 0) :
    (∫ y in -L..0, negativeTentAffine L y * Complex.exp (c * y)) =
      1 / c + (Complex.exp (-(c * L)) - 1) / ((L : ℂ) * c ^ 2) := by
  have hExpCont : Continuous (fun y : ℝ => Complex.exp (c * y)) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -L) (b := (0 : ℝ))
    (u := negativeTentAffine L) (u' := fun _ : ℝ => 1 / (L : ℂ))
    (v := fun y : ℝ => Complex.exp (c * y) / c)
    (v' := fun y : ℝ => Complex.exp (c * y))
    (fun y _ => hasDerivAt_negativeTentAffine hL y)
    (fun y _ => hasDerivAt_exp_mul_div hc y)
    (intervalIntegrable_const)
    (hExpCont.intervalIntegrable (-L) 0)
  have hfun :
      (fun y : ℝ => (1 / (L : ℂ)) * (Complex.exp (c * y) / c)) =
        fun y : ℝ => ((1 / (L : ℂ)) / c) * Complex.exp (c * y) := by
    funext y
    ring
  have hlast :
      (∫ y in -L..0, (1 / (L : ℂ)) * (Complex.exp (c * y) / c)) =
        ((1 / (L : ℂ)) / c) * ((1 - Complex.exp (-(c * L))) / c) := by
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    congr 2
    · simp
    · congr 2
      ring
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hparts, hlast]
  unfold negativeTentAffine
  simp
  field_simp [hL0, hc] <;> ring

private theorem hasDerivAt_positiveTentAreaPrimitive
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => ((t - t ^ 2 / (2 * L) : ℝ) : ℂ))
      ((1 - y / L : ℝ) : ℂ) y := by
  have hr : HasDerivAt (fun t : ℝ => t - t ^ 2 / (2 * L))
      (1 - y / L) y := by
    have h := (hasDerivAt_id y).sub
      (((hasDerivAt_id y).pow 2).div_const (2 * L))
    convert h using 1
    · funext t
      rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff]
      field_simp [hL.ne'] <;> ring
  exact hr.ofReal_comp

private theorem hasDerivAt_negativeTentAreaPrimitive
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => ((t + t ^ 2 / (2 * L) : ℝ) : ℂ))
      ((1 + y / L : ℝ) : ℂ) y := by
  have hr : HasDerivAt (fun t : ℝ => t + t ^ 2 / (2 * L))
      (1 + y / L) y := by
    have h := (hasDerivAt_id y).add
      (((hasDerivAt_id y).pow 2).div_const (2 * L))
    convert h using 1
    · funext t
      rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff]
      field_simp [hL.ne'] <;> ring
  exact hr.ofReal_comp

private theorem intervalIntegral_positiveTent_area
    {L : ℝ} (hL : 0 < L) :
    (∫ y in 0..L, ((1 - y / L : ℝ) : ℂ)) = (L / 2 : ℝ) := by
  have hint : IntervalIntegrable
      (fun y : ℝ => ((1 - y / L : ℝ) : ℂ)) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := L)
    (f := fun t : ℝ => ((t - t ^ 2 / (2 * L) : ℝ) : ℂ))
    (f' := fun t : ℝ => ((1 - t / L : ℝ) : ℂ))
    (fun y _ => hasDerivAt_positiveTentAreaPrimitive hL y) hint
  have hL0 : L ≠ 0 := hL.ne'
  rw [h]
  push_cast
  field_simp [hL0] <;> ring

private theorem intervalIntegral_negativeTent_area
    {L : ℝ} (hL : 0 < L) :
    (∫ y in -L..0, ((1 + y / L : ℝ) : ℂ)) = (L / 2 : ℝ) := by
  have hint : IntervalIntegrable
      (fun y : ℝ => ((1 + y / L : ℝ) : ℂ)) volume (-L) 0 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -L) (b := (0 : ℝ))
    (f := fun t : ℝ => ((t + t ^ 2 / (2 * L) : ℝ) : ℂ))
    (f' := fun t : ℝ => ((1 + t / L : ℝ) : ℂ))
    (fun y _ => hasDerivAt_negativeTentAreaPrimitive hL y) hint
  have hL0 : L ≠ 0 := hL.ne'
  rw [h]
  push_cast
  field_simp [hL0] <;> ring

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

theorem paperFT_dictionaryTent_eq_interval
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTent L) z =
      ∫ y in -L..L, dictionaryTent L y * Complex.exp (I * z * y) := by
  rw [Zeta23.paperFT_def]
  exact (intervalIntegral.integral_eq_integral_of_support_subset
    (tentExp_support_subset_Ioc hL z)).symm

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
        ∫ y in -L..0, negativeTentAffine L y * Complex.exp (c * y) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    change dictionaryTent L y * Complex.exp (c * y) =
      negativeTentAffine L y * Complex.exp (c * y)
    rw [dictionaryTent_eq_one_add_div_of_mem_Icc hL]
    · unfold negativeTentAffine
      push_cast
    · simpa [uIcc_of_le (by linarith : -L ≤ (0 : ℝ))] using hy
  have hright :
      (∫ y in 0..L, dictionaryTent L y * Complex.exp (c * y)) =
        ∫ y in 0..L, positiveTentAffine L y * Complex.exp (c * y) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro y hy
    change dictionaryTent L y * Complex.exp (c * y) =
      positiveTentAffine L y * Complex.exp (c * y)
    rw [dictionaryTent_eq_one_sub_div_of_mem_Icc hL]
    · unfold positiveTentAffine
      push_cast
    · simpa [uIcc_of_le hL.le] using hy
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

def dictionaryTentTransformClosed (L : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then (L : ℂ)
  else 2 * (1 - Complex.cos ((L : ℂ) * z)) / ((L : ℂ) * z ^ 2)

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