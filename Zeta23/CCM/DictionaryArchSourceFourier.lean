import Zeta23.CCM.DictionaryArchFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform Interval

/-! # Scalar source Fourier transform

This module isolates the source-test transform from the already-green tent and
diagonal Fourier gates.  The rational formula is used only away from its two
removable frequencies; later tail estimates keep those frequencies inside the
compact region rather than dividing through them.
-/

private theorem intervalIntegral_eq_integral_of_support_subset_Icc_source
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (h : Function.support f ⊆ Icc a b) :
    (∫ x in a..b, f x) = ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]

private def sourceSinCosPrimitive (a r y : ℝ) : ℝ :=
  (-1 / 2) *
    (Real.cos ((a + r) * y) / (a + r) +
      Real.cos ((a - r) * y) / (a - r))

private theorem hasDerivAt_sourceSinCosPrimitive
    {a r : ℝ} (hplus : a + r ≠ 0) (hminus : a - r ≠ 0) (y : ℝ) :
    HasDerivAt (sourceSinCosPrimitive a r)
      (Real.sin (a * y) * Real.cos (r * y)) y := by
  have hpLin : HasDerivAt (fun x : ℝ => (a + r) * x) (a + r) y := by
    simpa using (hasDerivAt_id y).const_mul (a + r)
  have hmLin : HasDerivAt (fun x : ℝ => (a - r) * x) (a - r) y := by
    simpa using (hasDerivAt_id y).const_mul (a - r)
  have hp := hpLin.cos.div_const (a + r)
  have hm := hmLin.cos.div_const (a - r)
  have hscaled := (hp.add hm).const_mul (-1 / 2)
  have hscaled' : HasDerivAt
      (fun x : ℝ => (-1 / 2) *
        (Real.cos ((a + r) * x) / (a + r) +
          Real.cos ((a - r) * x) / (a - r)))
      ((-1 / 2) *
        (-Real.sin ((a + r) * y) * (a + r) / (a + r) +
          -Real.sin ((a - r) * y) * (a - r) / (a - r))) y := by
    simpa only [Pi.add_apply] using hscaled
  have hpCancel :
      -Real.sin ((a + r) * y) * (a + r) / (a + r) =
        -Real.sin ((a + r) * y) := by
    field_simp [hplus]
  have hmCancel :
      -Real.sin ((a - r) * y) * (a - r) / (a - r) =
        -Real.sin ((a - r) * y) := by
    field_simp [hminus]
  have hder :
      (-1 / 2) *
        (-Real.sin ((a + r) * y) * (a + r) / (a + r) +
          -Real.sin ((a - r) * y) * (a - r) / (a - r)) =
        Real.sin (a * y) * Real.cos (r * y) := by
    rw [hpCancel, hmCancel]
    rw [show (a + r) * y = a * y + r * y by ring,
      show (a - r) * y = a * y - r * y by ring,
      Real.sin_add, Real.sin_sub]
    ring
  rw [hder] at hscaled'
  change HasDerivAt
    (fun x : ℝ => (-1 / 2) *
      (Real.cos ((a + r) * x) / (a + r) +
        Real.cos ((a - r) * x) / (a - r)))
    (Real.sin (a * y) * Real.cos (r * y)) y
  exact hscaled'

private theorem dictionaryFrequency_mul_L_sourceFourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryFrequency n L * L = (n : ℝ) * (2 * Real.pi) := by
  unfold dictionaryFrequency
  field_simp [hL.ne']

private theorem sin_dictionaryFrequency_L_sourceFourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.sin (dictionaryFrequency n L * L) = 0 := by
  rw [dictionaryFrequency_mul_L_sourceFourier hL n]
  simpa using Real.sin_add_int_mul_two_pi 0 n

private theorem cos_dictionaryFrequency_L_sourceFourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.cos (dictionaryFrequency n L * L) = 1 := by
  rw [dictionaryFrequency_mul_L_sourceFourier hL n]
  exact Real.cos_int_mul_two_pi n

private theorem intervalIntegral_source_sin_cos_sourceFourier
    {L r : ℝ} (hL : 0 < L) (n : ℤ)
    (hplus : dictionaryFrequency n L + r ≠ 0)
    (hminus : dictionaryFrequency n L - r ≠ 0) :
    (∫ y in (0 : ℝ)..L,
      Real.sin (dictionaryFrequency n L * y) * Real.cos (r * y)) =
      dictionaryFrequency n L * (1 - Real.cos (r * L)) /
        (dictionaryFrequency n L ^ 2 - r ^ 2) := by
  let a : ℝ := dictionaryFrequency n L
  have hint : IntervalIntegrable
      (fun y : ℝ => Real.sin (a * y) * Real.cos (r * y)) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hprim := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := sourceSinCosPrimitive a r)
    (f' := fun y : ℝ => Real.sin (a * y) * Real.cos (r * y))
    (fun y _ => hasDerivAt_sourceSinCosPrimitive (by simpa [a] using hplus)
      (by simpa [a] using hminus) y) hint
  have hcosPlus : Real.cos ((a + r) * L) = Real.cos (r * L) := by
    rw [show (a + r) * L = a * L + r * L by ring, Real.cos_add]
    rw [show a * L = dictionaryFrequency n L * L by rfl,
      cos_dictionaryFrequency_L_sourceFourier hL n,
      sin_dictionaryFrequency_L_sourceFourier hL n]
    ring
  have hcosMinus : Real.cos ((a - r) * L) = Real.cos (r * L) := by
    rw [show (a - r) * L = a * L - r * L by ring, Real.cos_sub]
    rw [show a * L = dictionaryFrequency n L * L by rfl,
      cos_dictionaryFrequency_L_sourceFourier hL n,
      sin_dictionaryFrequency_L_sourceFourier hL n]
    ring
  have hden : a ^ 2 - r ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa [a] using hplus) (by simpa [a] using hminus)
  have hpInv : (a + r)⁻¹ = (a - r) / (a ^ 2 - r ^ 2) := by
    apply (eq_div_iff hden).2
    calc
      (a + r)⁻¹ * (a ^ 2 - r ^ 2) =
          (a + r)⁻¹ * ((a - r) * (a + r)) := by ring
      _ = ((a + r)⁻¹ * (a + r)) * (a - r) := by ring
      _ = a - r := by rw [inv_mul_cancel₀ hplus, one_mul]
  have hmInv : (a - r)⁻¹ = (a + r) / (a ^ 2 - r ^ 2) := by
    apply (eq_div_iff hden).2
    calc
      (a - r)⁻¹ * (a ^ 2 - r ^ 2) =
          (a - r)⁻¹ * ((a - r) * (a + r)) := by ring
      _ = ((a - r)⁻¹ * (a - r)) * (a + r) := by ring
      _ = a + r := by rw [inv_mul_cancel₀ hminus, one_mul]
  rw [hprim]
  change sourceSinCosPrimitive a r L - sourceSinCosPrimitive a r 0 =
    a * (1 - Real.cos (r * L)) / (a ^ 2 - r ^ 2)
  unfold sourceSinCosPrimitive
  rw [hcosPlus, hcosMinus]
  simp only [mul_zero, Real.cos_zero, div_eq_mul_inv, hpInv, hmInv]
  field_simp [hden]
  ring

/-- Real-frequency closed form for the source transform away from the removable
frequencies `r = ± dictionaryFrequency n L`. -/
theorem paperFT_dictionarySourceTest_of_ne_frequency
    {L r : ℝ} (hL : 0 < L) (n : ℤ)
    (hplus : dictionaryFrequency n L + r ≠ 0)
    (hminus : dictionaryFrequency n L - r ≠ 0) :
    Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ) =
      ((dictionaryFrequency n L * (1 - Real.cos (r * L)) /
        (Real.pi * (r ^ 2 - dictionaryFrequency n L ^ 2)) : ℝ) : ℂ) := by
  let G : ℝ → ℂ := fun y =>
    dictionarySourceTest n L y * Complex.exp (I * (r : ℂ) * (y : ℂ))
  rw [Zeta23.paperFT_def]
  change (∫ y : ℝ, G y) = _
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro y hy
    apply dictionarySourceTest_support_subset hL n
    intro hzero
    apply hy
    simp [G, hzero]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc_source
    (by linarith : -L ≤ L) hGsupp]
  have hGcont : Continuous G :=
    (continuous_dictionarySourceTest n L).mul (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0) (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hleft :
      (∫ y in -L..(0 : ℝ), G y) = ∫ y in (0 : ℝ)..L, G (-y) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) G
    norm_num at h
    exact h.symm
  rw [hleft]
  have hcneg : Continuous (fun y : ℝ => G (-y)) := by
    simpa [Function.comp_def] using hGcont.comp continuous_neg
  have hnegInt : IntervalIntegrable (fun y : ℝ => G (-y)) volume 0 L :=
    hcneg.intervalIntegrable 0 L
  have hposInt : IntervalIntegrable G volume 0 L := hGcont.intervalIntegrable 0 L
  rw [← intervalIntegral.integral_add hnegInt hposInt]
  have hfun : ∀ y ∈ Set.uIcc (0 : ℝ) L,
      G (-y) + G y =
        (((-1 / Real.pi) *
          (Real.sin (dictionaryFrequency n L * y) * Real.cos (r * y)) : ℝ) : ℂ) := by
    intro y hy
    rw [Set.uIcc_of_le hL.le] at hy
    have hy0 : 0 ≤ y := hy.1
    have hyL : y ≤ L := hy.2
    have habs : |y| ≤ L := by simpa [abs_of_nonneg hy0] using hyL
    have hs := dictionarySourceTest_eq_sine_of_abs_le hL habs n
    have hsn := dictionarySourceTest_neg n L y
    dsimp [G]
    rw [hsn, hs]
    have hepos :
        Complex.exp (I * (r : ℂ) * (y : ℂ)) =
          Complex.exp (((r * y : ℝ) : ℂ) * I) := by
      congr 1
      push_cast
      ring
    have heneg :
        Complex.exp (I * (r : ℂ) * ((-y : ℝ) : ℂ)) =
          Complex.exp (((-(r * y) : ℝ) : ℂ) * I) := by
      congr 1
      push_cast
      ring
    rw [hepos, heneg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg, abs_of_nonneg hy0, dictionaryFrequency]
    ring
  rw [intervalIntegral.integral_congr hfun]
  rw [intervalIntegral.integral_ofReal]
  norm_cast
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral_source_sin_cos_sourceFourier hL n hplus hminus]
  have hden : dictionaryFrequency n L ^ 2 - r ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hden' : r ^ 2 - dictionaryFrequency n L ^ 2 ≠ 0 := by
    intro hzero
    apply hden
    nlinarith
  have hreal :
      (-1 / Real.pi) *
          (dictionaryFrequency n L * (1 - Real.cos (r * L)) /
            (dictionaryFrequency n L ^ 2 - r ^ 2)) =
        dictionaryFrequency n L * (1 - Real.cos (r * L)) /
          (Real.pi * (r ^ 2 - dictionaryFrequency n L ^ 2)) := by
    field_simp [Real.pi_ne_zero, hden, hden']
    ring
  exact_mod_cast hreal

end Zeta23.CCM
