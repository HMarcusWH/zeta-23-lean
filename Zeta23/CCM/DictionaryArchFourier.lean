import Zeta23.CCM.DictionaryArchCompletion
import Zeta23.CCM.DictionaryTentDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform Interval

/-! # Fourier-integrability gates for the deterministic archimedean bridge

The literature archimedean channel uses paper inversion and therefore needs an
actual `L¹` Fourier-transform hypothesis.  Continuity plus compact support of the
physical test is not enough.  This file proves the needed transform integrability
from explicit quadratic real-frequency decay.
-/

/-- A continuous complex function with a uniform bound and a global quadratic
weighted bound is integrable.  The proof compares it to the standard integrable
majorant `(1+x^2)⁻¹`. -/
private theorem integrable_of_continuous_uniform_sq
    {f : ℝ → ℂ} (hf : Continuous f)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hunif : ∀ x : ℝ, ‖f x‖ ≤ A)
    (hsq : ∀ x : ℝ, ‖f x‖ * x ^ 2 ≤ B) :
    Integrable f := by
  let C : ℝ := 2 * (A + B)
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hmajor : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + x ^ 2)⁻¹ := by
    intro x
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hden : 0 < 1 + x ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hden]
    by_cases hx : x ^ 2 ≤ 1
    · have hu := hunif x
      dsimp [C]
      nlinarith
    · have hx' : 1 < x ^ 2 := lt_of_not_ge hx
      have hs := hsq x
      have hn : 0 ≤ ‖f x‖ := norm_nonneg _
      dsimp [C]
      nlinarith
  have hmajorInt : Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  exact hmajorInt.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hmajor)

/-- Real-frequency continuity of the paper Fourier transform of an `L¹` test. -/
private theorem continuous_paperFT_real_of_integrable
    {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (fun r : ℝ => Zeta23.paperFT k (r : ℂ)) := by
  have hF : Continuous (𝓕 k) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hk
  have heq :
      (fun r : ℝ => Zeta23.paperFT k (r : ℂ)) =
        fun r : ℝ => 𝓕 k (-r / (2 * Real.pi)) := by
    funext r
    exact Zeta23.paperFT_ofReal_eq_fourier k r
  rw [heq]
  exact hF.comp (by fun_prop)

/-- Convert real-frequency paper-transform integrability to Mathlib Fourier
integrability using the repository's pinned convention bridge. -/
private theorem integrable_fourier_of_integrable_paperFT
    {k : ℝ → ℂ}
    (hk : Integrable (fun r : ℝ => Zeta23.paperFT k (r : ℂ))) :
    Integrable (𝓕 k) := by
  have hc : (-(2 * Real.pi) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hcomp := hk.comp_mul_left' hc
  have heq :
      (fun w : ℝ =>
        Zeta23.paperFT k (((-(2 * Real.pi)) * w : ℝ) : ℂ)) = 𝓕 k := by
    funext w
    calc
      Zeta23.paperFT k (((-(2 * Real.pi)) * w : ℝ) : ℂ) =
          Zeta23.paperFT k (-(2 * Real.pi * w)) := by
            congr 1
            push_cast
            ring
      _ = 𝓕 k w := (Zeta23.fourier_eq_paperFT k w).symm
  rw [← heq]
  exact hcomp

/-- The canonical tent's real-frequency paper transform is `L¹`.  The compact
part is controlled by the zeroth-order transform bound and the tail by the
already-certified quadratic tent decay theorem. -/
theorem integrable_paperFT_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun r : ℝ => Zeta23.paperFT (dictionaryTent L) (r : ℂ)) := by
  have hki : Integrable (dictionaryTent L) := integrable_dictionaryTent hL
  have hsupp : ∀ u : ℝ, dictionaryTent L u ≠ 0 → |u| ≤ L := by
    intro u hu
    exact abs_le.mpr (dictionaryTent_support_subset_Icc hL hu)
  let A : ℝ := ∫ u : ℝ, ‖dictionaryTent L u‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hunif : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ ≤ A := by
    intro r
    have h := Zeta23.norm_paperFT_le hki hsupp (r : ℂ)
    simpa [A] using h
  let B : ℝ := 2 * (1 + Real.exp (L / 2)) / L
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ * r ^ 2 ≤ B := by
    intro r
    have h := norm_paperFT_dictionaryTent_mul_sq_le hL (r : ℂ) (by simp)
    simpa [B, Real.norm_eq_abs, sq_abs] using h
  exact integrable_of_continuous_uniform_sq
    (continuous_paperFT_real_of_integrable hki) hA hB hunif hsq

/-- Mathlib-Fourier `L¹` gate for the canonical tent. -/
theorem integrable_fourier_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (𝓕 (dictionaryTent L)) :=
  integrable_fourier_of_integrable_paperFT
    (integrable_paperFT_dictionaryTent hL)

/-- The diagonal production basis test has an integrable Fourier transform.  Its
paper transform is the average of two real translates of the integrable tent
transform, so no new asymptotic estimate is required. -/
theorem integrable_fourier_dictionaryBasisTest_diag
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (𝓕 (dictionaryBasisTest n n L)) := by
  have ht : Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryTent L) (r : ℂ)) :=
    integrable_paperFT_dictionaryTent hL
  let a : ℝ := dictionaryFrequency n L
  have hp : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ))) := by
    simpa only [Complex.ofReal_add] using ht.comp_add_right a
  have hm : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) := by
    simpa only [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg] using
      ht.comp_add_right (-a)
  have hsum : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
          Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) :=
    hp.add hm
  have hhalf : Integrable
      (fun r : ℝ =>
        (1 / 2 : ℂ) *
          (Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
            Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ)))) :=
    hsum.const_mul (1 / 2 : ℂ)
  have heq :
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryBasisTest n n L) (r : ℂ)) =
        fun r : ℝ =>
          (1 / 2 : ℂ) *
            (Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
              Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) := by
    funext r
    rw [paperFT_dictionaryBasisTest_diag hL n (r : ℂ)]
    dsimp [a]
    ring
  have hpaper : Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryBasisTest n n L) (r : ℂ)) := by
    rw [heq]
    exact hhalf
  exact integrable_fourier_of_integrable_paperFT hpaper

/-! ### Scalar source-test tail transform -/

private theorem intervalIntegral_eq_integral_of_support_subset_Icc_fourier
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (h : Function.support f ⊆ Icc a b) :
    (∫ x in a..b, f x) = ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]

private def sinCosPrimitive (a r y : ℝ) : ℝ :=
  (-1 / 2) *
    (Real.cos ((a + r) * y) / (a + r) +
      Real.cos ((a - r) * y) / (a - r))

private theorem hasDerivAt_sinCosPrimitive
    {a r : ℝ} (hplus : a + r ≠ 0) (hminus : a - r ≠ 0) (y : ℝ) :
    HasDerivAt (sinCosPrimitive a r)
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

private theorem dictionaryFrequency_mul_L_fourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryFrequency n L * L = (n : ℝ) * (2 * Real.pi) := by
  unfold dictionaryFrequency
  field_simp [hL.ne']

private theorem sin_dictionaryFrequency_L_fourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.sin (dictionaryFrequency n L * L) = 0 := by
  rw [dictionaryFrequency_mul_L_fourier hL n]
  simpa using Real.sin_add_int_mul_two_pi 0 n

private theorem cos_dictionaryFrequency_L_fourier
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.cos (dictionaryFrequency n L * L) = 1 := by
  rw [dictionaryFrequency_mul_L_fourier hL n]
  simpa using Real.cos_int_mul_two_pi n

private theorem intervalIntegral_source_sin_cos
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
    (f := sinCosPrimitive a r)
    (f' := fun y : ℝ => Real.sin (a * y) * Real.cos (r * y))
    (fun y _ => hasDerivAt_sinCosPrimitive (by simpa [a] using hplus)
      (by simpa [a] using hminus) y) hint
  have hcosPlus : Real.cos ((a + r) * L) = Real.cos (r * L) := by
    rw [show (a + r) * L = a * L + r * L by ring, Real.cos_add]
    rw [show a * L = dictionaryFrequency n L * L by rfl,
      cos_dictionaryFrequency_L_fourier hL n,
      sin_dictionaryFrequency_L_fourier hL n]
    ring
  have hcosMinus : Real.cos ((a - r) * L) = Real.cos (r * L) := by
    rw [show (a - r) * L = a * L - r * L by ring, Real.cos_sub]
    rw [show a * L = dictionaryFrequency n L * L by rfl,
      cos_dictionaryFrequency_L_fourier hL n,
      sin_dictionaryFrequency_L_fourier hL n]
    ring
  have hden : a ^ 2 - r ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa [a] using hplus) (by simpa [a] using hminus)
  have hpInv : (a + r)⁻¹ = (a - r) / (a ^ 2 - r ^ 2) := by
    rw [show a ^ 2 - r ^ 2 = (a - r) * (a + r) by ring]
    field_simp [hplus, hminus]
  have hmInv : (a - r)⁻¹ = (a + r) / (a ^ 2 - r ^ 2) := by
    rw [show a ^ 2 - r ^ 2 = (a - r) * (a + r) by ring]
    field_simp [hplus, hminus]
  rw [hprim]
  change sinCosPrimitive a r L - sinCosPrimitive a r 0 =
    a * (1 - Real.cos (r * L)) / (a ^ 2 - r ^ 2)
  unfold sinCosPrimitive
  rw [hcosPlus, hcosMinus]
  simp only [div_eq_mul_inv, hpInv, hmInv]
  field_simp [hden]
  ring

private theorem paperFT_dictionarySourceTest_tail_formula
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
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc_fourier
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
    simpa using h.symm
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
    push_cast
    ring
  rw [intervalIntegral.integral_congr hfun]
  rw [intervalIntegral.integral_ofReal]
  norm_cast
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral_source_sin_cos hL n hplus hminus]
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