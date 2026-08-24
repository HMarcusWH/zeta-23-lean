import Zeta23.CCM.DictionaryArchMuGrowth
import Zeta23.CCM.DictionaryArchSourceDecay
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped FourierTransform

/-! # Weighted source-transform integrability for the literature arch bridge

The positive-abscissa digamma series is controlled by `sqrt |τ|`, while the
source transform has global inverse-quadratic decay.  This module packages the
resulting `L¹` majorant needed to interchange the actual literature gamma
integral with the digamma series. -/

private theorem continuous_paperFT_source
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Continuous (fun r : ℝ => Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)) := by
  have hki : Integrable (dictionarySourceTest n L) :=
    (continuous_dictionarySourceTest n L).integrable_of_hasCompactSupport
      (dictionarySourceTest_hasCompactSupport hL n)
  have hF : Continuous (𝓕 (dictionarySourceTest n L)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hki
  have heq :
      (fun r : ℝ => Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)) =
        fun r : ℝ => 𝓕 (dictionarySourceTest n L) (-r / (2 * Real.pi)) := by
    funext r
    exact Zeta23.paperFT_ofReal_eq_fourier _ r
  rw [heq]
  exact hF.comp (by fun_prop)

/-- Elementary comparison used to place the square-root weighted inverse
quadratic tail under the standard Japanese-bracket `L¹` majorant. -/
private theorem sqrt_div_one_add_sq_le_two_mul_rpow
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x / (1 + x ^ 2) ≤
      2 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 : 0 < 1 + x := by linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hs1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 h1
  have hsle : Real.sqrt x ≤ Real.sqrt (1 + x) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq1 : (Real.sqrt (1 + x)) ^ 2 = 1 + x := by
    simpa using Real.sq_sqrt h1.le
  have hmul :
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
        (1 + x) ^ 2 := by
    calc
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
          Real.sqrt (1 + x) * ((1 + x) * Real.sqrt (1 + x)) := by
        exact mul_le_mul_of_nonneg_right hsle
          (mul_nonneg h1.le hs1.le)
      _ = (1 + x) ^ 2 := by
        rw [← hsq1]
        ring
  have hpoly : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x - 1)]
  have hcross :
      Real.sqrt x * ((1 + x) * Real.sqrt (1 + x)) ≤
        2 * (1 + x ^ 2) := hmul.trans hpoly
  have hden1 : 0 < 1 + x ^ 2 := by positivity
  have hden2 : 0 < (1 + x) * Real.sqrt (1 + x) :=
    mul_pos h1 hs1
  have hfrac :
      Real.sqrt x / (1 + x ^ 2) ≤
        2 / ((1 + x) * Real.sqrt (1 + x)) := by
    rw [div_le_div_iff₀ hden1 hden2]
    exact hcross
  have hp :
      (1 + x) ^ (3 / 2 : ℝ) =
        (1 + x) * Real.sqrt (1 + x) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add h1]
    simp [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg h1.le, hp]
  simpa [div_eq_mul_inv] using hfrac

/-- The source transform remains integrable after multiplication by the
square-root weight required by the positive-abscissa digamma estimate. -/
theorem integrable_norm_paperFT_dictionarySourceTest_mul_sqrt
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (fun τ : ℝ =>
      ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2|) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_paperFT_dictionarySourceTest_inv_quad_bound hL n
  have hbase : Integrable
      (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num
  have hmajorInt : Integrable
      (fun τ : ℝ => (2 * C) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) :=
    hbase.const_mul (2 * C)
  have hcont : Continuous (fun τ : ℝ =>
      ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2|) := by
    exact (continuous_paperFT_source hL n).norm.mul (by fun_prop)
  refine hmajorInt.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with τ
  have habs : |τ / 2| ≤ |τ| := by
    rw [abs_div]
    norm_num
    nlinarith [abs_nonneg τ]
  have hsqrt : Real.sqrt |τ / 2| ≤ Real.sqrt |τ| :=
    Real.sqrt_le_sqrt habs
  have hfirst :
      ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2| ≤
        (C * (1 + τ ^ 2)⁻¹) * Real.sqrt |τ| := by
    exact mul_le_mul (hdecay τ) hsqrt (Real.sqrt_nonneg _) hC
  have hkernel :=
    sqrt_div_one_add_sq_le_two_mul_rpow (x := |τ|) (abs_nonneg τ)
  have hsecond :
      (C * (1 + τ ^ 2)⁻¹) * Real.sqrt |τ| ≤
        (2 * C) * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
    have hsquare : |τ| ^ 2 = τ ^ 2 := sq_abs τ
    have hc := mul_le_mul_of_nonneg_left hkernel hC
    rw [hsquare] at hc
    convert hc using 1 <;> ring
  have hnonneg :
      0 ≤ ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2| :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hmajnonneg :
      0 ≤ (2 * C) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.norm_eq_abs, abs_of_nonneg hmajnonneg]
  simpa [Real.norm_eq_abs] using hfirst.trans hsecond

end Zeta23.CCM
