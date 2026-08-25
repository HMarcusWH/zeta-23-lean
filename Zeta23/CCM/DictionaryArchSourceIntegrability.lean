import Zeta23.CCM.DictionaryArchSourceFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform

/-! # Source-test Fourier integrability

The two removable source frequencies are deliberately kept inside a compact
region.  The rational transform formula is used only on the genuine tail, where
`|r| > 2 |dictionaryFrequency n L|`, so neither denominator can vanish.
-/

private theorem integrable_of_continuous_uniform_sq_source
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

private theorem continuous_paperFT_real_source
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

private theorem integrable_fourier_of_integrable_paperFT_source
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

/-- The production source test has an `L¹` Mathlib Fourier transform. -/
theorem integrable_fourier_dictionarySourceTest
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (𝓕 (dictionarySourceTest n L)) := by
  have hki : Integrable (dictionarySourceTest n L) :=
    (continuous_dictionarySourceTest n L).integrable_of_hasCompactSupport
      (dictionarySourceTest_hasCompactSupport hL n)
  have hsupp : ∀ u : ℝ, dictionarySourceTest n L u ≠ 0 → |u| ≤ L := by
    intro u hu
    exact abs_le.mpr (dictionarySourceTest_support_subset hL n hu)
  let A : ℝ := ∫ u : ℝ, ‖dictionarySourceTest n L u‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hunif : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ ≤ A := by
    intro r
    have h := Zeta23.norm_paperFT_le hki hsupp (r : ℂ)
    simpa [A] using h
  let a : ℝ := dictionaryFrequency n L
  let R : ℝ := 1 + 2 * |a|
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let T : ℝ := 4 * |a| / Real.pi
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  let B : ℝ := max (A * R ^ 2) T
  have hB : 0 ≤ B := by
    dsimp [B]
    exact (mul_nonneg hA (sq_nonneg R)).trans (le_max_left _ _)
  have hsq : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ * r ^ 2 ≤ B := by
    intro r
    by_cases hr : |r| ≤ R
    · have hr2 : r ^ 2 ≤ R ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hR] using hr
      have hmul :
          ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ * r ^ 2 ≤
            A * R ^ 2 :=
        mul_le_mul (hunif r) hr2 (sq_nonneg r) hA
      exact hmul.trans (le_max_left _ _)
    · have hra : R < |r| := lt_of_not_ge hr
      have h2a : 2 * |a| < |r| := by
        dsimp [R] at hra
        linarith
      have hplus : a + r ≠ 0 := by
        intro hzero
        have hre : r = -a := by linarith
        rw [hre, abs_neg] at h2a
        nlinarith [abs_nonneg a]
      have hminus : a - r ≠ 0 := by
        intro hzero
        have hre : r = a := by linarith
        rw [hre] at h2a
        nlinarith [abs_nonneg a]
      have hs : (2 * |a|) ^ 2 < r ^ 2 := by
        rw [sq_lt_sq, abs_of_nonneg (mul_nonneg (by norm_num) (abs_nonneg a))]
        exact h2a
      have hsquare : 4 * a ^ 2 < r ^ 2 := by
        have haabs := sq_abs a
        nlinarith
      have hdenpos : 0 < r ^ 2 - a ^ 2 := by nlinarith
      have hhalf : r ^ 2 / 2 ≤ r ^ 2 - a ^ 2 := by nlinarith
      have hc0 : 0 ≤ 1 - Real.cos (r * L) :=
        sub_nonneg.mpr (Real.cos_le_one _)
      have hc2 : 1 - Real.cos (r * L) ≤ 2 := by
        linarith [Real.neg_one_le_cos (r * L)]
      have hform := paperFT_dictionarySourceTest_of_ne_frequency
        hL n (by simpa [a] using hplus) (by simpa [a] using hminus)
      have hnorm :
          ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ =
            |a| * (1 - Real.cos (r * L)) /
              (Real.pi * (r ^ 2 - a ^ 2)) := by
        rw [hform]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul]
        rw [abs_of_nonneg hc0, abs_of_pos Real.pi_pos, abs_of_pos hdenpos]
      have hnum : |a| * (1 - Real.cos (r * L)) ≤ 2 * |a| := by
        nlinarith [abs_nonneg a]
      have hden : 0 < Real.pi * (r ^ 2 - a ^ 2) :=
        mul_pos Real.pi_pos hdenpos
      have hfrac :
          |a| * (1 - Real.cos (r * L)) /
              (Real.pi * (r ^ 2 - a ^ 2)) ≤
            (2 * |a|) / (Real.pi * (r ^ 2 - a ^ 2)) :=
        div_le_div_of_nonneg_right hnum hden.le
      have htail :
          ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ * r ^ 2 ≤ T := by
        rw [hnorm]
        calc
          (|a| * (1 - Real.cos (r * L)) /
                (Real.pi * (r ^ 2 - a ^ 2))) * r ^ 2 ≤
              ((2 * |a|) / (Real.pi * (r ^ 2 - a ^ 2))) * r ^ 2 :=
            mul_le_mul_of_nonneg_right hfrac (sq_nonneg r)
          _ = (2 * |a| * r ^ 2) /
                (Real.pi * (r ^ 2 - a ^ 2)) := by ring
          _ ≤ 4 * |a| / Real.pi := by
            rw [div_le_iff₀ hden]
            have hcancel :
                (4 * |a| / Real.pi) *
                    (Real.pi * (r ^ 2 - a ^ 2)) =
                  4 * |a| * (r ^ 2 - a ^ 2) := by
              field_simp [Real.pi_ne_zero]
            rw [hcancel]
            have hm := mul_le_mul_of_nonneg_left hhalf
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg a))
            convert hm using 1
            all_goals ring
          _ = T := by rfl
      exact htail.trans (le_max_right _ _)
  have hpaper : Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)) :=
    integrable_of_continuous_uniform_sq_source
      (continuous_paperFT_real_source hki) hA hB hunif hsq
  exact integrable_fourier_of_integrable_paperFT_source hpaper

end Zeta23.CCM
