import Zeta23.CCM.DictionaryArchSourceIntegrability

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform

/-! # Quantitative source-test Fourier decay

The source `L¹` theorem already proves the two ingredients below internally:
a uniform transform bound on the compact-frequency region and a quadratic tail
bound away from the two removable source frequencies.  This downstream module
packages the same estimates into the global `C / (1+r²)` form needed by the
actual gamma-channel integrability proof. -/

/-- The real-frequency source transform admits a global inverse-quadratic
majorant.  The removable frequencies stay in the compact part of the proof. -/
theorem exists_paperFT_dictionarySourceTest_inv_quad_bound
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ ≤
        C * (1 + r ^ 2)⁻¹ := by
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
  let C : ℝ := 2 * (A + B)
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro r
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hden : 0 < 1 + r ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  by_cases hr : r ^ 2 ≤ 1
  · have hu := hunif r
    dsimp [C]
    nlinarith
  · have hr' : 1 < r ^ 2 := lt_of_not_ge hr
    have hs := hsq r
    have hn : 0 ≤ ‖Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ)‖ := norm_nonneg _
    dsimp [C]
    nlinarith

end Zeta23.CCM
