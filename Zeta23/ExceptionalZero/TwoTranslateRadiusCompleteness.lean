import Zeta23.ExceptionalZero.TwoTranslateFixedTest
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory ContinuousLinearMap Filter Set
open scoped Convolution Topology

/-!
# Eventual completeness of the canonical radius family

This module strengthens the single-radius visibility theorem from
`TwoTranslateFixedTest`: a fixed spectral target is visible at every sufficiently
small positive radius.  It then transfers that uniformity through the existing
pole-killing operator and specializes it to a countable radius sequence.

No positivity statement is made for any detector family.
-/

/-- A complex target is visible to every canonical seed below a radius cutoff. -/
def CanonicalSeedVisibleBelow (w : ℂ) (ε : ℝ) : Prop :=
  ∀ r : PositiveRadius, (r : ℝ) < ε →
    paperFT (canonicalSeedTest r) w ≠ 0

/-- A zeta zero is visible to every canonical pole-killed detector below a radius cutoff. -/
def CanonicalPoleKilledVisibleBelowAtZero
    (ρ₀ : zetaZeroConfig.carrier) (ε : ℝ) : Prop :=
  ∀ r : PositiveRadius, (r : ℝ) < ε →
    paperFT (canonicalPoleKilledTest r) (gammaOf (ρ₀ : ℂ)) ≠ 0

/-- Every sufficiently small canonical seed radius sees a fixed complex spectral target. -/
theorem eventually_canonicalSeed_visible (w : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ CanonicalSeedVisibleBelow w ε := by
  let g : ℝ → ℝ := fun x => (Complex.exp (-(I * w * (x : ℂ)))).re
  have hg : Continuous g := by
    fun_prop
  have hg0 : ContinuousAt g 0 := hg.continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.1 hg0) (1 / 2 : ℝ) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro r hrδ
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨(r : ℝ) / 2, (r : ℝ), by
      have hr : 0 < (r : ℝ) := r.2
      linarith, by
      have hr : 0 < (r : ℝ) := r.2
      linarith⟩
  have hconv :
      dist
          ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0)
          (g 0) ≤ (1 / 2 : ℝ) := by
    apply φ.dist_normed_convolution_le hg.aestronglyMeasurable
    intro x hx
    have hxr : dist x 0 < (r : ℝ) := by
      simpa [φ] using hx
    exact le_of_lt (hclose (hxr.trans hrδ))
  have hconv_ne : ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) ≠ 0 := by
    intro hzero
    rw [hzero] at hconv
    norm_num [g] at hconv
  let q : ℝ → ℂ := fun x => ((φ.normed volume x : ℝ) : ℂ)
  have hq4 : ContDiff ℝ 4 q := by
    exact Complex.ofRealCLM.contDiff.comp φ.contDiff_normed
  have hqc : HasCompactSupport q := by
    exact (φ.hasCompactSupport_normed (μ := volume)).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hint : Integrable (fun x : ℝ => q x * Complex.exp (I * w * (x : ℂ))) := by
    have hce : Continuous (fun x : ℝ => Complex.exp (I * w * (x : ℂ))) := by
      fun_prop
    exact (hq4.continuous.mul hce).integrable_of_hasCompactSupport hqc.mul_right
  have hconv_re :
      ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) = (paperFT q w).re := by
    unfold MeasureTheory.convolution paperFT
    calc
      (∫ t : ℝ, ((lsmul ℝ ℝ) (φ.normed volume t)) (g (0 - t))) =
          ∫ u : ℝ, (q u * Complex.exp (I * w * (u : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, g, lsmul_apply, Complex.mul_re]
      _ = (∫ u : ℝ, q u * Complex.exp (I * w * (u : ℂ))).re := by
        exact integral_re hint
  have hqvis_re : (paperFT q w).re ≠ 0 := by
    intro hzero
    apply hconv_ne
    rw [hconv_re, hzero]
  have hqvis : paperFT q w ≠ 0 := by
    intro hzero
    apply hqvis_re
    rw [hzero]
    simp
  have hφ : φ = canonicalRadiusBump r := by
    rfl
  have hq : q = canonicalSeedTest r := by
    funext x
    simp [q, canonicalSeedTest, hφ]
  rw [← hq]
  exact hqvis

/-- Every sufficiently small canonical pole-killed radius sees a fixed nontrivial zeta zero. -/
theorem eventually_canonicalPoleKilled_visible_at_zero
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ CanonicalPoleKilledVisibleBelowAtZero ρ₀ ε := by
  obtain ⟨ε, hε, hvis⟩ :=
    eventually_canonicalSeed_visible (gammaOf (ρ₀ : ℂ))
  refine ⟨ε, hε, ?_⟩
  intro r hrε
  have hq4 := canonicalSeedTest_contDiff_four r
  have hq2 : ContDiff ℝ 2 (canonicalSeedTest r) := hq4.of_le (by norm_num)
  have hqc := canonicalSeedTest_hasCompactSupport r
  exact paperFT_poleKilled_ne_zero_at_zero hq2 hqc ρ₀ (hvis r hrε)

/-- Explicit countable sequence of positive canonical radii tending to zero. -/
def canonicalRadiusSequence (n : ℕ) : PositiveRadius :=
  ⟨1 / ((n : ℝ) + 1), by positivity⟩

/-- The explicit canonical radius sequence converges to zero. -/
theorem canonicalRadiusSequence_tendsto_zero :
    Tendsto (fun n : ℕ => (canonicalRadiusSequence n : ℝ)) atTop (𝓝 0) := by
  simpa [canonicalRadiusSequence] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Every nontrivial zeta zero is visible to all sufficiently late detectors in the
explicit countable radius bank. -/
theorem eventually_canonicalPoleKilledSequence_visible_at_zero
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperFT
        (canonicalPoleKilledTest (canonicalRadiusSequence n))
        (gammaOf (ρ₀ : ℂ)) ≠ 0 := by
  obtain ⟨ε, hε, hvis⟩ := eventually_canonicalPoleKilled_visible_at_zero ρ₀
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (canonicalRadiusSequence n : ℝ) < ε :=
    canonicalRadiusSequence_tendsto_zero.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N, ?_⟩
  intro n hn
  exact hvis (canonicalRadiusSequence n) (hN n hn)

/-- Countable-bank X4.6 endpoint: every hypothetical off-line zero forces a negative
complete two-translate determinant for some explicitly indexed canonical detector. -/
theorem exists_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ n : ℕ, ∃ a : ℝ,
      0 ≤ a ∧
        twoTranslateDeterminantGap zetaZeroConfig
          (canonicalPoleKilledTest (canonicalRadiusSequence n)) (2 * a) < 0 := by
  obtain ⟨ρR, _hprov, hright⟩ :=
    exists_rightHalf_reflection_of_offLine ρ₀ hoff
  obtain ⟨N, hvis⟩ :=
    eventually_canonicalPoleKilledSequence_visible_at_zero ρR
  obtain ⟨hk, hkc, heven, hreal⟩ :=
    canonicalPoleKilledTest_admissible (canonicalRadiusSequence N)
  have hnot :=
    not_subexponential_weilRelativeCorrelation_of_right_zero
      hk hkc hreal heven ρR hright (hvis N le_rfl)
  obtain ⟨a, ha, hgt⟩ :=
    exists_nonneg_gt_of_not_subexponential
      hnot
      ‖zetaZeroConfig.W
        (canonicalPoleKilledTest (canonicalRadiusSequence N))
        (canonicalPoleKilledTest (canonicalRadiusSequence N))‖
  refine ⟨N, a, ha, ?_⟩
  exact twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
    zetaZeroConfig (canonicalPoleKilledTest (canonicalRadiusSequence N)) (2 * a) hgt

#print axioms Zeta23.ExceptionalZero.eventually_canonicalSeed_visible
#print axioms Zeta23.ExceptionalZero.eventually_canonicalPoleKilled_visible_at_zero
#print axioms Zeta23.ExceptionalZero.canonicalRadiusSequence_tendsto_zero
#print axioms Zeta23.ExceptionalZero.eventually_canonicalPoleKilledSequence_visible_at_zero
#print axioms Zeta23.ExceptionalZero.exists_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero

end Zeta23.ExceptionalZero
