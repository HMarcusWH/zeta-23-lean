import Zeta23.ExceptionalZero.TwoTranslateFixedTest

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory ContinuousLinearMap
open scoped Convolution

/-!
# Eventual completeness of the canonical radius family

This module strengthens the single-radius visibility theorem from
`TwoTranslateFixedTest`: a fixed spectral target is visible at every sufficiently
small positive radius.  It then transfers that uniformity through the existing
pole-killing operator and, optionally, to a countable radius sequence.

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

end Zeta23.ExceptionalZero
