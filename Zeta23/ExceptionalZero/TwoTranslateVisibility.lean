import Zeta23.ExceptionalZero.WeilFilter
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory ContinuousLinearMap
open scoped Convolution

/-!
# X1: real-even target-adaptive visibility

The existing exceptional-zero stack already contains the pole-killing operator
`poleKilled` and its exact Fourier multiplier.  X1 therefore starts by producing,
for an arbitrary complex spectral target, a real-even smooth compactly supported
bump whose paper Fourier transform is nonzero at that target.

The construction uses a normalized bump as an approximate identity.  A sufficiently
small real-even bump has Fourier response close to `1` at the fixed target, hence
cannot vanish there.  No zero location is hard-coded into the test family.
-/

/-- Every complex spectral target is visible to a real-even `C⁴` compactly supported test. -/
theorem exists_realEven_contDiff_visible_test (w : ℂ) :
    ∃ q : ℝ → ℂ,
      ContDiff ℝ 4 q ∧ HasCompactSupport q ∧ Function.Even q ∧
        (∀ x : ℝ, (q x).im = 0) ∧ paperFT q w ≠ 0 := by
  let g : ℝ → ℝ := fun x => (Complex.exp (-(I * w * (x : ℂ)))).re
  have hg : Continuous g := by
    fun_prop
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.1 hg.continuousAt) (1 / 2 : ℝ) (by norm_num)
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨δ / 2, δ, by positivity, by linarith⟩
  have hconv :
      dist
          ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0)
          (g 0) ≤ (1 / 2 : ℝ) := by
    apply φ.dist_normed_convolution_le hg.aestronglyMeasurable
    intro x hx
    exact le_of_lt (hclose x (by simpa [φ] using hx))
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
  have hqeven : Function.Even q := by
    intro x
    change ((φ.normed volume (-x) : ℝ) : ℂ) = ((φ.normed volume x : ℝ) : ℂ)
    rw [φ.normed_neg]
  have hqreal : ∀ x : ℝ, (q x).im = 0 := by
    intro x
    simp [q]
  have hint : Integrable (fun x : ℝ => q x * Complex.exp (I * w * (x : ℂ))) := by
    have hce : Continuous (fun x : ℝ => Complex.exp (I * w * (x : ℂ))) := by
      fun_prop
    exact (hq4.continuous.mul hce).integrable_of_hasCompactSupport hqc.mul_right
  have hconv_re :
      ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) = (paperFT q w).re := by
    unfold MeasureTheory.convolution paperFT
    rw [← integral_re hint]
    apply integral_congr_ae
    filter_upwards with x
    have harg : -(I * w * ((-x : ℝ) : ℂ)) = I * w * (x : ℂ) := by
      push_cast
      ring
    simp [q, g, lsmul_apply, harg, Complex.mul_re]
  have hqvis_re : (paperFT q w).re ≠ 0 := by
    intro hzero
    apply hconv_ne
    rw [hconv_re, hzero]
  have hqvis : paperFT q w ≠ 0 := by
    intro hzero
    apply hqvis_re
    rw [hzero]
    simp
  exact ⟨q, hq4, hqc, hqeven, hqreal, hqvis⟩

#print axioms Zeta23.ExceptionalZero.exists_realEven_contDiff_visible_test

end Zeta23.ExceptionalZero
