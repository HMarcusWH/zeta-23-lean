import Zeta23.CCM.DictionaryArchSourceMuIntegrability
import Zeta23.CCM.DictionaryArchCompletion

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators FourierTransform

/-! # Density route for the source-test literature archimedean bridge

This file returns to the canonical v0.7 route after the quantitative source and
`mu - mu 0` estimates.  The first gate packages absolute integrability of the
actual literature integrand after subtracting the constant `mu 0` term.
-/

private theorem measurable_mu_sub_mu_zero :
    Measurable (fun τ : ℝ => Zeta23.mu τ - Zeta23.mu 0) := by
  have hterm : ∀ m : ℕ,
      Measurable (fun τ : ℝ => archDigammaAllTerm (τ / 2) m) := by
    intro m
    unfold archDigammaAllTerm
    fun_prop
  have hsum : Measurable (fun τ : ℝ =>
      ∑' m : ℕ, archDigammaAllTerm (τ / 2) m) :=
    Measurable.tsum hterm
  have heq :
      (fun τ : ℝ => Zeta23.mu τ - Zeta23.mu 0) =
        fun τ : ℝ => (1 / (2 * Real.pi)) *
          ∑' m : ℕ, archDigammaAllTerm (τ / 2) m := by
    funext τ
    exact mu_sub_mu_zero_eq_archDigammaAllSeries τ
  rw [heq]
  exact measurable_const.mul hsum

/-- Absolute integrability of the source Fourier transform against the exact
vertical gamma-density difference.  This is the domination certificate used by
the density Fubini step; no new asymptotic or explicit-formula hypothesis is
introduced. -/
theorem integrable_paperFT_dictionarySourceTest_mul_mu_sub_mu_zero
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) := by
  let Cmu : ℝ :=
    (1 / (2 * Real.pi)) * ∑' m : ℕ, archHalfWeight m
  have hW := integrable_norm_paperFT_dictionarySourceTest_mul_sqrt hL n
  have hmajor : Integrable (fun τ : ℝ =>
      Cmu *
        (‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2|)) :=
    hW.const_mul Cmu
  have hmeasFT : Measurable (fun τ : ℝ =>
      Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)) := by
    have hki : Integrable (dictionarySourceTest n L) :=
      (continuous_dictionarySourceTest n L).integrable_of_hasCompactSupport
        (dictionarySourceTest_hasCompactSupport hL n)
    have hF : Continuous (𝓕 (dictionarySourceTest n L)) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hki
    have heq :
        (fun τ : ℝ => Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)) =
          fun τ : ℝ => 𝓕 (dictionarySourceTest n L) (-τ / (2 * Real.pi)) := by
      funext τ
      exact Zeta23.paperFT_ofReal_eq_fourier _ τ
    rw [heq]
    exact (hF.comp (by fun_prop)).measurable
  have hmeasMu : Measurable (fun τ : ℝ =>
      ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_mu_sub_mu_zero
  refine hmajor.mono' (hmeasFT.mul hmeasMu).aestronglyMeasurable ?_
  filter_upwards with τ
  have hmu0 := mu_sub_mu_zero_nonneg τ
  have hmule := mu_sub_mu_zero_le_sqrt τ
  have hnorm0 :
      0 ≤ ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hmule hnorm0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu0]
  dsimp [Cmu]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

end Zeta23.CCM
