import Zeta23.CCM.DictionaryArchSourceMuIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators FourierTransform

/-! # Source-test digamma series under the literature gamma integral

This is the first layer that acts on the actual literature integrand.  The
square-root source majorant from `DictionaryArchSourceMuIntegrability` controls
each positive-abscissa digamma summand by the summable `archHalfWeight` series.
-/

/-- One positive-abscissa summand in the source-test gamma integral. -/
def sourceArchDigammaIntegrand
    (n : ℤ) (L : ℝ) (m : ℕ) (τ : ℝ) : ℂ :=
  Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ) *
    (archDigammaAllTerm (τ / 2) m : ℂ)

private theorem continuous_paperFT_source_series
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

private theorem continuous_archDigammaAllTerm_half (m : ℕ) :
    Continuous (fun τ : ℝ => archDigammaAllTerm (τ / 2) m) := by
  unfold archDigammaAllTerm
  apply Continuous.sub continuous_const
  exact continuous_const.div (by fun_prop) (fun τ => by positivity)

/-- Pointwise norm bound for one literature-gamma digamma summand. -/
theorem norm_sourceArchDigammaIntegrand_le
    {L : ℝ} (n : ℤ) (m : ℕ) (τ : ℝ) :
    ‖sourceArchDigammaIntegrand n L m τ‖ ≤
      archHalfWeight m *
        (‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2|) := by
  have ht0 := archDigammaAllTerm_nonneg (τ / 2) m
  have htle := archDigammaAllTerm_le_sqrt_weight (τ / 2) m
  have hmul := mul_le_mul_of_nonneg_left htle
    (norm_nonneg (Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)))
  unfold sourceArchDigammaIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Every positive-abscissa summand is absolutely integrable in the literature
frequency variable. -/
theorem integrable_sourceArchDigammaIntegrand
    {L : ℝ} (hL : 0 < L) (n : ℤ) (m : ℕ) :
    Integrable (sourceArchDigammaIntegrand n L m) := by
  have hW := integrable_norm_paperFT_dictionarySourceTest_mul_sqrt hL n
  have hw0 : 0 ≤ archHalfWeight m := by
    unfold archHalfWeight
    positivity
  have hmajor : Integrable (fun τ : ℝ =>
      archHalfWeight m *
        (‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
          Real.sqrt |τ / 2|)) :=
    hW.const_mul (archHalfWeight m)
  have hcont : Continuous (sourceArchDigammaIntegrand n L m) := by
    unfold sourceArchDigammaIntegrand
    exact (continuous_paperFT_source_series hL n).mul
      (Complex.continuous_ofReal.comp (continuous_archDigammaAllTerm_half m))
  refine hmajor.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with τ
  have hmaj0 : 0 ≤ archHalfWeight m *
      (‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
        Real.sqrt |τ / 2|) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hmaj0]
  exact norm_sourceArchDigammaIntegrand_le n m τ

/-- The integral norms of the literature-gamma summands form a summable
series.  This is the exact absolute-convergence certificate used for the
`τ ↔ m` interchange. -/
theorem summable_integral_norm_sourceArchDigammaIntegrand
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Summable (fun m : ℕ =>
      ∫ τ : ℝ, ‖sourceArchDigammaIntegrand n L m τ‖) := by
  let W : ℝ → ℝ := fun τ =>
    ‖Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ)‖ *
      Real.sqrt |τ / 2|
  let J : ℝ := ∫ τ : ℝ, W τ
  have hW : Integrable W := by
    simpa [W] using integrable_norm_paperFT_dictionarySourceTest_mul_sqrt hL n
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun τ => by
      dsimp [W]
      positivity
  have hbound : ∀ m : ℕ,
      (∫ τ : ℝ, ‖sourceArchDigammaIntegrand n L m τ‖) ≤
        archHalfWeight m * J := by
    intro m
    have htarget := (integrable_sourceArchDigammaIntegrand hL n m).norm
    have hw0 : 0 ≤ archHalfWeight m := by
      unfold archHalfWeight
      positivity
    have hmajor : Integrable (fun τ : ℝ => archHalfWeight m * W τ) :=
      hW.const_mul (archHalfWeight m)
    have hle : ∀ τ : ℝ,
        ‖sourceArchDigammaIntegrand n L m τ‖ ≤ archHalfWeight m * W τ := by
      intro τ
      simpa [W] using norm_sourceArchDigammaIntegrand_le (L := L) n m τ
    have hi := integral_mono htarget hmajor hle
    dsimp [J]
    simpa [W, integral_const_mul] using hi
  have hmaj : Summable (fun m : ℕ => J * archHalfWeight m) :=
    summable_archHalfWeight.mul_left J
  refine Summable.of_norm_bounded hmaj ?_
  intro m
  have hi0 : 0 ≤ ∫ τ : ℝ, ‖sourceArchDigammaIntegrand n L m τ‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hi0]
  simpa [mul_comm] using hbound m

/-- Certified interchange of the positive-abscissa series with the actual
literature gamma-frequency integral for a source test. -/
theorem tsum_integral_sourceArchDigammaIntegrand_eq_integral_tsum
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∑' m : ℕ, ∫ τ : ℝ, sourceArchDigammaIntegrand n L m τ) =
      ∫ τ : ℝ, ∑' m : ℕ, sourceArchDigammaIntegrand n L m τ := by
  exact integral_tsum_of_summable_integral_norm
    (fun m => integrable_sourceArchDigammaIntegrand hL n m)
    (summable_integral_norm_sourceArchDigammaIntegrand hL n)

/-- Pointwise collapse of the complex-cast positive-abscissa series. -/
theorem tsum_sourceArchDigammaIntegrand_eq
    {L : ℝ} (n : ℤ) (τ : ℝ) :
    (∑' m : ℕ, sourceArchDigammaIntegrand n L m τ) =
      Zeta23.paperFT (dictionarySourceTest n L) (τ : ℂ) *
        ((∑' m : ℕ, archDigammaAllTerm (τ / 2) m : ℝ) : ℂ) := by
  unfold sourceArchDigammaIntegrand
  rw [tsum_mul_left]
  rw [RCLike.ofReal_tsum]

end Zeta23.CCM
