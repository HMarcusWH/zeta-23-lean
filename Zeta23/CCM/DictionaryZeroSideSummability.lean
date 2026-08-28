import Zeta23.CCM.DictionaryTentZeroSummability
import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.WeilEF.ZeroSummability

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory
open scoped BigOperators

/-!
# Full finite-dictionary zero-side summability

The real finite dictionary splits exactly into the canonical tent channel and the
globally C² residual channel.  Both zero-side series are already known to converge
absolutely:

* the literal tent by `dictionaryTent_zero_sum_summable`;
* the residual by the inherited `WeilEF.EF_zero_sum_summable`.

This module combines those two facts.  It deliberately proves only absolute
convergence of the full dictionary zero side.  It does not extend the explicit
formula to the nonsmooth tent and does not identify the resulting zero sum with
`literatureRHS`.
-/

/-- Function-level version of the exact real seam decomposition. -/
theorem dictionaryTest_ofReal_eq_tent_smul_add_residual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryTest N (fun i => (u i : ℂ)) L =
      fun y =>
        ((coefficientSumReal N u) ^ 2 : ℂ) * dictionaryTent L y +
          dictionaryResidualTest N u L y := by
  funext y
  rw [dictionaryTest_ofReal_eq_tent_add_residual N u hL y]
  simp [dictionaryTent, dictionaryResidualTest]

/-- Exact transform decomposition of the full real dictionary into its literal
canonical tent transform and its smooth residual transform. -/
theorem dictionaryTransform_ofReal_eq_tent_add_residual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    dictionaryTransform N (fun i => (u i : ℂ)) L z =
      ((coefficientSumReal N u) ^ 2 : ℂ) *
          Zeta23.paperFT (dictionaryTent L) z +
        Zeta23.paperFT (dictionaryResidualTest N u L) z := by
  rw [dictionaryTransform, dictionaryTest_ofReal_eq_tent_smul_add_residual N u hL]
  unfold Zeta23.paperFT
  let c0 : ℂ := ((coefficientSumReal N u) ^ 2 : ℂ)
  have ht : Integrable
      (fun y : ℝ =>
        dictionaryTent L y * Complex.exp (Complex.I * z * y)) := by
    have hc : Continuous
        (fun y : ℝ =>
          dictionaryTent L y * Complex.exp (Complex.I * z * y)) := by
      exact (continuous_dictionaryTent L).mul (by fun_prop)
    have hs : HasCompactSupport
        (fun y : ℝ =>
          dictionaryTent L y * Complex.exp (Complex.I * z * y)) :=
      (dictionaryTent_hasCompactSupport hL).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hr : Integrable
      (fun y : ℝ =>
        dictionaryResidualTest N u L y *
          Complex.exp (Complex.I * z * y)) := by
    have hc : Continuous
        (fun y : ℝ =>
          dictionaryResidualTest N u L y *
            Complex.exp (Complex.I * z * y)) := by
      exact (contDiff_two_dictionaryResidualTest N u hL).continuous.mul (by fun_prop)
    have hs : HasCompactSupport
        (fun y : ℝ =>
          dictionaryResidualTest N u L y *
            Complex.exp (Complex.I * z * y)) :=
      (dictionaryResidualTest_hasCompactSupport N u hL).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hsplit :
      (fun y : ℝ =>
        ((((coefficientSumReal N u) ^ 2 : ℂ) * dictionaryTent L y +
            dictionaryResidualTest N u L y) *
          Complex.exp (Complex.I * z * y))) =
      fun y =>
        c0 * (dictionaryTent L y * Complex.exp (Complex.I * z * y)) +
          dictionaryResidualTest N u L y *
            Complex.exp (Complex.I * z * y) := by
    funext y
    simp only [c0]
    ring
  rw [hsplit, integral_add (ht.const_mul c0) hr, Zeta23.integral_const_mul_C]
  rfl

/-- The smooth residual contribution is absolutely summable over the concrete
zeta zeros for every real coefficient vector. -/
theorem dictionaryResidual_zero_sum_summable
    (hs : ZetaSeam)
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT (dictionaryResidualTest N u L) (gammaOf ρ)) := by
  exact Zeta23.WeilEF.EF_zero_sum_summable hs
    (contDiff_two_dictionaryResidualTest N u hL)
    (dictionaryResidualTest_hasCompactSupport N u hL)

/-- H2b analytic legality gate: for every real finite coefficient vector, the
literal full-dictionary zero-side series converges absolutely.

No explicit-formula equality is asserted here. -/
theorem dictionaryTransform_zero_sum_summable
    (hs : ZetaSeam)
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) := by
  have ht := dictionaryTent_zero_sum_summable hs hL
  have ht' : Summable (fun ρ : (zetaZeros hs).carrier =>
      ((coefficientSumReal N u) ^ 2 : ℂ) *
        (((zetaZeros hs).mult ρ : ℂ) *
          Zeta23.paperFT (dictionaryTent L) (gammaOf ρ))) :=
    ht.mul_left (((coefficientSumReal N u) ^ 2 : ℂ))
  have hr := dictionaryResidual_zero_sum_summable hs N u hL
  have hadd := ht'.add hr
  convert hadd using 1
  funext ρ
  rw [dictionaryTransform_ofReal_eq_tent_add_residual N u hL]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTransform_zero_sum_summable
