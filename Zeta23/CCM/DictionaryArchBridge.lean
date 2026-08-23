import Zeta23.CCM.DictionaryArchPhysical
import Zeta23.GammaFacts.Mu
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators Interval

/-! # Gamma/digamma bridge for the finite dictionary

This file proves only the exact archimedean representation needed by R003.
It does not invoke the explicit formula or any zero sum.
-/

/-- The isolated `a = 1/4` term in the real digamma vertical-line difference. -/
def archDigammaBaseTerm (t : ℝ) : ℝ :=
  4 - (1 / 4 : ℝ) / ((1 / 4 : ℝ) ^ 2 + t ^ 2)

/-- The summable tail in the `a = 1/4` real digamma vertical-line difference. -/
def archDigammaTailTerm (t : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1 + 1 / 4) -
    ((n : ℝ) + 1 + 1 / 4) /
      (((n : ℝ) + 1 + 1 / 4) ^ 2 + t ^ 2)

/-- The difference tail is summable.  This is inherited directly from the
compiler-proved vertical-line digamma series at `t` and at `0`. -/
theorem summable_archDigammaTailTerm (t : ℝ) :
    Summable (archDigammaTailTerm t) := by
  have hsT := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) t
  have hs0 := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  have hsub := hsT.sub hs0
  refine hsub.congr ?_
  intro n
  unfold archDigammaTailTerm
  have hb : (n : ℝ) + 1 + 1 / 4 ≠ 0 := by positivity
  field_simp [hb]
  ring

/-- Exact series form of `mu(τ) - mu(0)`.  Constants cancel before any
Fourier/integral manipulation, which is the normalization-safe route used below. -/
theorem mu_sub_mu_zero_eq_archDigammaSeries (τ : ℝ) :
    Zeta23.mu τ - Zeta23.mu 0 =
      (1 / (2 * Real.pi)) *
        (archDigammaBaseTerm (τ / 2) +
          ∑' n : ℕ, archDigammaTailTerm (τ / 2) n) := by
  rw [Zeta23.MuFields.mu_eq, Zeta23.MuFields.mu_eq]
  have hT := Zeta23.MuFields.re_digamma_vertical
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (τ / 2)
  have h0 := Zeta23.MuFields.re_digamma_vertical
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  rw [hT, h0]
  have hsT := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (τ / 2)
  have hs0 := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  rw [← hsT.tsum_sub hs0]
  have htail :
      (fun n : ℕ =>
        (1 / ((n : ℝ) + 1) -
            ((n : ℝ) + 1 + 1 / 4) /
              (((n : ℝ) + 1 + 1 / 4) ^ 2 + (τ / 2) ^ 2)) -
          (1 / ((n : ℝ) + 1) -
            ((n : ℝ) + 1 + 1 / 4) /
              (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2))) =
        archDigammaTailTerm (τ / 2) := by
    funext n
    unfold archDigammaTailTerm
    have hb : (n : ℝ) + 1 + 1 / 4 ≠ 0 := by positivity
    field_simp [hb]
    ring
  rw [htail]
  unfold archDigammaBaseTerm
  field_simp [Real.pi_ne_zero]
  ring

end Zeta23.CCM
