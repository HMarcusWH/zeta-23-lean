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
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ((0 : ℝ) / 2)
  rw [hT, h0]
  have hsT := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (τ / 2)
  have hs0 := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ((0 : ℝ) / 2)
  let fT : ℕ → ℝ := fun n =>
    1 / ((n : ℝ) + 1) -
      ((n : ℝ) + 1 + 1 / 4) /
        (((n : ℝ) + 1 + 1 / 4) ^ 2 + (τ / 2) ^ 2)
  let f0 : ℕ → ℝ := fun n =>
    1 / ((n : ℝ) + 1) -
      ((n : ℝ) + 1 + 1 / 4) /
        (((n : ℝ) + 1 + 1 / 4) ^ 2 + ((0 : ℝ) / 2) ^ 2)
  have hsT' : Summable fT := by simpa [fT] using hsT
  have hs0' : Summable f0 := by simpa [f0] using hs0
  have htail : (fun n : ℕ => fT n - f0 n) = archDigammaTailTerm (τ / 2) := by
    funext n
    unfold fT f0 archDigammaTailTerm
    have hb : (n : ℝ) + 1 + 1 / 4 ≠ 0 := by positivity
    field_simp [hb]
    ring
  calc
    1 / (2 * Real.pi) *
          (-Real.eulerMascheroniConstant - 1 / 4 / ((1 / 4) ^ 2 + (τ / 2) ^ 2) + ∑' n, fT n) -
        Real.log Real.pi / (2 * Real.pi) -
      (1 / (2 * Real.pi) *
          (-Real.eulerMascheroniConstant - 1 / 4 / ((1 / 4) ^ 2 + ((0 : ℝ) / 2) ^ 2) + ∑' n, f0 n) -
        Real.log Real.pi / (2 * Real.pi)) =
        (1 / (2 * Real.pi)) *
          (archDigammaBaseTerm (τ / 2) + ((∑' n, fT n) - ∑' n, f0 n)) := by
            unfold archDigammaBaseTerm
            norm_num
            ring
    _ = (1 / (2 * Real.pi)) *
          (archDigammaBaseTerm (τ / 2) + ∑' n, (fT n - f0 n)) := by
            rw [hsT'.tsum_sub hs0']
    _ = (1 / (2 * Real.pi)) *
          (archDigammaBaseTerm (τ / 2) + ∑' n, archDigammaTailTerm (τ / 2) n) := by
            rw [htail]

/-- Uniform positive-abscissa form of the digamma difference terms.  The zero
index is the isolated base term above; successor indices are exactly the tail. -/
def archDigammaAllTerm (t : ℝ) (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1 / 4) -
    ((m : ℝ) + 1 / 4) / (((m : ℝ) + 1 / 4) ^ 2 + t ^ 2)

@[simp] theorem archDigammaAllTerm_zero (t : ℝ) :
    archDigammaAllTerm t 0 = archDigammaBaseTerm t := by
  unfold archDigammaAllTerm archDigammaBaseTerm
  norm_num

@[simp] theorem archDigammaAllTerm_succ (t : ℝ) (n : ℕ) :
    archDigammaAllTerm t (n + 1) = archDigammaTailTerm t n := by
  unfold archDigammaAllTerm archDigammaTailTerm
  push_cast
  ring

/-- The uniform positive-abscissa series is summable. -/
theorem summable_archDigammaAllTerm (t : ℝ) :
    Summable (archDigammaAllTerm t) := by
  rw [← summable_nat_add_iff 1]
  simpa using summable_archDigammaTailTerm t

/-- Reinsert the isolated zero index into the digamma tail. -/
theorem archDigammaBase_add_tail_eq_all_tsum (t : ℝ) :
    archDigammaBaseTerm t + ∑' n : ℕ, archDigammaTailTerm t n =
      ∑' m : ℕ, archDigammaAllTerm t m := by
  have h := (summable_archDigammaAllTerm t).sum_add_tsum_nat_add 1
  simpa using h.symm

/-- Exact positive-abscissa series representation of the gamma density difference. -/
theorem mu_sub_mu_zero_eq_archDigammaAllSeries (τ : ℝ) :
    Zeta23.mu τ - Zeta23.mu 0 =
      (1 / (2 * Real.pi)) * ∑' m : ℕ, archDigammaAllTerm (τ / 2) m := by
  rw [mu_sub_mu_zero_eq_archDigammaSeries,
    archDigammaBase_add_tail_eq_all_tsum]

end Zeta23.CCM
