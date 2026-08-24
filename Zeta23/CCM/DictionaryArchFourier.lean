import Zeta23.CCM.DictionaryArchCompletion
import Zeta23.CCM.DictionaryTentDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform

/-! # Fourier-integrability gates for the deterministic archimedean bridge

The literature archimedean channel uses paper inversion and therefore needs an
actual `L¹` Fourier-transform hypothesis.  Continuity plus compact support of the
physical test is not enough.  This file proves the needed transform integrability
from explicit quadratic real-frequency decay.
-/

/-- A continuous complex function with a uniform bound and a global quadratic
weighted bound is integrable.  The proof compares it to the standard integrable
majorant `(1+x^2)⁻¹`. -/
private theorem integrable_of_continuous_uniform_sq
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

/-- Real-frequency continuity of the paper Fourier transform of an `L¹` test. -/
private theorem continuous_paperFT_real_of_integrable
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

/-- Convert real-frequency paper-transform integrability to Mathlib Fourier
integrability using the repository's pinned convention bridge. -/
private theorem integrable_fourier_of_integrable_paperFT
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

/-- The canonical tent's real-frequency paper transform is `L¹`.  The compact
part is controlled by the zeroth-order transform bound and the tail by the
already-certified quadratic tent decay theorem. -/
theorem integrable_paperFT_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun r : ℝ => Zeta23.paperFT (dictionaryTent L) (r : ℂ)) := by
  have hki : Integrable (dictionaryTent L) := integrable_dictionaryTent hL
  have hsupp : ∀ u : ℝ, dictionaryTent L u ≠ 0 → |u| ≤ L := by
    intro u hu
    exact abs_le.mpr (dictionaryTent_support_subset_Icc hL hu)
  let A : ℝ := ∫ u : ℝ, ‖dictionaryTent L u‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hunif : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ ≤ A := by
    intro r
    have h := Zeta23.norm_paperFT_le hki hsupp (r : ℂ)
    simpa [A] using h
  let B : ℝ := 2 * (1 + Real.exp (L / 2)) / L
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq : ∀ r : ℝ,
      ‖Zeta23.paperFT (dictionaryTent L) (r : ℂ)‖ * r ^ 2 ≤ B := by
    intro r
    have h := norm_paperFT_dictionaryTent_mul_sq_le hL (r : ℂ) (by simp)
    simpa [B, Real.norm_eq_abs, sq_abs] using h
  exact integrable_of_continuous_uniform_sq
    (continuous_paperFT_real_of_integrable hki) hA hB hunif hsq

/-- Mathlib-Fourier `L¹` gate for the canonical tent. -/
theorem integrable_fourier_dictionaryTent
    {L : ℝ} (hL : 0 < L) :
    Integrable (𝓕 (dictionaryTent L)) :=
  integrable_fourier_of_integrable_paperFT
    (integrable_paperFT_dictionaryTent hL)

/-- The diagonal production basis test has an integrable Fourier transform.  Its
paper transform is the average of two real translates of the integrable tent
transform, so no new asymptotic estimate is required. -/
theorem integrable_fourier_dictionaryBasisTest_diag
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (𝓕 (dictionaryBasisTest n n L)) := by
  have ht : Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryTent L) (r : ℂ)) :=
    integrable_paperFT_dictionaryTent hL
  let a : ℝ := dictionaryFrequency n L
  have hp : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ))) := by
    simpa only [Complex.ofReal_add] using ht.comp_add_right a
  have hm : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) := by
    simpa only [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg] using
      ht.comp_add_right (-a)
  have hsum : Integrable
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
          Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) :=
    hp.add hm
  have hhalf : Integrable
      (fun r : ℝ =>
        (1 / 2 : ℂ) *
          (Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
            Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ)))) :=
    hsum.const_mul (1 / 2 : ℂ)
  have heq :
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryBasisTest n n L) (r : ℂ)) =
        fun r : ℝ =>
          (1 / 2 : ℂ) *
            (Zeta23.paperFT (dictionaryTent L) ((r : ℂ) + (a : ℂ)) +
              Zeta23.paperFT (dictionaryTent L) ((r : ℂ) - (a : ℂ))) := by
    funext r
    rw [paperFT_dictionaryBasisTest_diag hL n (r : ℂ)]
    dsimp [a]
    ring
  have hpaper : Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryBasisTest n n L) (r : ℂ)) := by
    rw [heq]
    exact hhalf
  exact integrable_fourier_of_integrable_paperFT hpaper

end Zeta23.CCM
