import Zeta23.OPICASupport.NativeParityActual.ActualZeroSampling
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates

/-!
Exact complex-linear interpolation on the unchanged native physical moment
slices.  Every evaluation is the positive-sign `paperFT` of the original
localized finite vector.  The sample conditions remain explicit in the
generic maps and bijectivity theorems.  Actual-zero existence uses the accepted
square-distinct nonresonant sampler, with no C1 or RH premise.

These are linear isomorphisms, not isometries.  No effective conditioning,
uniform bound, energy sign, or claim about nonlinear measurements is made.
-/

noncomputable section

namespace Zeta23.OPICARound21.NativeSliceInterpolation

open CCM OPICARound4.ArithmeticFrontier OPICARound20
open OPICARound20.NativeParityRational OPICARound21.NativeParityActual
open scoped BigOperators

theorem paperFT_localized_coefficients_add {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hexp : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    paperFT (localizedFiniteVector L K (u + v)) z =
      paperFT (localizedFiniteVector L K u) z +
        paperFT (localizedFiniteVector L K v) z := by
  have hden := fun i : Fin (2 * K + 1) =>
    paperModeDenominator_ne_zero_of_exp_ne_one hL z hexp (centeredIndex K i)
  rw [paperFT_localizedFiniteVector_eq_rational hL K (u + v) z hden,
    paperFT_localizedFiniteVector_eq_rational hL K u z hden,
    paperFT_localizedFiniteVector_eq_rational hL K v z hden]
  simp only [Pi.add_apply, add_div, Finset.sum_add_distrib, mul_add]

theorem paperFT_localized_coefficients_smul {L : ℝ} (hL : 0 < L) (K : ℕ)
    (a : ℂ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hexp : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    paperFT (localizedFiniteVector L K (a • u)) z =
      a • paperFT (localizedFiniteVector L K u) z := by
  have hden := fun i : Fin (2 * K + 1) =>
    paperModeDenominator_ne_zero_of_exp_ne_one hL z hexp (centeredIndex K i)
  rw [paperFT_localizedFiniteVector_eq_rational hL K (a • u) z hden,
    paperFT_localizedFiniteVector_eq_rational hL K u z hden]
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← Finset.mul_sum]
  ring

def evenFourierEvaluation {κ : Type*} {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1) :
    evenMomentSlice L K →ₗ[ℂ] (κ → ℂ) where
  toFun u j :=
    paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u.val)) (z j)
  map_add' u v := by
    funext j
    exact paperFT_localized_coefficients_add hL K _ _ _ (hexp j)
  map_smul' a u := by
    funext j
    exact paperFT_localized_coefficients_smul hL K a _ _ (hexp j)

def oddFourierEvaluation {κ : Type*} {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1) :
    oddMomentSlice L K →ₗ[ℂ] (κ → ℂ) where
  toFun u j :=
    paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u.val)) (z j)
  map_add' u v := by
    funext j
    exact paperFT_localized_coefficients_add hL K _ _ _ (hexp j)
  map_smul' a u := by
    funext j
    exact paperFT_localized_coefficients_smul hL K a _ _ (hexp j)

theorem evenFourierEvaluation_apply {κ : Type*} {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (u : evenMomentSlice L K) (j : κ) :
    evenFourierEvaluation hL K z hexp u j =
      paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u.val)) (z j) := rfl

theorem oddFourierEvaluation_apply {κ : Type*} {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (u : oddMomentSlice L K) (j : κ) :
    oddFourierEvaluation hL K z hexp u j =
      paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u.val)) (z j) := rfl

theorem evenFourierEvaluation_injective {κ : Type*} [Fintype κ] {L : ℝ}
    (hL : 0 < L) (K : ℕ) (z : κ → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 3 ≤ Fintype.card κ) :
    Function.Injective (evenFourierEvaluation hL K z hexp) :=
  evenMomentSlice_paperFT_sampling_injective hL K z hzsq hexp hzpole hcard

theorem oddFourierEvaluation_injective {κ : Type*} [Fintype κ] {L : ℝ}
    (hL : 0 < L) (K : ℕ) (z : κ → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 4 ≤ Fintype.card κ) :
    Function.Injective (oddFourierEvaluation hL K z hexp) :=
  oddMomentSlice_paperFT_sampling_injective hL K z hzsq hexp hzpole hcard

theorem evenFourierEvaluation_bijective {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) (z : Fin (K - 3) → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ)) :
    Function.Bijective (evenFourierEvaluation hL K z hexp) := by
  have hinj : Function.Injective (evenFourierEvaluation hL K z hexp) :=
    evenFourierEvaluation_injective hL K z hzsq hexp hzpole (by simp)
  have hdim : Module.finrank ℂ (evenMomentSlice L K) =
      Module.finrank ℂ (Fin (K - 3) → ℂ) := by
    simpa only [Module.finrank_fin_fun] using finrank_evenMomentSlice hL K hK
  exact (LinearMap.linearEquivOfInjective
    (K := ℂ) (V := evenMomentSlice L K) (V₂ := Fin (K - 3) → ℂ)
    (evenFourierEvaluation hL K z hexp) hinj hdim).bijective

theorem oddFourierEvaluation_bijective {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) (z : Fin (K - 4) → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ)) :
    Function.Bijective (oddFourierEvaluation hL K z hexp) := by
  have hinj : Function.Injective (oddFourierEvaluation hL K z hexp) :=
    oddFourierEvaluation_injective hL K z hzsq hexp hzpole (by simp)
  have hdim : Module.finrank ℂ (oddMomentSlice L K) =
      Module.finrank ℂ (Fin (K - 4) → ℂ) := by
    simpa only [Module.finrank_fin_fun] using finrank_oddMomentSlice hL K hK
  exact (LinearMap.linearEquivOfInjective
    (K := ℂ) (V := oddMomentSlice L K) (V₂ := Fin (K - 4) → ℂ)
    (oddFourierEvaluation hL K z hexp) hinj hdim).bijective

theorem evenFourierEvaluation_unique_interpolation {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) (z : Fin (K - 3) → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ)) (y : Fin (K - 3) → ℂ) :
    ∃! u : evenMomentSlice L K, evenFourierEvaluation hL K z hexp u = y := by
  obtain ⟨u, hu⟩ := (evenFourierEvaluation_bijective hL K hK z hzsq hexp hzpole).2 y
  exact ⟨u, hu, fun v hv =>
    (evenFourierEvaluation_bijective hL K hK z hzsq hexp hzpole).1 (hv.trans hu.symm)⟩

theorem oddFourierEvaluation_unique_interpolation {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) (z : Fin (K - 4) → ℂ)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ)) (y : Fin (K - 4) → ℂ) :
    ∃! u : oddMomentSlice L K, oddFourierEvaluation hL K z hexp u = y := by
  obtain ⟨u, hu⟩ := (oddFourierEvaluation_bijective hL K hK z hzsq hexp hzpole).2 y
  exact ⟨u, hu, fun v hv =>
    (oddFourierEvaluation_bijective hL K hK z hzsq hexp hzpole).1 (hv.trans hu.symm)⟩

theorem exists_even_actual_zero_interpolation {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) :
    ∃ ρ : Fin (K - 3) → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j) ^ 2) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      (∀ j, gammaOf (ρ j) ^ 2 ≠ -(1 / 4 : ℂ)) ∧
      ∀ y : Fin (K - 3) → ℂ, ∃! u : evenMomentSlice L K,
        (fun j => paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u.val))
          (gammaOf (ρ j))) = y := by
  obtain ⟨ρ, hsq, hexp, hpole, _hzero⟩ :=
    actual_square_distinct_nonresonant_samples hL (K - 3)
  exact ⟨ρ, hsq, hexp, hpole, fun y =>
    evenFourierEvaluation_unique_interpolation hL K hK _ hsq hexp hpole y⟩

theorem exists_odd_actual_zero_interpolation {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 2 ≤ K) :
    ∃ ρ : Fin (K - 4) → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j) ^ 2) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      (∀ j, gammaOf (ρ j) ^ 2 ≠ -(1 / 4 : ℂ)) ∧
      ∀ y : Fin (K - 4) → ℂ, ∃! u : oddMomentSlice L K,
        (fun j => paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u.val))
          (gammaOf (ρ j))) = y := by
  obtain ⟨ρ, hsq, hexp, hpole, _hzero⟩ :=
    actual_square_distinct_nonresonant_samples hL (K - 4)
  exact ⟨ρ, hsq, hexp, hpole, fun y =>
    oddFourierEvaluation_unique_interpolation hL K hK _ hsq hexp hpole y⟩

theorem even_fewer_linear_evaluations_not_injective {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (m : ℕ) (hm : m < K - 3)
    (f : evenMomentSlice L K →ₗ[ℂ] (Fin m → ℂ)) : ¬ Function.Injective f := by
  intro hinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_evenMomentSlice hL K hK, Module.finrank_fin_fun] at hle
  omega

theorem odd_fewer_linear_evaluations_not_injective {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (m : ℕ) (hm : m < K - 4)
    (f : oddMomentSlice L K →ₗ[ℂ] (Fin m → ℂ)) : ¬ Function.Injective f := by
  intro hinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_oddMomentSlice hL K hK, Module.finrank_fin_fun] at hle
  omega

end Zeta23.OPICARound21.NativeSliceInterpolation
