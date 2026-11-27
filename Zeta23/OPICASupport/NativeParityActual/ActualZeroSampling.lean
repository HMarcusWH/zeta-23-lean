import Zeta23.OPICASupport.NativeParityActual.FiniteFiberSampling
import Zeta23.OPICASupport.NativeParityRational.MomentSliceSampling
import Zeta23.OPICASupport.DensityCompatibility.ActualDistinctGrowth

/-!
Unconditional actual-zero sampling on the exact native moment slices.
The spectral coordinate remains the complex `gammaOf`; no critical-line or
real-ordinate identification is assumed. Squares have finite fibers, and
representatives are chosen after deleting the forbidden values 0 and -1/4.
-/

noncomputable section

namespace Zeta23.OPICARound21.NativeParityActual

open CCM OPICARound4.ArithmeticFrontier OPICARound20 OPICARound20.NativeParityRational
open Polynomial

theorem actual_square_distinct_nonresonant_samples {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ∃ ρ : Fin n → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j) ^ 2) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      (∀ j, gammaOf (ρ j) ^ 2 ≠ -(1 / 4 : ℂ)) ∧
      (∀ j, gammaOf (ρ j) ≠ 0) := by
  let _ : Filter.TendstoCofinite gammaOf :=
    Filter.tendstoCofinite_of_injective gammaOf_injective
  let _ : Filter.TendstoCofinite (fun z : ℂ => z ^ 2) := by
    have heval : (X ^ 2 : ℂ[X]).eval = (fun z : ℂ => z ^ 2) := by
      funext z
      simp
    rw [← heval]
    exact Polynomial.tendstoCofinite_of_natDegree_ne_zero (X ^ 2 : ℂ[X]) (by simp)
  have hs := nonresonantZeroSet_infinite_of_distinct_growth zetaZeroConfig
    DensityCompatibility.actual_distinct_window_superlinear hL
  obtain ⟨x, hx, hinj, hbad⟩ := exists_samples_with_distinct_images
    ((fun z : ℂ => z ^ 2) ∘ gammaOf) hs ({0, -(1 / 4 : ℂ)} : Set ℂ)
    (by simp) n
  let ρ : Fin n → zetaZeroConfig.carrier := fun j => ⟨x j, (hx j).1⟩
  refine ⟨ρ, hinj, fun j => (hx j).2, ?_, ?_⟩
  · intro j he
    apply hbad j
    change gammaOf (ρ j) ^ 2 ∈ ({0, -(1 / 4 : ℂ)} : Set ℂ)
    simp [he]
  · intro j he
    apply hbad j
    change gammaOf (ρ j) ^ 2 ∈ ({0, -(1 / 4 : ℂ)} : Set ℂ)
    simp [he]

theorem exists_evenMomentSlice_actual_zero_sampling {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∃ ρ : Fin (K - 3) → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j) ^ 2) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      (∀ j, gammaOf (ρ j) ^ 2 ≠ -(1 / 4 : ℂ)) ∧
      Function.Injective
        (fun u : evenMomentSlice L K =>
          fun j => paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u.val))
            (gammaOf (ρ j))) := by
  obtain ⟨ρ, hinj, hexp, hpole, _⟩ := actual_square_distinct_nonresonant_samples hL (K - 3)
  exact ⟨ρ, hinj, hexp, hpole, evenMomentSlice_paperFT_sampling_injective hL K
    (fun j => gammaOf (ρ j)) hinj hexp hpole (by simp)⟩

theorem exists_oddMomentSlice_actual_zero_sampling {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∃ ρ : Fin (K - 4) → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j) ^ 2) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      (∀ j, gammaOf (ρ j) ^ 2 ≠ -(1 / 4 : ℂ)) ∧
      Function.Injective
        (fun u : oddMomentSlice L K =>
          fun j => paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u.val))
            (gammaOf (ρ j))) := by
  obtain ⟨ρ, hinj, hexp, hpole, _⟩ := actual_square_distinct_nonresonant_samples hL (K - 4)
  exact ⟨ρ, hinj, hexp, hpole, oddMomentSlice_paperFT_sampling_injective hL K
    (fun j => gammaOf (ρ j)) hinj hexp hpole (by simp)⟩

end Zeta23.OPICARound21.NativeParityActual
