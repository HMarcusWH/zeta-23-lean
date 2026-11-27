import Zeta23.OPICASupport.NativeParityRational.MomentSliceIdentification

/-!
Sharp parity-folded sample bounds on the exact native moment slices.
Samples avoid the complete exponential lattice and the physical poles ±I/2;
their squares, rather than just their values, must be pairwise distinct.
All cutoffs are retained, including the zero-carrier low-cutoff cases.
-/

noncomputable section

namespace Zeta23.OPICARound20.NativeParityRational

open CCM OPICARound4.ArithmeticFrontier Polynomial
open scoped BigOperators

theorem half_imaginary_sq : (Complex.I / 2) ^ 2 = -(1 / 4 : ℂ) := by
  rw [div_pow, Complex.I_sq]
  norm_num

theorem evenPhysicalNumerator_pole_factorization {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralEvenSubspace L K) :
    ∃ R : ℂ[X], finiteCauchyNumerator (physicalPole L K) (evenPhysicalCoefficients u) =
      (X ^ 2 + C (1 / 4)) * R.comp (X ^ 2) := by
  obtain ⟨Q, hQ⟩ := evenPhysicalNumerator_square_form u
  obtain ⟨R, hR⟩ := ParityRational.even_pole_factorization Q (Complex.I / 2)
    (hQ ▸ evenPhysicalNumerator_half_imaginary_root hL u)
  refine ⟨R, hQ.trans ?_⟩
  simpa only [half_imaginary_sq, map_neg, sub_neg_eq_add] using hR

theorem oddPhysicalNumerator_pole_factorization {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralOddSubspace L K) :
    ∃ R : ℂ[X], finiteCauchyNumerator (physicalPole L K) (oddPhysicalCoefficients u) =
      X * (X ^ 2 + C (1 / 4)) * R.comp (X ^ 2) := by
  obtain ⟨Q, hQ⟩ := oddPhysicalNumerator_square_form u
  obtain ⟨R, hR⟩ := ParityRational.odd_pole_factorization Q (Complex.I / 2)
    (div_ne_zero Complex.I_ne_zero (by norm_num))
    (hQ ▸ oddPhysicalNumerator_half_imaginary_root hL u)
  refine ⟨R, hQ.trans ?_⟩
  simpa only [half_imaginary_sq, map_neg, sub_neg_eq_add] using hR

theorem evenMomentSlice_paperFT_samples_force_zero
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralEvenSubspace L K) (hu : u ∈ evenMomentSlice L K)
    (z : κ → ℂ) (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 3 ≤ Fintype.card κ)
    (hzero : ∀ j, paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u)) (z j) = 0) :
    u = 0 := by
  obtain ⟨Q, hQ⟩ := evenPhysicalNumerator_square_form u
  have hc : evenPhysicalCoefficients u = 0 := by
    apply ParityRational.even_six_moment_samples_force_coefficients K
      (physicalPole L K) (evenPhysicalCoefficients u) Q (Complex.I / 2) hQ
      (evenPhysicalNumerator_half_imaginary_root hL u) z (physicalPole_injective hL K)
      hzsq (fun j => physicalPole_ne_of_nonresonance hL K (z j) (hexp j))
      (by simpa only [half_imaginary_sq] using hzpole)
      (physicalPole_moment_prefix L K 6 _ (evenMomentSlice_centered_moments u hu)) hcard
    intro j
    rw [finiteCauchySum_physicalPole_eq]
    exact (paperFT_localizedFiniteVector_zero_iff_rational_sum_zero hL K _ _ (hexp j)).mp
      (hzero j)
  apply Subtype.ext
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  simpa [evenPhysicalCoefficients] using hc

theorem oddMomentSlice_paperFT_samples_force_zero
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralOddSubspace L K) (hu : u ∈ oddMomentSlice L K)
    (z : κ → ℂ) (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 4 ≤ Fintype.card κ)
    (hzero : ∀ j, paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u)) (z j) = 0) :
    u = 0 := by
  obtain ⟨Q, hQ⟩ := oddPhysicalNumerator_square_form u
  have hc : oddPhysicalCoefficients u = 0 := by
    apply ParityRational.odd_seven_moment_samples_force_coefficients K
      (physicalPole L K) (oddPhysicalCoefficients u) Q (Complex.I / 2)
      (div_ne_zero Complex.I_ne_zero (by norm_num)) hQ
      (oddPhysicalNumerator_half_imaginary_root hL u) z (physicalPole_injective hL K)
      hzsq (fun j => physicalPole_ne_of_nonresonance hL K (z j) (hexp j))
      (fun j hj => hexp j (by simp [hj]))
      (by simpa only [half_imaginary_sq] using hzpole)
      (physicalPole_moment_prefix L K 7 _ (oddMomentSlice_centered_moments u hu)) hcard
    intro j
    rw [finiteCauchySum_physicalPole_eq]
    exact (paperFT_localizedFiniteVector_zero_iff_rational_sum_zero hL K _ _ (hexp j)).mp
      (hzero j)
  apply Subtype.ext
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  simpa [oddPhysicalCoefficients] using hc

theorem paperFT_localized_coefficients_sub {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hexp : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    paperFT (localizedFiniteVector L K (u - v)) z =
      paperFT (localizedFiniteVector L K u) z - paperFT (localizedFiniteVector L K v) z := by
  have hden := fun i : Fin (2 * K + 1) =>
    paperModeDenominator_ne_zero_of_exp_ne_one hL z hexp (centeredIndex K i)
  rw [paperFT_localizedFiniteVector_eq_rational hL K (u - v) z hden,
    paperFT_localizedFiniteVector_eq_rational hL K u z hden,
    paperFT_localizedFiniteVector_eq_rational hL K v z hden]
  simp only [Pi.sub_apply, sub_div, Finset.sum_sub_distrib, mul_sub]

theorem evenMomentSlice_paperFT_sampling_injective
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 3 ≤ Fintype.card κ) :
    Function.Injective
      (fun u : evenMomentSlice L K =>
        fun j => paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u.val)) (z j)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply evenMomentSlice_paperFT_samples_force_zero hL (u - v).val (u - v).property
    z hzsq hexp hzpole hcard
  intro j
  have hraw : evenPhysicalCoefficients (u - v).val =
      evenPhysicalCoefficients u.val - evenPhysicalCoefficients v.val := rfl
  rw [hraw, paperFT_localized_coefficients_sub hL K _ _ _ (hexp j)]
  exact sub_eq_zero.mpr (congrFun huv j)

theorem oddMomentSlice_paperFT_sampling_injective
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hzsq : Function.Injective (fun j => z j ^ 2))
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hzpole : ∀ j, z j ^ 2 ≠ -(1 / 4 : ℂ))
    (hcard : K - 4 ≤ Fintype.card κ) :
    Function.Injective
      (fun u : oddMomentSlice L K =>
        fun j => paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u.val)) (z j)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply oddMomentSlice_paperFT_samples_force_zero hL (u - v).val (u - v).property
    z hzsq hexp hzpole hcard
  intro j
  have hraw : oddPhysicalCoefficients (u - v).val =
      oddPhysicalCoefficients u.val - oddPhysicalCoefficients v.val := rfl
  rw [hraw, paperFT_localized_coefficients_sub hL K _ _ _ (hexp j)]
  exact sub_eq_zero.mpr (congrFun huv j)

theorem evenMomentSlice_low_cutoff_zero {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : K ≤ 3)
    (u : poleNeutralEvenSubspace L K) (hu : u ∈ evenMomentSlice L K) : u = 0 := by
  exact evenMomentSlice_paperFT_samples_force_zero hL u hu
    (fun j : Fin 0 => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (by simp; omega) (fun j => j.elim0)

theorem oddMomentSlice_low_cutoff_zero {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : K ≤ 4)
    (u : poleNeutralOddSubspace L K) (hu : u ∈ oddMomentSlice L K) : u = 0 := by
  exact oddMomentSlice_paperFT_samples_force_zero hL u hu
    (fun j : Fin 0 => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (by simp; omega) (fun j => j.elim0)

end Zeta23.OPICARound20.NativeParityRational
