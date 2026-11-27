import Zeta23.OPICASupport.OPICAStep4.FiniteCauchySampling
import Zeta23.CCM.BoundaryFlatFiniteSpace

/-!
# The finite rational sampling theorem on the actual boundary-flat carrier

This specializes the field lemma to the unchanged native `centeredIndex` and
`BoundaryFlatCoefficients`.  It does not identify the rational expression with
`paperFT`; that analytic identity and the supply of nonresonant actual zeros
remain separate obligations.
-/

noncomputable section

namespace Zeta23.OPICARound20

open scoped BigOperators
open CCM

theorem boundaryFlat_scaled_moments (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) (ω : ℂ) :
    ∀ k < 3, ∑ i, (ω * (centeredIndex K i : ℂ)) ^ k * u i = 0 := by
  intro k hk
  have hmoment : centeredMoment K k u = 0 := by
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h
    · simpa [h] using hflat.1
    · simpa [h] using hflat.2.1
    · simpa [h] using hflat.2.2
  simp_rw [mul_pow, mul_assoc]
  rw [← Finset.mul_sum]
  change ω ^ k * centeredMoment K k u = 0
  rw [hmoment, mul_zero]

/-- On the native three-moment-flat coefficient space, `2*K-2` distinct
samples away from the scaled centered poles determine the coefficient vector.
The natural-number subtraction includes the zero-dimensional `K=0,1` cases. -/
theorem boundaryFlat_rational_samples_force_coefficients
    {κ : Type*} [Fintype κ] (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) (ω : ℂ) (hω : ω ≠ 0)
    (z : κ → ℂ) (hz : Function.Injective z)
    (hza : ∀ j i, z j ≠ ω * (centeredIndex K i : ℂ))
    (hcard : 2 * K - 2 ≤ Fintype.card κ)
    (hzero : ∀ j,
      finiteCauchySum (fun i => ω * (centeredIndex K i : ℂ)) u (z j) = 0) : u = 0 := by
  apply finiteCauchySum_zero_forces_coefficients
    (fun i => ω * (centeredIndex K i : ℂ)) u z 3
  · intro i j hij
    exact centeredIndex_injective K (Int.cast_injective (mul_left_cancel₀ hω hij))
  · exact hz
  · exact hza
  · exact boundaryFlat_scaled_moments K u hflat ω
  · simp only [Fintype.card_fin]
    omega
  · exact hzero

/-- The rational sampling map is injective on the actual native boundary-flat
carrier.  Its target has one complex coordinate per distinct sample point. -/
theorem boundaryFlat_rational_sampling_injective
    {κ : Type*} [Fintype κ] (K : ℕ) (ω : ℂ) (hω : ω ≠ 0)
    (z : κ → ℂ) (hz : Function.Injective z)
    (hza : ∀ j i, z j ≠ ω * (centeredIndex K i : ℂ))
    (hcard : 2 * K - 2 ≤ Fintype.card κ) :
    Function.Injective
      (fun u : {u : Fin (2 * K + 1) → ℂ // BoundaryFlatCoefficients K u} =>
        fun j => finiteCauchySum (fun i => ω * (centeredIndex K i : ℂ)) u.val (z j)) := by
  intro u v huv
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hm (k : ℕ) : centeredMoment K k (u.val - v.val) =
      centeredMoment K k u.val - centeredMoment K k v.val := by
    simp [centeredMoment, mul_sub, Finset.sum_sub_distrib]
  have hflat : BoundaryFlatCoefficients K (u.val - v.val) := by
    exact ⟨by rw [hm, u.property.1, v.property.1, sub_self],
      by rw [hm, u.property.2.1, v.property.2.1, sub_self],
      by rw [hm, u.property.2.2, v.property.2.2, sub_self]⟩
  apply boundaryFlat_rational_samples_force_coefficients K (u.val - v.val) hflat ω hω
    z hz hza hcard
  intro j
  have heq := congrFun huv j
  simp only [finiteCauchySum, Pi.sub_apply, sub_div, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr heq

/-- The low-cutoff boundary-flat carriers vanish without taking samples. -/
theorem boundaryFlat_coefficients_zero_of_cutoff_le_one
    (K : ℕ) (hK : K ≤ 1) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) : u = 0 := by
  exact boundaryFlat_rational_samples_force_coefficients K u hflat 1 one_ne_zero
    (fun j : Fin 0 => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (by simp; omega) (fun j => j.elim0)

end Zeta23.OPICARound20
