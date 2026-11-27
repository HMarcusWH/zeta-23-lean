import Zeta23.OPICASupport.FourierBridge.FiniteFourierRational
import Zeta23.OPICASupport.OPICAStep4.BoundaryFlatRationalSampling

/-!
# Native boundary-flat finite Fourier sampling

This composes the exact native paper-transform identity with the verified
three-moment-flat Cauchy sampling theorem. Samples must avoid the whole
exponential resonance lattice, not merely the finitely many modal poles.
No zeta-zero supply, density premise, positivity, C1 or RH premise is used.
-/

noncomputable section

namespace Zeta23.OPICARound20

open CCM
open scoped BigOperators

/-- `2*K-2` distinct complex samples away from the full exponential resonance
lattice determine every coefficient in the actual native boundary-flat carrier. -/
theorem boundaryFlat_paperFT_sampling_injective
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : κ → ℂ) (hz : Function.Injective z)
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hcard : 2 * K - 2 ≤ Fintype.card κ) :
    Function.Injective
      (fun u : {u : Fin (2 * K + 1) → ℂ // BoundaryFlatCoefficients K u} =>
        fun j => paperFT (localizedFiniteVector L K u.val) (z j)) := by
  let ω : ℂ := -((2 * Real.pi / L : ℝ) : ℂ)
  have hω : ω ≠ 0 := by
    dsimp [ω]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL.ne'))
  have hpole : ∀ j i, z j ≠ ω * (centeredIndex K i : ℂ) := by
    intro j i
    have hden := paperModeDenominator_ne_zero_of_exp_ne_one hL (z j) (hexp j)
      (centeredIndex K i)
    intro hij
    apply hden
    rw [hij]
    dsimp [ω]
    ring
  intro u v huv
  apply boundaryFlat_rational_sampling_injective K ω hω z hz hpole hcard
  funext j
  have hu : paperFT (localizedFiniteVector L K u.val) (z j) =
      paperFT (localizedFiniteVector L K v.val) (z j) := congrFun huv j
  have hden : ∀ i : Fin (2 * K + 1),
      z j + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ) ≠ 0 :=
    fun i => paperModeDenominator_ne_zero_of_exp_ne_one hL (z j) (hexp j) (centeredIndex K i)
  rw [paperFT_localizedFiniteVector_eq_rational hL K u.val (z j) hden,
      paperFT_localizedFiniteVector_eq_rational hL K v.val (z j) hden] at hu
  have hscale : (Complex.exp (Complex.I * z j * (L : ℂ)) - 1) /
      (Complex.I * (Real.sqrt L : ℂ)) ≠ 0 := finiteFourierScale_ne_zero hL (z j) (hexp j)
  have heq := mul_left_cancel₀ hscale hu
  simpa [finiteCauchySum, ω, neg_mul, sub_neg_eq_add] using heq

/-- Equivalent vanishing formulation on the unchanged coefficient vector. -/
theorem boundaryFlat_paperFT_samples_force_coefficients
    {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (z : κ → ℂ) (hz : Function.Injective z)
    (hexp : ∀ j, Complex.exp (Complex.I * z j * (L : ℂ)) ≠ 1)
    (hcard : 2 * K - 2 ≤ Fintype.card κ)
    (hzero : ∀ j, paperFT (localizedFiniteVector L K u) (z j) = 0) : u = 0 := by
  have hflat0 : BoundaryFlatCoefficients K (0 : Fin (2 * K + 1) → ℂ) := by
    simp [BoundaryFlatCoefficients, centeredMoment]
  have hsame : (⟨u, hflat⟩ : {u : Fin (2 * K + 1) → ℂ // BoundaryFlatCoefficients K u}) =
      ⟨0, hflat0⟩ := by
    apply boundaryFlat_paperFT_sampling_injective hL K z hz hexp hcard
    funext j
    simp only [hzero]
    simp [paperFT, localizedFiniteVector]
  exact congrArg Subtype.val hsame

end Zeta23.OPICARound20

#print axioms Zeta23.OPICARound20.boundaryFlat_paperFT_sampling_injective
#print axioms Zeta23.OPICARound20.boundaryFlat_paperFT_samples_force_coefficients
