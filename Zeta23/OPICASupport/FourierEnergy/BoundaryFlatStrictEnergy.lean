import Zeta23.OPICASupport.FourierBridge.BoundaryFlatFourierSampling
import Zeta23.OPICASupport.OPICAStep4.BoundaryFlatGram

/-!
# Conditional strict positivity from actual nonresonant zero samples

The sample supply and the native C1 contract remain separate visible premises.
The sample premise alone is an injectivity input; this module does not supply
C1, RH, or an unconditional positivity claim.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.OPICARound20

/-- Exactly the actual-zero sampling premise needed at the fixed native
aperture and cutoff. Multiplicity does not count toward distinct samples. -/
def NonresonantActualZeroSamples (L : ℝ) (K : ℕ) : Prop :=
  ∃ ρ : Fin (2 * K - 2) → zetaZeroConfig.carrier,
    Function.Injective (fun j => gammaOf (ρ j)) ∧
      ∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1

/-- Sampling injectivity yields a nonzero actual-zero transform sample for
every nonzero native boundary-flat vector, without a C1 premise. -/
theorem boundaryFlat_exists_nonzero_actual_sample_of_supply
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (hne : u ≠ 0) :
    ∃ ρ : zetaZeroConfig.carrier,
      paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) ≠ 0 := by
  classical
  rcases hsamples with ⟨ρ, hρ, hexp⟩
  by_contra h
  apply hne
  apply boundaryFlat_paperFT_samples_force_coefficients hL K u hflat
    (fun j => gammaOf (ρ j)) hρ hexp (by simp)
  intro j
  by_contra hj
  exact h ⟨ρ j, hj⟩

/-- The native C1 contract plus a separate usable actual-zero sample supply
makes the complete canonical energy strictly positive on every nonzero BF vector. -/
theorem canonicalSourceEnergy_pos_of_c1_and_nonresonant_samples
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (hne : u ≠ 0) :
    0 < (quadraticForm (canonicalSourceMatrix L K) u).re :=
  (canonicalSourceEnergy_pos_iff_exists_nonzero_sample_of_c1 hC1 hL K u hflat).mpr
    (boundaryFlat_exists_nonzero_actual_sample_of_supply hL K hsamples u hflat hne)

/-- Under the two explicit premises, the canonical form has no nonzero
boundary-flat null vector. -/
theorem canonicalSourceEnergy_zero_iff_coefficients_zero_of_c1_and_samples
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u) :
    (quadraticForm (canonicalSourceMatrix L K) u).re = 0 ↔ u = 0 := by
  constructor
  · intro hz
    by_contra hne
    have hp := canonicalSourceEnergy_pos_of_c1_and_nonresonant_samples
      hC1 hL K hsamples u hflat hne
    linarith
  · rintro rfl
    simp [quadraticForm]

/-- The same strict positivity statement on the existing physical
Euclidean/PiLp_2 boundary-flat carrier, with no function-space norm substitution. -/
theorem canonicalSourceEnergy_pos_euclidean_of_c1_and_samples
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : x ∈ euclideanBoundaryFlatSubspace K) (hne : x ≠ 0) :
    0 < matrixRealEnergy (canonicalSourceMatrix L K) x := by
  apply canonicalSourceEnergy_pos_of_c1_and_nonresonant_samples hC1 hL K hsamples
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)
  · exact (mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K x).mp hflat
  · intro hx
    apply hne
    apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
    simpa using hx

end Zeta23.OPICARound20

#print axioms Zeta23.OPICARound20.boundaryFlat_exists_nonzero_actual_sample_of_supply
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_pos_of_c1_and_nonresonant_samples
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_zero_iff_coefficients_zero_of_c1_and_samples
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_pos_euclidean_of_c1_and_samples
