import Zeta23.OPICASupport.DensityCompatibility.ActualDistinctGrowth
import Zeta23.OPICASupport.FourierEnergy.EuclideanEnergyLowerBound

/-!
# Actual-zero sampling and complete boundary-flat energy

The accepted actual distinct-zero theorem supplies the finite nonresonant
sample family. No C1 or RH premise is needed for sampling or nonvanishing.
The energy assertions retain precisely the native C1 premise. Every lower
bound uses the physical Euclidean/PiLp_2 norm, with an existential constant
chosen separately for each fixed positive aperture and cutoff.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICARound20

namespace Zeta23.OPICARound21.ActualDensityEnergy

/-- Actual distinct zeros supply exactly the previously separate sampling
premise, including exclusion of the entire exponential resonance lattice. -/
theorem actual_nonresonant_samples {L : ℝ} (hL : 0 < L) (K : ℕ) :
    NonresonantActualZeroSamples L K :=
  DensityCompatibility.actual_nonresonant_zero_samples hL (2 * K - 2)

/-- At each fixed positive aperture and cutoff, some `2*K-2` actual zero
samples determine every native boundary-flat coefficient vector. -/
theorem exists_actual_zero_sampling_injective {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∃ ρ : Fin (2 * K - 2) → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j)) ∧
      (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
      Function.Injective
        (fun u : {u : Fin (2 * K + 1) → ℂ // BoundaryFlatCoefficients K u} =>
          fun j => paperFT (localizedFiniteVector L K u.val) (gammaOf (ρ j))) := by
  rcases actual_nonresonant_samples hL K with ⟨ρ, hρ, hexp⟩
  exact ⟨ρ, hρ, hexp,
    boundaryFlat_paperFT_sampling_injective hL K (fun j => gammaOf (ρ j))
      hρ hexp (by simp)⟩

/-- Every nonzero native BF vector has a nonzero Fourier value at an actual
zero. This assertion has no energy-sign, C1, or RH premise. -/
theorem boundaryFlat_exists_nonzero_actual_zero_sample
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (hne : u ≠ 0) :
    ∃ ρ : zetaZeroConfig.carrier,
      paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) ≠ 0 :=
  boundaryFlat_exists_nonzero_actual_sample_of_supply hL K
    (actual_nonresonant_samples hL K) u hflat hne

theorem boundaryFlat_all_actual_zero_samples_vanish_iff
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u) :
    (∀ ρ : zetaZeroConfig.carrier,
      paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) = 0) ↔ u = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨ρ, hρ⟩ := boundaryFlat_exists_nonzero_actual_zero_sample hL K u hflat hne
    exact hρ (h ρ)
  · rintro rfl
    intro ρ
    simp [paperFT, localizedFiniteVector]

/-- C1 alone gives strict positivity of the complete canonical form on
every nonzero vector in the full three-moment BF carrier. -/
theorem canonicalSourceEnergy_pos_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (hne : u ≠ 0) :
    0 < (quadraticForm (canonicalSourceMatrix L K) u).re :=
  canonicalSourceEnergy_pos_of_c1_and_nonresonant_samples hC1 hL K
    (actual_nonresonant_samples hL K) u hflat hne

theorem canonicalSourceEnergy_zero_iff_coefficients_zero_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u) :
    (quadraticForm (canonicalSourceMatrix L K) u).re = 0 ↔ u = 0 :=
  canonicalSourceEnergy_zero_iff_coefficients_zero_of_c1_and_samples hC1 hL K
    (actual_nonresonant_samples hL K) u hflat

theorem canonicalSourceEnergy_pos_euclidean_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : x ∈ euclideanBoundaryFlatSubspace K) (hne : x ≠ 0) :
    0 < matrixRealEnergy (canonicalSourceMatrix L K) x :=
  canonicalSourceEnergy_pos_euclidean_of_c1_and_samples hC1 hL K
    (actual_nonresonant_samples hL K) x hflat hne

theorem canonicalSourceEnergy_exists_positive_euclidean_bound_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
        x ∈ euclideanBoundaryFlatSubspace K →
        c * ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x :=
  canonicalSourceEnergy_exists_positive_euclidean_lower_bound hC1 hL K
    (actual_nonresonant_samples hL K)

theorem canonicalSourceEnergy_exists_positive_coefficient_l2_bound_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin (2 * K + 1) → ℂ,
      BoundaryFlatCoefficients K u →
      c * ‖WithLp.toLp 2 u‖ ^ 2 ≤
        (quadraticForm (canonicalSourceMatrix L K) u).re :=
  canonicalSourceEnergy_exists_positive_coefficient_l2_lower_bound hC1 hL K
    (actual_nonresonant_samples hL K)

def AllBoundaryFlatStrictPositive : Prop :=
  ∀ L : ℝ, 0 < L → ∀ K : ℕ, ∀ u : Fin (2 * K + 1) → ℂ,
    BoundaryFlatCoefficients K u → u ≠ 0 →
      0 < (quadraticForm (canonicalSourceMatrix L K) u).re

def AllBoundaryFlatEuclideanCoercive : Prop :=
  ∀ L : ℝ, 0 < L → ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      x ∈ euclideanBoundaryFlatSubspace K →
        c * ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x

def AllBoundaryFlatCoefficientL2Coercive : Prop :=
  ∀ L : ℝ, 0 < L → ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ u : Fin (2 * K + 1) → ℂ, BoundaryFlatCoefficients K u →
      c * ‖WithLp.toLp 2 u‖ ^ 2 ≤
        (quadraticForm (canonicalSourceMatrix L K) u).re

/-- Every positive aperture and every cutoff remain universally quantified.
One fixed positive definite matrix is not asserted to imply C1. -/
theorem c1_iff_all_boundary_flat_strict_positive :
    CofinalMomentSliceVanishingErrorBounds ↔ AllBoundaryFlatStrictPositive := by
  constructor
  · intro hC1 L hL K u hflat hne
    exact canonicalSourceEnergy_pos_of_c1 hC1 hL K u hflat hne
  · intro h
    apply c1_iff_all_boundary_flat_nonnegative.mpr
    intro L hL K u hflat
    by_cases hu : u = 0
    · simp [hu, quadraticForm]
    · exact le_of_lt (h L hL K u hflat hu)

/-- The constant is chosen after the fixed `L,K`; no uniform or effective
coercivity constant is supplied by this equivalence. -/
theorem c1_iff_all_boundary_flat_euclidean_coercive :
    CofinalMomentSliceVanishingErrorBounds ↔ AllBoundaryFlatEuclideanCoercive := by
  constructor
  · intro hC1 L hL K
    exact canonicalSourceEnergy_exists_positive_euclidean_bound_of_c1 hC1 hL K
  · intro h
    apply c1_iff_all_boundary_flat_nonnegative.mpr
    intro L hL K u hflat
    obtain ⟨c, hc, hbound⟩ := h L hL K
    have hx : WithLp.toLp 2 u ∈ euclideanBoundaryFlatSubspace K :=
      (mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mpr hflat
    exact le_trans (mul_nonneg hc.le (sq_nonneg ‖WithLp.toLp 2 u‖))
      (hbound (WithLp.toLp 2 u) hx)

theorem c1_iff_all_boundary_flat_coefficient_l2_coercive :
    CofinalMomentSliceVanishingErrorBounds ↔ AllBoundaryFlatCoefficientL2Coercive := by
  constructor
  · intro hC1 L hL K
    exact canonicalSourceEnergy_exists_positive_coefficient_l2_bound_of_c1 hC1 hL K
  · intro h
    apply c1_iff_all_boundary_flat_nonnegative.mpr
    intro L hL K u hflat
    obtain ⟨c, hc, hbound⟩ := h L hL K
    exact le_trans (mul_nonneg hc.le (sq_nonneg ‖WithLp.toLp 2 u‖)) (hbound u hflat)

/-- A nonzero exact BF null vector now refutes C1, as does a negative one.
The matrix is the complete source, not a finite zero truncation. -/
theorem canonicalSourceEnergy_nonpositive_witness_refutes_c1
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hflat : BoundaryFlatCoefficients K u)
    (hne : u ≠ 0)
    (hnonpos : (quadraticForm (canonicalSourceMatrix L K) u).re ≤ 0) :
    ¬ CofinalMomentSliceVanishingErrorBounds := by
  intro hC1
  exact not_lt_of_ge hnonpos (canonicalSourceEnergy_pos_of_c1 hC1 hL K u hflat hne)

/-- The degenerate cutoffs have the explicit constant one without C1,
because the entire native BF carrier is zero. -/
theorem canonicalSourceEnergy_low_cutoff_positive_euclidean_bound
    (L : ℝ) (K : ℕ) (hK : K ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
        x ∈ euclideanBoundaryFlatSubspace K →
        c * ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x :=
  ⟨1, by norm_num, canonicalSourceEnergy_low_cutoff_euclidean_bound L K hK⟩

end Zeta23.OPICARound21.ActualDensityEnergy
