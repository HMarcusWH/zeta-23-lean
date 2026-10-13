import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.CCM.SourceMomentVandermondeFiltration

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
Rigidity of the actual centered-index square on the legal finite carrier.

The two vanishing initial moments propagate through the exact index-moment
recurrence. Finite Vandermonde separation then forces the coefficients to
vanish. This concerns the unchanged centered-index matrix and cannot be
replaced by a claim about an arbitrary index equivalence.
-/

/-- A finite squared-index eigenvector with zero initial moments is zero. -/
theorem eq_zero_of_indexMatrix_sq_eigen_of_moments_zero_one
    (K : ℕ) (c : ℂ) (u : Fin (2 * K + 1) → ℂ)
    (h0 : centeredMoment K 0 u = 0) (h1 : centeredMoment K 1 u = 0)
    (hu : indexMatrix K *ᵥ (indexMatrix K *ᵥ u) = c • u) : u = 0 := by
  have hrec (k : ℕ) : centeredMoment K (k + 2) u = c * centeredMoment K k u := by
    have hm := congrArg (centeredMomentLinearMap K k) hu
    rw [map_smul] at hm
    simp only [centeredMomentLinearMap_apply, smul_eq_mul] at hm
    rw [centeredMoment_indexMatrix_mulVec, centeredMoment_indexMatrix_mulVec] at hm
    simpa only [show k + 1 + 1 = k + 2 by omega] using hm
  have hall (k : ℕ) : centeredMoment K k u = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        exact h0
      by_cases hk1 : k = 1
      · subst k
        exact h1
      have hk2 : 2 ≤ k := by omega
      have hm := hrec (k - 2)
      rw [Nat.sub_add_cancel hk2, ih (k - 2) (by omega), mul_zero] at hm
      exact hm
  exact eq_zero_of_centeredMoment_eq_zero (fun k _ => hall k)

/-- The actual ambient index square has no nonzero eigenvector in the legal
even carrier. No pole condition, positivity, or eigenvalue sign is needed. -/
theorem evenBoundaryFlat_eq_zero_of_euclideanIndex_sq_eigen
    (K : ℕ) (c : ℂ) (u : euclideanEvenBoundaryFlatSubspace K)
    (hu : euclideanIndexLinearMap K
      (euclideanIndexLinearMap K (u : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        c • (u : EuclideanSpace ℂ (Fin (2 * K + 1)))) : u = 0 := by
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K u
  have hraw : indexMatrix K *ᵥ (indexMatrix K *ᵥ evenBoundaryFlatRawCoefficients K u) =
      c • evenBoundaryFlatRawCoefficients K u := by
    have hm := congrArg (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) hu
    rw [euclideanIndexLinearMap_coordinates, euclideanIndexLinearMap_coordinates,
      map_smul] at hm
    exact hm
  have hz := eq_zero_of_indexMatrix_sq_eigen_of_moments_zero_one K c
    (evenBoundaryFlatRawCoefficients K u) hflat.1 hflat.2.1 hraw
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  simpa only [map_zero, evenBoundaryFlatRawCoefficients] using hz

/-- Vanishing fourth moment supplies exactly the missing legal boundary
condition for the second centered-index iterate of an even vector. -/
theorem indexMatrix_sq_mem_evenBoundaryFlat_of_momentFour_eq_zero
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (hu : u ∈ evenBoundaryFlatSubspace K)
    (h4 : centeredMoment K 4 u = 0) :
    indexMatrix K *ᵥ (indexMatrix K *ᵥ u) ∈ evenBoundaryFlatSubspace K := by
  have hf := (mem_boundaryFlatSubspace_iff K u).mp hu.1
  have he := (mem_evenCoefficientSubspace_iff K u).mp hu.2
  refine ⟨(mem_boundaryFlatSubspace_iff K _).mpr ?_,
    (mem_evenCoefficientSubspace_iff K _).mpr ?_⟩
  · simp only [centeredMoment_indexMatrix_mulVec]
    exact ⟨hf.2.2, centeredMoment_odd_eq_zero_of_even hu.2 (by decide), h4⟩
  · simp only [reverseCoefficients_indexMatrix_mulVec, he, Matrix.mulVec_neg, neg_neg]

/-- The actual native even pole profile under the centered-index square. -/
theorem poleEvenProfile_mul_centeredIndex_sq {L : ℝ} (hL : 0 < L)
    (K : ℕ) (i : Fin (2 * K + 1)) :
    poleEvenProfile L K i * (centeredIndex K i : ℂ) ^ 2 =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) -
        ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * poleEvenProfile L K i := by
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hr : poleEvenProfileReal (centeredIndex K i) L * (centeredIndex K i : ℝ) ^ 2 =
      L / (16 * Real.pi ^ 2) -
        (L ^ 2 / (16 * Real.pi ^ 2)) * poleEvenProfileReal (centeredIndex K i) L := by
    unfold poleEvenProfileReal
    field_simp [Real.pi_ne_zero, hd]
    unfold poleProfileDenominator
    ring
  unfold poleEvenProfile
  exact_mod_cast hr

/-- Squared index preserves native pole-neutrality whenever the zeroth
moment and the native even pole profile both vanish. -/
theorem poleEvenProfile_dot_indexMatrix_sq_eq_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (h0 : centeredMoment K 0 u = 0) (hp : poleEvenProfile L K ⬝ᵥ u = 0) :
    poleEvenProfile L K ⬝ᵥ (indexMatrix K *ᵥ (indexMatrix K *ᵥ u)) = 0 := by
  have hs : ∑ i, u i = 0 := by simpa only [centeredMoment_zero_eq_sum] using h0
  have hc (i : Fin (2 * K + 1)) :
      poleEvenProfile L K i * (indexMatrix K *ᵥ (indexMatrix K *ᵥ u)) i =
        (((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) -
          ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * poleEvenProfile L K i) * u i := by
    rw [indexMatrix_mulVec_apply, indexMatrix_mulVec_apply,
      show poleEvenProfile L K i * ((centeredIndex K i : ℂ) *
        ((centeredIndex K i : ℂ) * u i)) =
          (poleEvenProfile L K i * (centeredIndex K i : ℂ) ^ 2) * u i by ring,
      poleEvenProfile_mul_centeredIndex_sq hL]
  unfold dotProduct at hp ⊢
  simp_rw [hc, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hp, mul_zero, sub_self]

end Zeta23.CCM

#print axioms Zeta23.CCM.eq_zero_of_indexMatrix_sq_eigen_of_moments_zero_one
#print axioms Zeta23.CCM.evenBoundaryFlat_eq_zero_of_euclideanIndex_sq_eigen
#print axioms Zeta23.CCM.indexMatrix_sq_mem_evenBoundaryFlat_of_momentFour_eq_zero
#print axioms Zeta23.CCM.poleEvenProfile_mul_centeredIndex_sq
#print axioms Zeta23.CCM.poleEvenProfile_dot_indexMatrix_sq_eq_zero
