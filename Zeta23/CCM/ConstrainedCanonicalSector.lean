import Zeta23.CCM.BoundaryFlatFiniteSpace
import Zeta23.CCM.FiniteDictionary
import Zeta23.CCM.SourceNormalizationRepair
import Zeta23.CCM.DictionarySymmetry
import Mathlib.LinearAlgebra.Matrix.Hermitian

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
# K0/K1-F1: constrained canonical finite sector

This module packages the exact three centered-moment constraints carried by the
F1 finite negative witness as finite linear algebra and theorem-locks their
interaction with the centered index operator and the exact canonical
displacement identity.

The project-level proposition `BoundaryFlatCoefficients` remains the canonical
statement of the three moment equations.  `boundaryFlatSubspace` is only its
linear-algebra packaging.

No positivity theorem, spectral minimizer, aperture-flow theorem, source-QW
identification, or RH claim is asserted here.
-/

/-- The centered moment of order `k` as a complex-linear functional. -/
def centeredMomentLinearMap
    (N k : ℕ) :
    (Fin (2 * N + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun := centeredMoment N k
  map_add' := by
    intro u v
    simp [centeredMoment, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c u
    simp only [centeredMoment, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp] theorem centeredMomentLinearMap_apply
    (N k : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMomentLinearMap N k u = centeredMoment N k u := rfl

/-- The exact codimension-at-most-three F1 coefficient sector, packaged as a
complex subspace. -/
def boundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  (centeredMomentLinearMap N 0).ker ⊓
    ((centeredMomentLinearMap N 1).ker ⊓
      (centeredMomentLinearMap N 2).ker)

/-- Membership in the linear-algebra sector is exactly the pre-existing
`BoundaryFlatCoefficients` proposition. -/
theorem mem_boundaryFlatSubspace_iff
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    u ∈ boundaryFlatSubspace N ↔ BoundaryFlatCoefficients N u := by
  simp [boundaryFlatSubspace, BoundaryFlatCoefficients]

/-- Moment zero is the ordinary coefficient sum. -/
@[simp] theorem centeredMoment_zero_eq_sum
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 0 u = ∑ i, u i := by
  simp [centeredMoment]

/-- The centered index matrix acts coordinatewise by multiplication by the
centered integer index. -/
@[simp] theorem indexMatrix_mulVec_apply
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (i : Fin (2 * N + 1)) :
    (indexMatrix N *ᵥ u) i = (centeredIndex N i : ℂ) * u i := by
  rw [indexMatrix, mulVec_diagonal]

/-- Exact centered-moment shift under the centered index operator:
`M_k(Du)=M_{k+1}(u)`. -/
theorem centeredMoment_indexMatrix_mulVec
    (N k : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N k (indexMatrix N *ᵥ u) =
      centeredMoment N (k + 1) u := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i hi
  rw [indexMatrix_mulVec_apply]
  rw [pow_succ]
  ring

/-- Boundary-flat coefficients give zero coefficient sum. -/
theorem sum_eq_zero_of_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    ∑ i, u i = 0 := by
  simpa [centeredMoment] using hu.1

/-- The first centered-index iterate of a boundary-flat vector has zero
coefficient sum. -/
theorem sum_indexMatrix_mulVec_eq_zero_of_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    ∑ i, (indexMatrix N *ᵥ u) i = 0 := by
  have hshift := centeredMoment_indexMatrix_mulVec N 0 u
  have hm1 := hu.2.1
  simpa [centeredMoment] using hshift.trans hm1

/-- The second centered-index iterate of a boundary-flat vector has zero
coefficient sum. -/
theorem sum_indexMatrix_mulVec_sq_eq_zero_of_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    ∑ i, (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) i = 0 := by
  have hshift0 :=
    centeredMoment_indexMatrix_mulVec N 0 (indexMatrix N *ᵥ u)
  have hshift1 := centeredMoment_indexMatrix_mulVec N 1 u
  have hm2 := hu.2.2
  have hmid :
      centeredMoment N 1 (indexMatrix N *ᵥ u) = 0 :=
    hshift1.trans hm2
  simpa [centeredMoment] using hshift0.trans hmid

/-- Exact descending moment flag after one application of `D`. -/
theorem indexMatrix_mulVec_moments_zero_one_of_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    centeredMoment N 0 (indexMatrix N *ᵥ u) = 0 ∧
      centeredMoment N 1 (indexMatrix N *ᵥ u) = 0 := by
  constructor
  · rw [centeredMoment_indexMatrix_mulVec]
    exact hu.2.1
  · rw [centeredMoment_indexMatrix_mulVec]
    exact hu.2.2

/-- Exact descending moment flag after two applications of `D`. -/
theorem indexMatrix_mulVec_sq_moment_zero_of_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    centeredMoment N 0
        (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) = 0 := by
  rw [centeredMoment_indexMatrix_mulVec,
    centeredMoment_indexMatrix_mulVec]
  exact hu.2.2

/-- Package form of the only moment annihilations available from F1:
`u` kills moments 0,1,2; `Du` kills 0,1; `D²u` kills 0.

In particular this theorem deliberately does not claim that `D` preserves the
full boundary-flat sector. -/
theorem boundaryFlat_moment_flag
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    (centeredMoment N 0 u = 0 ∧
      centeredMoment N 1 u = 0 ∧
      centeredMoment N 2 u = 0) ∧
    (centeredMoment N 0 (indexMatrix N *ᵥ u) = 0 ∧
      centeredMoment N 1 (indexMatrix N *ᵥ u) = 0) ∧
    centeredMoment N 0
      (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) = 0 := by
  exact ⟨hu,
    indexMatrix_mulVec_moments_zero_one_of_boundaryFlat hu,
    indexMatrix_mulVec_sq_moment_zero_of_boundaryFlat hu⟩

/-- Every canonical-source entry is fixed by complex conjugation because the
matrix is built from real scalar entries. -/
theorem canonicalSourceMatrix_apply_star_self
    (L : ℝ)
    (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    star (canonicalSourceMatrix L N i j) =
      canonicalSourceMatrix L N i j := by
  rw [canonicalSourceMatrix_eq_dictionaryMatrix, dictionaryMatrix_apply]
  by_cases h : i = j
  · rw [if_pos h]
    simp only [star_add, finiteMatrix_apply, starRingEnd_apply,
      Complex.star_def, Complex.conj_ofReal]
  · rw [if_neg h]
    simp only [star_add, finiteMatrix_apply, starRingEnd_apply,
      Complex.star_def, Complex.conj_ofReal, star_zero, add_zero]

/-- Entrywise Hermitian symmetry of the canonical source matrix. -/
theorem canonicalSourceMatrix_star_apply_comm
    (L : ℝ)
    (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    star (canonicalSourceMatrix L N j i) =
      canonicalSourceMatrix L N i j := by
  rw [canonicalSourceMatrix_apply_star_self]
  rw [canonicalSourceMatrix_eq_dictionaryMatrix]
  exact (dictionaryMatrix_apply_comm L N i j).symm

/-- Matrix-level Hermitian identity for the canonical source matrix. -/
theorem canonicalSourceMatrix_conjTranspose
    (L : ℝ)
    (N : ℕ) :
    (canonicalSourceMatrix L N)ᴴ = canonicalSourceMatrix L N := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  exact canonicalSourceMatrix_star_apply_comm L N i j

/-- Canonical source matrices are Hermitian. -/
theorem canonicalSourceMatrix_isHermitian
    (L : ℝ)
    (N : ℕ) :
    (canonicalSourceMatrix L N).IsHermitian := by
  exact canonicalSourceMatrix_conjTranspose L N

/-- Bilinear displacement pairing.  This is deliberately not a Hermitian inner
product: the exact rank-two displacement identity contains no conjugation. -/
def displacementPairing
    (L : ℝ)
    (N : ℕ)
    (v : Fin (2 * N + 1) → ℂ) : ℂ :=
  ∑ i, displacementVector L N i * v i

/-- Exact one-channel collapse of the canonical displacement on every
zero-moment vector. -/
theorem canonicalSourceMatrix_displacement_mulVec_of_moment_zero
    {L : ℝ}
    (hL : 0 < L)
    (N : ℕ)
    (v : Fin (2 * N + 1) → ℂ)
    (hv : centeredMoment N 0 v = 0) :
    (indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ v =
      fun _ => -displacementPairing L N v := by
  have hsum : (∑ i, v i) = 0 := by
    simpa [centeredMoment] using hv
  rw [canonicalSourceMatrix_displacement hL N]
  ext i
  simp only [Matrix.mulVec, Pi.sub_apply, Matrix.vecMulVec, dotProduct,
    displacementPairing, mul_one, one_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  simp

/-- Exact constrained displacement collapse on a boundary-flat vector. -/
theorem canonicalSourceMatrix_displacement_mulVec_boundaryFlat
    {L : ℝ}
    (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) :
    (indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ u =
      fun _ => -displacementPairing L N u :=
  canonicalSourceMatrix_displacement_mulVec_of_moment_zero
    hL N u hu.1

/-- Exact constrained displacement collapse on the first centered-index
iterate of a boundary-flat vector. -/
theorem canonicalSourceMatrix_displacement_mulVec_index_boundaryFlat
    {L : ℝ}
    (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) :
    (indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ
        (indexMatrix N *ᵥ u) =
      fun _ => -displacementPairing L N (indexMatrix N *ᵥ u) := by
  apply canonicalSourceMatrix_displacement_mulVec_of_moment_zero hL N
  exact (indexMatrix_mulVec_moments_zero_one_of_boundaryFlat hu).1

/-- Exact constrained displacement collapse on the second centered-index
iterate of a boundary-flat vector. -/
theorem canonicalSourceMatrix_displacement_mulVec_index_sq_boundaryFlat
    {L : ℝ}
    (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) :
    (indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ
        (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) =
      fun _ =>
        -displacementPairing L N
          (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) := by
  apply canonicalSourceMatrix_displacement_mulVec_of_moment_zero hL N
  exact indexMatrix_mulVec_sq_moment_zero_of_boundaryFlat hu

/-- Package theorem: on the first three Krylov vectors generated by a
boundary-flat vector, the exact ambient rank-two displacement lies entirely in
the one-dimensional all-ones forcing channel. -/
theorem boundaryFlat_canonical_displacement_package
    {L : ℝ}
    (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) :
    ((indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ u =
      fun _ => -displacementPairing L N u) ∧
    ((indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ
        (indexMatrix N *ᵥ u) =
      fun _ => -displacementPairing L N (indexMatrix N *ᵥ u)) ∧
    ((indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ
        (indexMatrix N *ᵥ (indexMatrix N *ᵥ u)) =
      fun _ =>
        -displacementPairing L N
          (indexMatrix N *ᵥ (indexMatrix N *ᵥ u))) := by
  exact ⟨
    canonicalSourceMatrix_displacement_mulVec_boundaryFlat hL N u hu,
    canonicalSourceMatrix_displacement_mulVec_index_boundaryFlat hL N u hu,
    canonicalSourceMatrix_displacement_mulVec_index_sq_boundaryFlat hL N u hu
  ⟩

/-- Quadratic forms scale sesquilinearly under scalar multiplication with the
project's fixed conjugation convention. -/
theorem quadraticForm_smul
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι ℂ)
    (c : ℂ)
    (u : ι → ℂ) :
    quadraticForm A (c • u) =
      star c * c * quadraticForm A u := by
  unfold quadraticForm
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem quadraticForm_zero
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι ℂ) :
    quadraticForm A (0 : ι → ℂ) = 0 := by
  simp [quadraticForm]

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredMomentLinearMap_apply
#print axioms Zeta23.CCM.mem_boundaryFlatSubspace_iff
#print axioms Zeta23.CCM.centeredMoment_indexMatrix_mulVec
#print axioms Zeta23.CCM.boundaryFlat_moment_flag
#print axioms Zeta23.CCM.canonicalSourceMatrix_conjTranspose
#print axioms Zeta23.CCM.canonicalSourceMatrix_isHermitian
#print axioms Zeta23.CCM.canonicalSourceMatrix_displacement_mulVec_of_moment_zero
#print axioms Zeta23.CCM.boundaryFlat_canonical_displacement_package
#print axioms Zeta23.CCM.quadraticForm_smul
