import Zeta23.CCM.ConstrainedCanonicalSector
import Zeta23.CCM.BoundaryFlatProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
# K0-F1E: Euclidean constrained finite sector

This module closes the semantic gap between the raw finite coefficient sector
used by F1 and the finite-dimensional Hilbert-space carrier used by Mathlib's
spectral machinery.

It also theorem-locks the exact rank-three moment map for N >= 1 and therefore
the exact dimension of the boundary-flat sector.

The Euclidean transport is algebraic only.  In particular, no raw function-
space norm is identified with the Euclidean/PiLp_2 norm.

No orthogonal compression, Rayleigh minimizer/eigenvalue theorem, positivity
theorem, or RH claim is asserted here.
-/

/-- The three boundary moments as one complex-linear map. -/
def boundaryMomentTripleMap
    (N : ℕ) :
    (Fin (2 * N + 1) → ℂ) →ₗ[ℂ] ℂ × (ℂ × ℂ) :=
  LinearMap.prod
    (centeredMomentLinearMap N 0)
    (LinearMap.prod
      (centeredMomentLinearMap N 1)
      (centeredMomentLinearMap N 2))

@[simp] theorem boundaryMomentTripleMap_apply
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryMomentTripleMap N u =
      (centeredMoment N 0 u,
        (centeredMoment N 1 u, centeredMoment N 2 u)) := rfl

/-- The kernel of the combined moment map is exactly the existing
boundary-flat subspace. -/
theorem ker_boundaryMomentTripleMap
    (N : ℕ) :
    LinearMap.ker (boundaryMomentTripleMap N) =
      boundaryFlatSubspace N := by
  ext u
  simp [boundaryMomentTripleMap, boundaryFlatSubspace,
    BoundaryFlatCoefficients]

/-- For N >= 1 the three moment constraints are independent.  The proof uses
only the already theorem-locked centered coordinates -1, 0, +1. -/
theorem boundaryMomentTripleMap_surjective
    (N : ℕ)
    (hN : 1 ≤ N) :
    Function.Surjective (boundaryMomentTripleMap N) := by
  rintro ⟨m0, ⟨m1, m2⟩⟩
  let a : ℂ := (m2 - m1) / 2
  let b : ℂ := m0 - m2
  let c : ℂ := (m2 + m1) / 2
  let u : Fin (2 * N + 1) → ℂ :=
    fun i =>
      (coefficientSingle (boundaryFlatNegOneIndex N hN) a i +
        coefficientSingle (boundaryFlatZeroIndex N) b i) +
      coefficientSingle (boundaryFlatOneIndex N hN) c i
  have hmoment (k : ℕ) :
      centeredMoment N k u =
        ((-1 : ℂ) ^ k) * a + ((0 : ℂ) ^ k) * b +
          ((1 : ℂ) ^ k) * c := by
    dsimp [u]
    rw [centeredMoment_add N k
      (fun i =>
        coefficientSingle (boundaryFlatNegOneIndex N hN) a i +
          coefficientSingle (boundaryFlatZeroIndex N) b i)
      (coefficientSingle (boundaryFlatOneIndex N hN) c)]
    rw [centeredMoment_add N k
      (coefficientSingle (boundaryFlatNegOneIndex N hN) a)
      (coefficientSingle (boundaryFlatZeroIndex N) b)]
    simp [centeredMoment_coefficientSingle]
  have h0 : centeredMoment N 0 u = m0 := by
    rw [hmoment 0]
    norm_num [a, b, c]
    ring
  have h1 : centeredMoment N 1 u = m1 := by
    rw [hmoment 1]
    norm_num [a, b, c]
    ring
  have h2 : centeredMoment N 2 u = m2 := by
    rw [hmoment 2]
    norm_num [a, b, c]
    ring
  refine ⟨u, ?_⟩
  change
    (centeredMoment N 0 u,
      (centeredMoment N 1 u, centeredMoment N 2 u)) =
      (m0, (m1, m2))
  rw [h0, h1, h2]

/-- Exact dimension of the raw boundary-flat coefficient sector. -/
theorem finrank_boundaryFlatSubspace
    (N : ℕ)
    (hN : 1 ≤ N) :
    Module.finrank ℂ (boundaryFlatSubspace N) = 2 * N - 2 := by
  have hrange :
      LinearMap.range (boundaryMomentTripleMap N) = ⊤ :=
    LinearMap.range_eq_top.mpr (boundaryMomentTripleMap_surjective N hN)
  have hdim :=
    (boundaryMomentTripleMap N).finrank_range_add_finrank_ker
  rw [hrange, ker_boundaryMomentTripleMap N] at hdim
  have hcalc :
      3 + Module.finrank ℂ (boundaryFlatSubspace N) =
        2 * N + 1 := by
    simpa using hdim
  omega

/-- At N=1 the three moment constraints exhaust the three-dimensional
coefficient space. -/
theorem boundaryFlatSubspace_one_eq_bot :
    boundaryFlatSubspace 1 = ⊥ := by
  rw [← Submodule.finrank_eq_zero]
  simpa using finrank_boundaryFlatSubspace 1 (by omega)

/-- Every nonzero boundary-flat vector with N>=1 actually requires N>=2. -/
theorem two_le_of_ne_zero_mem_boundaryFlatSubspace
    {N : ℕ}
    (hN : 1 ≤ N)
    {u : Fin (2 * N + 1) → ℂ}
    (hmem : u ∈ boundaryFlatSubspace N)
    (hne : u ≠ 0) :
    2 ≤ N := by
  by_contra h2
  have hN1 : N = 1 := by omega
  subst N
  rw [boundaryFlatSubspace_one_eq_bot] at hmem
  exact hne (by simpa using hmem)

/-- The Euclidean/PiLp_2 copy of the exact boundary-flat coefficient sector.
This definition transports only the linear equations, not the raw norm. -/
def euclideanBoundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (boundaryFlatSubspace N).comap
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap

@[simp] theorem mem_euclideanBoundaryFlatSubspace_iff
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanBoundaryFlatSubspace N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        boundaryFlatSubspace N := by
  rfl

/-- Euclidean-sector membership is still exactly the original three
BoundaryFlatCoefficients equations on coordinates. -/
theorem mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanBoundaryFlatSubspace N ↔
      BoundaryFlatCoefficients N
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  rw [mem_euclideanBoundaryFlatSubspace_iff,
    mem_boundaryFlatSubspace_iff]

/-- The Euclidean constrained sector has the same exact dimension. -/
theorem finrank_euclideanBoundaryFlatSubspace
    (N : ℕ)
    (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanBoundaryFlatSubspace N) =
      2 * N - 2 := by
  have hmap :
      euclideanBoundaryFlatSubspace N =
        (boundaryFlatSubspace N).map
          (EuclideanSpace.equiv
            (Fin (2 * N + 1)) ℂ).symm.toLinearEquiv.toLinearMap := by
    simpa [euclideanBoundaryFlatSubspace] using
      (Submodule.comap_equiv_eq_map_symm
        (EuclideanSpace.equiv
          (Fin (2 * N + 1)) ℂ).toLinearEquiv
        (boundaryFlatSubspace N))
  rw [hmap]
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_boundaryFlatSubspace N hN

/-- The canonical finite matrix becomes a symmetric operator on Euclidean
space. -/
theorem canonicalSourceMatrix_toEuclideanLin_isSymmetric
    (L : ℝ)
    (N : ℕ) :
    (canonicalSourceMatrix L N).toEuclideanLin.IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (canonicalSourceMatrix_isHermitian L N)

/-- The project quadratic form is the ordinary star-dot-product matrix
quadratic form. -/
theorem quadraticForm_eq_star_dotProduct_mulVec
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι ℂ)
    (u : ι → ℂ) :
    quadraticForm A u = star u ⬝ᵥ (A *ᵥ u) := by
  unfold quadraticForm Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [Pi.star_apply, starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Exact bridge from the project quadratic form to the Euclidean inner
product.  The inner-product convention is fixed by Mathlib, not guessed. -/
theorem quadraticForm_eq_inner_toEuclideanLin
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    quadraticForm A ((EuclideanSpace.equiv ι ℂ) x) =
      inner ℂ x (A.toEuclideanLin x) := by
  rw [quadraticForm_eq_star_dotProduct_mulVec]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  exact dotProduct_comm _ _

/-- Real-part bridge in the orientation used by Rayleigh's
reApplyInnerSelf. -/
theorem quadraticForm_re_eq_re_inner_apply_self
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    (quadraticForm A ((EuclideanSpace.equiv ι ℂ) x)).re =
      Complex.re (inner ℂ (A.toEuclideanLin x) x) := by
  rw [quadraticForm_eq_inner_toEuclideanLin]
  exact inner_re_symm (𝕜 := ℂ) _ _

end Zeta23.CCM

#print axioms Zeta23.CCM.ker_boundaryMomentTripleMap
#print axioms Zeta23.CCM.boundaryMomentTripleMap_surjective
#print axioms Zeta23.CCM.finrank_boundaryFlatSubspace
#print axioms Zeta23.CCM.boundaryFlatSubspace_one_eq_bot
#print axioms Zeta23.CCM.two_le_of_ne_zero_mem_boundaryFlatSubspace
#print axioms Zeta23.CCM.mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat
#print axioms Zeta23.CCM.finrank_euclideanBoundaryFlatSubspace
#print axioms Zeta23.CCM.canonicalSourceMatrix_toEuclideanLin_isSymmetric
#print axioms Zeta23.CCM.quadraticForm_eq_inner_toEuclideanLin
#print axioms Zeta23.CCM.quadraticForm_re_eq_re_inner_apply_self
