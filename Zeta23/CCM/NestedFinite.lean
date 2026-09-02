import Zeta23.CCM.ConstrainedEuclideanSector
import Zeta23.CCM.LocalizedWeilRestriction
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators

/-!
# N-FLOW-A/B: exact centered finite nesting

This module theorem-locks the exact centered inclusion of the canonical CCM
finite sectors. The inclusion preserves the integer Fourier label, the
canonical principal block, every centered coefficient moment, the localized
finite function, the Euclidean inner product, and therefore the canonical
quadratic value.

The embedding is the central inclusion, not the prefix inclusion of Fin:
i.val is shifted by M-N.

No parity decomposition, constrained compression, spectral minimizer,
finite-to-infinite convergence, positivity theorem, or RH claim is made here.
-/

def centeredEmbedding
    (N M : ℕ) (hNM : N ≤ M) :
    Fin (2 * N + 1) ↪ Fin (2 * M + 1) where
  toFun i := ⟨i.1 + (M - N), by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp at hval
    omega

@[simp] theorem centeredIndex_centeredEmbedding
    (N M : ℕ) (hNM : N ≤ M)
    (i : Fin (2 * N + 1)) :
    centeredIndex M (centeredEmbedding N M hNM i) =
      centeredIndex N i := by
  unfold centeredIndex centeredEmbedding
  simp only [Fin.val_mk]
  rw [Int.ofNat_add, Int.ofNat_sub hNM]
  omega

theorem centeredEmbedding_trans
    (N M K : ℕ) (hNM : N ≤ M) (hMK : M ≤ K) :
    (centeredEmbedding M K hMK).comp (centeredEmbedding N M hNM) =
      centeredEmbedding N K (hNM.trans hMK) := by
  ext i
  apply Fin.ext
  simp [centeredEmbedding]
  omega

@[simp] theorem canonicalSourceMatrix_submatrix_centeredEmbedding
    (L : ℝ)
    (N M : ℕ) (hNM : N ≤ M) :
    (canonicalSourceMatrix L M).submatrix
        (centeredEmbedding N M hNM)
        (centeredEmbedding N M hNM) =
      canonicalSourceMatrix L N := by
  ext i j
  simp [canonicalSourceMatrix, cutoffFreeMatrix]

@[simp] theorem indexMatrix_submatrix_centeredEmbedding
    (N M : ℕ) (hNM : N ≤ M) :
    (indexMatrix M).submatrix
        (centeredEmbedding N M hNM)
        (centeredEmbedding N M hNM) =
      indexMatrix N := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [indexMatrix]
  · have hemb :
        centeredEmbedding N M hNM i ≠ centeredEmbedding N M hNM j := by
      exact fun h => hij ((centeredEmbedding N M hNM).injective h)
    simp [indexMatrix, hij, hemb]

def centeredZeroExtend
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * M + 1) → ℂ :=
  Function.extend (centeredEmbedding N M hNM) u (fun _ => 0)

@[simp] theorem centeredZeroExtend_apply_centeredEmbedding
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ)
    (i : Fin (2 * N + 1)) :
    centeredZeroExtend hNM u (centeredEmbedding N M hNM i) = u i := by
  exact (centeredEmbedding N M hNM).injective.extend_apply u (fun _ => 0) i

theorem centeredZeroExtend_apply_of_not_mem_range
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ)
    (j : Fin (2 * M + 1))
    (hj : j ∉ Set.range (centeredEmbedding N M hNM)) :
    centeredZeroExtend hNM u j = 0 := by
  exact Function.extend_apply' _ _ _ hj

def centeredZeroExtendLinearMap
    {N M : ℕ} (hNM : N ≤ M) :
    (Fin (2 * N + 1) → ℂ) →ₗ[ℂ]
      (Fin (2 * M + 1) → ℂ) where
  toFun := centeredZeroExtend hNM
  map_add' := by
    intro u v
    ext j
    by_cases hj : j ∈ Set.range (centeredEmbedding N M hNM)
    · obtain ⟨i, rfl⟩ := hj
      simp
    · rw [centeredZeroExtend_apply_of_not_mem_range hNM (u + v) _ hj]
      rw [centeredZeroExtend_apply_of_not_mem_range hNM u _ hj]
      rw [centeredZeroExtend_apply_of_not_mem_range hNM v _ hj]
      rfl
  map_smul' := by
    intro c u
    ext j
    by_cases hj : j ∈ Set.range (centeredEmbedding N M hNM)
    · obtain ⟨i, rfl⟩ := hj
      simp
    · rw [centeredZeroExtend_apply_of_not_mem_range hNM (c • u) _ hj]
      rw [centeredZeroExtend_apply_of_not_mem_range hNM u _ hj]
      simp

@[simp] theorem centeredZeroExtendLinearMap_apply
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredZeroExtendLinearMap hNM u = centeredZeroExtend hNM u := rfl

theorem centeredMoment_centeredZeroExtend
    {N M : ℕ} (hNM : N ≤ M)
    (k : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment M k (centeredZeroExtend hNM u) =
      centeredMoment N k u := by
  unfold centeredMoment
  rw [Fintype.sum_of_injective
    (centeredEmbedding N M hNM)
    (centeredEmbedding N M hNM).injective
    (fun i : Fin (2 * N + 1) =>
      (centeredIndex N i : ℂ) ^ k * u i)
    (fun j : Fin (2 * M + 1) =>
      (centeredIndex M j : ℂ) ^ k * centeredZeroExtend hNM u j)]
  · intro j hj
    rw [centeredZeroExtend_apply_of_not_mem_range hNM u j]
    · simp
    · simpa using hj
  · intro i
    simp

theorem centeredZeroExtend_boundaryFlat
    {N M : ℕ} (hNM : N ≤ M)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    BoundaryFlatCoefficients M (centeredZeroExtend hNM u) := by
  constructor
  · rw [centeredMoment_centeredZeroExtend hNM 0]
    exact hu.1
  · constructor
    · rw [centeredMoment_centeredZeroExtend hNM 1]
      exact hu.2.1
    · rw [centeredMoment_centeredZeroExtend hNM 2]
      exact hu.2.2

theorem centeredZeroExtend_mem_boundaryFlatSubspace
    {N M : ℕ} (hNM : N ≤ M)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    centeredZeroExtend hNM u ∈ boundaryFlatSubspace M := by
  rw [mem_boundaryFlatSubspace_iff] at hu ⊢
  exact centeredZeroExtend_boundaryFlat hNM hu

theorem localizedFiniteVector_centeredZeroExtend
    (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteVector L M (centeredZeroExtend hNM u) =
      localizedFiniteVector L N u := by
  funext x
  unfold localizedFiniteVector
  rw [Fintype.sum_of_injective
    (centeredEmbedding N M hNM)
    (centeredEmbedding N M hNM).injective
    (fun i : Fin (2 * N + 1) =>
      u i * localizedZeroExtendedMode L (centeredIndex N i) x)
    (fun j : Fin (2 * M + 1) =>
      centeredZeroExtend hNM u j *
        localizedZeroExtendedMode L (centeredIndex M j) x)]
  · intro j hj
    rw [centeredZeroExtend_apply_of_not_mem_range hNM u j]
    · simp
    · simpa using hj
  · intro i
    simp

theorem quadraticForm_canonicalSourceMatrix_centeredZeroExtend
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm
        (canonicalSourceMatrix L M)
        (centeredZeroExtend hNM u) =
      quadraticForm (canonicalSourceMatrix L N) u := by
  change quadraticForm
      (cutoffFreeMatrix L M)
      (centeredZeroExtend hNM u) =
    quadraticForm (cutoffFreeMatrix L N) u
  rw [← localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
      M (centeredZeroExtend hNM u) hL]
  rw [← localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
      N u hL]
  rw [localizedFiniteVector_centeredZeroExtend L hNM u]

def euclideanCenteredZeroExtendLinearMap
    {N M : ℕ} (hNM : N ≤ M) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (2 * M + 1)) :=
  (EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ).symm.toLinearEquiv.toLinearMap.comp
    ((centeredZeroExtendLinearMap hNM).comp
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap)

theorem euclideanCenteredZeroExtendLinearMap_coordinates
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ)
        (euclideanCenteredZeroExtendLinearMap hNM x) =
      centeredZeroExtend hNM
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  simp [euclideanCenteredZeroExtendLinearMap]

theorem inner_euclideanCenteredZeroExtendLinearMap
    {N M : ℕ} (hNM : N ≤ M)
    (x y : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    inner ℂ
        (euclideanCenteredZeroExtendLinearMap hNM x)
        (euclideanCenteredZeroExtendLinearMap hNM y) =
      inner ℂ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hx := euclideanCenteredZeroExtendLinearMap_coordinates hNM x
  have hy := euclideanCenteredZeroExtendLinearMap_coordinates hNM y
  rw [Fintype.sum_of_injective
    (centeredEmbedding N M hNM)
    (centeredEmbedding N M hNM).injective
    (fun i : Fin (2 * N + 1) => inner ℂ (x i) (y i))
    (fun j : Fin (2 * M + 1) =>
      inner ℂ
        (euclideanCenteredZeroExtendLinearMap hNM x j)
        (euclideanCenteredZeroExtendLinearMap hNM y j))]
  · intro j hj
    have hxj := congrFun hx j
    have hyj := congrFun hy j
    rw [hxj, hyj]
    rw [centeredZeroExtend_apply_of_not_mem_range hNM _ j]
    · simp
    · simpa using hj
  · intro i
    have hxi := congrFun hx (centeredEmbedding N M hNM i)
    have hyi := congrFun hy (centeredEmbedding N M hNM i)
    rw [hxi, hyi]
    simp

def euclideanCenteredZeroExtend
    {N M : ℕ} (hNM : N ≤ M) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 * M + 1)) :=
  (euclideanCenteredZeroExtendLinearMap hNM).isometryOfInner
    (inner_euclideanCenteredZeroExtendLinearMap hNM)

@[simp] theorem euclideanCenteredZeroExtend_apply
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanCenteredZeroExtend hNM x =
      euclideanCenteredZeroExtendLinearMap hNM x := rfl

theorem euclideanCenteredZeroExtend_coordinates
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ)
        (euclideanCenteredZeroExtend hNM x) =
      centeredZeroExtend hNM
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  exact euclideanCenteredZeroExtendLinearMap_coordinates hNM x

theorem euclideanCenteredZeroExtend_mem_euclideanBoundaryFlatSubspace
    {N M : ℕ} (hNM : N ≤ M)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanBoundaryFlatSubspace N) :
    euclideanCenteredZeroExtend hNM x ∈
      euclideanBoundaryFlatSubspace M := by
  rw [mem_euclideanBoundaryFlatSubspace_iff] at hx ⊢
  rw [euclideanCenteredZeroExtend_coordinates]
  exact centeredZeroExtend_mem_boundaryFlatSubspace hNM hx

theorem re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L M).toEuclideanLin
            (euclideanCenteredZeroExtend hNM x))
          (euclideanCenteredZeroExtend hNM x)) =
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin x)
          x) := by
  have hM :=
    quadraticForm_re_eq_re_inner_apply_self
      (canonicalSourceMatrix L M)
      (euclideanCenteredZeroExtend hNM x)
  have hN :=
    quadraticForm_re_eq_re_inner_apply_self
      (canonicalSourceMatrix L N) x
  rw [← hM, ← hN]
  rw [euclideanCenteredZeroExtend_coordinates]
  exact congrArg Complex.re
    (quadraticForm_canonicalSourceMatrix_centeredZeroExtend
      hL hNM ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredIndex_centeredEmbedding
#print axioms Zeta23.CCM.canonicalSourceMatrix_submatrix_centeredEmbedding
#print axioms Zeta23.CCM.centeredMoment_centeredZeroExtend
#print axioms Zeta23.CCM.euclideanCenteredZeroExtend_mem_euclideanBoundaryFlatSubspace
#print axioms Zeta23.CCM.re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
