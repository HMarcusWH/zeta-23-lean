import Zeta23.CCM.CanonicalPoleNeutralCarrier
import Zeta23.CCM.NestedFinite

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
Actual pole-neutral nesting at fixed aperture under unchanged centered
zero extension. The profile pairings, legal carriers, coefficient norm,
and unchanged canonical quadratic form are all preserved by construction.
No nested-form premise is supplied by a caller. No aperture flow or output
invariance of the compressed operators is asserted.
-/

theorem poleOddProfile_dot_centeredZeroExtend (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M) (u : Fin (2 * N + 1) → ℂ) :
    poleOddProfile L M ⬝ᵥ centeredZeroExtend hNM u = poleOddProfile L N ⬝ᵥ u := by
  unfold dotProduct
  rw [Fintype.sum_of_injective
    (centeredEmbedding N M hNM) (centeredEmbedding N M hNM).injective
    (fun i : Fin (2 * N + 1) => poleOddProfile L N i * u i)
    (fun j : Fin (2 * M + 1) => poleOddProfile L M j * centeredZeroExtend hNM u j)]
  · intro j hj
    rw [centeredZeroExtend_apply_of_not_mem_range hNM u j]
    · simp
    · simpa using hj
  · intro i
    simp [poleOddProfile]

theorem canonicalPoleEvenFunctional_centeredZeroExtend (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    canonicalPoleEvenFunctional L M (euclideanCenteredZeroExtend hNM x) =
      canonicalPoleEvenFunctional L N x := by
  change poleEvenProfile L M ⬝ᵥ
      ((EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ) (euclideanCenteredZeroExtend hNM x)) = _
  rw [euclideanCenteredZeroExtend_coordinates, poleEvenProfile_dot_centeredZeroExtend] <;> rfl

theorem canonicalPoleOddFunctional_centeredZeroExtend (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    canonicalPoleOddFunctional L M (euclideanCenteredZeroExtend hNM x) =
      canonicalPoleOddFunctional L N x := by
  change poleOddProfile L M ⬝ᵥ
      ((EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ) (euclideanCenteredZeroExtend hNM x)) = _
  rw [euclideanCenteredZeroExtend_coordinates, poleOddProfile_dot_centeredZeroExtend] <;> rfl

/-- Restrict the actual centered extension to both native even kernels. -/
def poleNeutralEvenCenteredZeroExtendLinearMap (L : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    poleNeutralEvenSubspace L N →ₗ[ℂ] poleNeutralEvenSubspace L M where
  toFun u := by
    let w : euclideanEvenBoundaryFlatSubspace M :=
      ⟨euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))),
        euclideanCenteredZeroExtend_mem_euclideanEvenBoundaryFlatSubspace hNM u.val.property⟩
    refine ⟨w, ?_⟩
    rw [mem_poleNeutralEvenSubspace]
    change canonicalPoleEvenFunctional L M
      (euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1)))) = 0
    rw [canonicalPoleEvenFunctional_centeredZeroExtend]
    exact (mem_poleNeutralEvenSubspace L N u.val).mp u.property
  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (euclideanCenteredZeroExtend hNM).map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    exact (euclideanCenteredZeroExtend hNM).map_smul c _

/-- Restrict the same actual centered extension to both native odd kernels. -/
def poleNeutralOddCenteredZeroExtendLinearMap (L : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    poleNeutralOddSubspace L N →ₗ[ℂ] poleNeutralOddSubspace L M where
  toFun u := by
    let w : euclideanOddBoundaryFlatSubspace M :=
      ⟨euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))),
        euclideanCenteredZeroExtend_mem_euclideanOddBoundaryFlatSubspace hNM u.val.property⟩
    refine ⟨w, ?_⟩
    rw [mem_poleNeutralOddSubspace]
    change canonicalPoleOddFunctional L M
      (euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1)))) = 0
    rw [canonicalPoleOddFunctional_centeredZeroExtend]
    exact (mem_poleNeutralOddSubspace L N u.val).mp u.property
  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (euclideanCenteredZeroExtend hNM).map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    exact (euclideanCenteredZeroExtend hNM).map_smul c _

theorem coe_poleNeutralEvenCenteredZeroExtendLinearMap (L : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (u : poleNeutralEvenSubspace L N) :
    ((poleNeutralEvenCenteredZeroExtendLinearMap L hNM u).val : EuclideanSpace ℂ (Fin (2 * M + 1))) =
      euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

theorem coe_poleNeutralOddCenteredZeroExtendLinearMap (L : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (u : poleNeutralOddSubspace L N) :
    ((poleNeutralOddCenteredZeroExtendLinearMap L hNM u).val : EuclideanSpace ℂ (Fin (2 * M + 1))) =
      euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

def poleNeutralEvenCenteredZeroExtend (L : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    poleNeutralEvenSubspace L N →ₗᵢ[ℂ] poleNeutralEvenSubspace L M where
  toLinearMap := poleNeutralEvenCenteredZeroExtendLinearMap L hNM
  norm_map' u := (euclideanCenteredZeroExtend hNM).norm_map
    (u.val : EuclideanSpace ℂ (Fin (2 * N + 1)))

def poleNeutralOddCenteredZeroExtend (L : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    poleNeutralOddSubspace L N →ₗᵢ[ℂ] poleNeutralOddSubspace L M where
  toLinearMap := poleNeutralOddCenteredZeroExtendLinearMap L hNM
  norm_map' u := (euclideanCenteredZeroExtend hNM).norm_map
    (u.val : EuclideanSpace ℂ (Fin (2 * N + 1)))

theorem coe_poleNeutralEvenCenteredZeroExtend (L : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (u : poleNeutralEvenSubspace L N) :
    ((poleNeutralEvenCenteredZeroExtend L hNM u).val : EuclideanSpace ℂ (Fin (2 * M + 1))) =
      euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

theorem coe_poleNeutralOddCenteredZeroExtend (L : ℝ) {N M : ℕ} (hNM : N ≤ M)
    (u : poleNeutralOddSubspace L N) :
    ((poleNeutralOddCenteredZeroExtend L hNM u).val : EuclideanSpace ℂ (Fin (2 * M + 1))) =
      euclideanCenteredZeroExtend hNM (u.val : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

/-- Full complex self-form consistency of the unchanged canonical matrix. -/
theorem inner_canonicalSourceMatrix_euclideanCenteredZeroExtend {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    inner ℂ ((canonicalSourceMatrix L M).toEuclideanLin (euclideanCenteredZeroExtend hNM x))
      (euclideanCenteredZeroExtend hNM x) = inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x := by
  have hq := quadraticForm_canonicalSourceMatrix_centeredZeroExtend hL hNM
    ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)
  rw [← euclideanCenteredZeroExtend_coordinates hNM x,
    quadraticForm_eq_inner_toEuclideanLin, quadraticForm_eq_inner_toEuclideanLin] at hq
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hq

/-- Actual native even quadratic form consistency, without output invariance. -/
theorem inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) (u : poleNeutralEvenSubspace L N) :
    inner ℂ (poleNeutralEvenCompressedCanonical L M (poleNeutralEvenCenteredZeroExtend L hNM u))
      (poleNeutralEvenCenteredZeroExtend L hNM u) = inner ℂ (poleNeutralEvenCompressedCanonical L N u) u := by
  rw [inner_poleNeutralEvenCompressedCanonical_self, inner_poleNeutralEvenCompressedCanonical_self]
  simp only [coe_poleNeutralEvenCenteredZeroExtend]
  exact inner_canonicalSourceMatrix_euclideanCenteredZeroExtend hL hNM _

/-- Actual native odd quadratic form consistency under the same extension. -/
theorem inner_poleNeutralOddCompressedCanonical_centeredZeroExtend {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) (u : poleNeutralOddSubspace L N) :
    inner ℂ (poleNeutralOddCompressedCanonical L M (poleNeutralOddCenteredZeroExtend L hNM u))
      (poleNeutralOddCenteredZeroExtend L hNM u) = inner ℂ (poleNeutralOddCompressedCanonical L N u) u := by
  rw [inner_poleNeutralOddCompressedCanonical_self, inner_poleNeutralOddCompressedCanonical_self]
  simp only [coe_poleNeutralOddCenteredZeroExtend]
  exact inner_canonicalSourceMatrix_euclideanCenteredZeroExtend hL hNM _

end Zeta23.CCM

#print axioms Zeta23.CCM.poleOddProfile_dot_centeredZeroExtend
#print axioms Zeta23.CCM.canonicalPoleEvenFunctional_centeredZeroExtend
#print axioms Zeta23.CCM.canonicalPoleOddFunctional_centeredZeroExtend
#print axioms Zeta23.CCM.poleNeutralEvenCenteredZeroExtend
#print axioms Zeta23.CCM.poleNeutralOddCenteredZeroExtend
#print axioms Zeta23.CCM.inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
#print axioms Zeta23.CCM.inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend
#print axioms Zeta23.CCM.inner_poleNeutralOddCompressedCanonical_centeredZeroExtend
