import Zeta23.CCM.FrozenCanonicalSourceAnalytic
import Zeta23.CCM.FirstBadShiftedSchur
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: frozen intrinsic predecessor scaffold

This module pushes the frozen-source scalar decomposition through the exact
production parity compression and the exact intrinsic predecessor projection.
The result theorem-locks that the ambient scalar coefficient `-log L` survives
both projections as exactly `-log L * id` on the intrinsic predecessor.

No matrix slice or raw Gram surrogate is used: the definitions reproduce
`parityCompressedCanonical` and `intrinsicPredecessorBlock` with only the
physical prime cutoff frozen.

No complex continuation, determinant nonidentity, dense regularity, positivity,
negative-root exclusion, or RH theorem is claimed here.
-/

/-- Parity compression of the frozen canonical source, using exactly the same
orthogonal projection as the production compression. -/
def frozenParityCompressedCanonicalCLM
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →L[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  let V := euclideanParityBoundaryFlatSubspace p N
  V.orthogonalProjectionOnto.comp
    ((LinearMap.toContinuousLinearMap
        (frozenCanonicalSourceMatrix Q L N).toEuclideanLin).comp V.subtypeL)

/-- Linear-map form of the frozen parity compression. -/
def frozenParityCompressedCanonical
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  (frozenParityCompressedCanonicalCLM Q p L N).toLinearMap

@[simp] theorem frozenParityCompressedCanonical_apply
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    frozenParityCompressedCanonical Q p L N x =
      (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((frozenCanonicalSourceMatrix Q L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) := rfl

/-- On a physical cutoff cell, the frozen parity compression is exactly the
production `parityCompressedCanonical`. -/
theorem frozenParityCompressedCanonical_eq_actual_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q)
    (p : ReversalParity) (N : ℕ) :
    frozenParityCompressedCanonical Q p L N =
      parityCompressedCanonical p L N := by
  apply LinearMap.ext
  intro x
  rw [frozenParityCompressedCanonical_apply,
    parityCompressedCanonical_apply,
    frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell hQ hL N]

/-- Intrinsic predecessor block of the frozen parity compression.  This is the
same two-stage projection as production, not a principal submatrix. -/
def frozenIntrinsicPredecessorBlock
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (intrinsicPredecessorPart p N).comp
    ((frozenParityCompressedCanonical Q p L (N + 1)).comp
      (intrinsicParityPredecessorSubspace p N).subtype)

/-- On its physical cutoff cell, the frozen intrinsic predecessor is exactly
the actual production `intrinsicPredecessorBlock`. -/
theorem frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q)
    (p : ReversalParity) (N : ℕ) :
    frozenIntrinsicPredecessorBlock Q p L N =
      intrinsicPredecessorBlock p L N := by
  apply LinearMap.ext
  intro x
  change
    intrinsicPredecessorPart p N
        (frozenParityCompressedCanonical Q p L (N + 1)
          (x : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1)
          (x : euclideanParityBoundaryFlatSubspace p (N + 1)))
  rw [frozenParityCompressedCanonical_eq_actual_fixedCell hQ hL]

/-- Parity compression of the real frozen source remainder. -/
def frozenParityCompressedRemainderCLM
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →L[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  let V := euclideanParityBoundaryFlatSubspace p N
  V.orthogonalProjectionOnto.comp
    ((LinearMap.toContinuousLinearMap
        (frozenCanonicalSourceRemainderReal Q L N).toEuclideanLin).comp V.subtypeL)

/-- Linear-map form of the parity-compressed real frozen remainder. -/
def frozenParityCompressedRemainder
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  (frozenParityCompressedRemainderCLM Q p L N).toLinearMap

@[simp] theorem frozenParityCompressedRemainder_apply
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    frozenParityCompressedRemainder Q p L N x =
      (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((frozenCanonicalSourceRemainderReal Q L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) := rfl

/-- The exact ambient scalar split survives parity compression with coefficient
unchanged.  The identity matrix compresses to the identity endomorphism on the
parity subspace. -/
theorem frozenParityCompressedCanonical_eq_neg_log_id_add_remainder
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    frozenParityCompressedCanonical Q p L N =
      (-(Real.log L : ℂ)) • LinearMap.id +
        frozenParityCompressedRemainder Q p L N := by
  apply LinearMap.ext
  intro x
  rw [frozenParityCompressedCanonical_apply,
    frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder Q N hL]
  change
    (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        (((( (-(Real.log L : ℂ)) •
            (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) +
          frozenCanonicalSourceRemainderReal Q L N).toEuclideanLin)
            (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) =
      ((-(Real.log L : ℂ)) • LinearMap.id +
        frozenParityCompressedRemainder Q p L N) x
  simp [frozenParityCompressedRemainder_apply]

/-- Intrinsic compression of the real frozen source remainder. -/
def frozenIntrinsicPredecessorRemainderReal
    (Q : ℕ) (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (intrinsicPredecessorPart p N).comp
    ((frozenParityCompressedRemainder Q p L (N + 1)).comp
      (intrinsicParityPredecessorSubspace p N).subtype)

/-- The intrinsic predecessor projection fixes vectors already in the intrinsic
predecessor.  This is the second scalar-compression firewall. -/
@[simp] theorem intrinsicPredecessorPart_subtype
    (p : ReversalParity) (N : ℕ)
    (x : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorPart p N
      (x : euclideanParityBoundaryFlatSubspace p (N + 1)) = x := by
  exact Submodule.projectionOnto_apply_left
    (intrinsicPredecessor_isCompl_shell p N) x

/-- The exact `-log L` coefficient survives the full production intrinsic
predecessor compression unchanged. -/
theorem frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    frozenIntrinsicPredecessorBlock Q p L N =
      (-(Real.log L : ℂ)) • LinearMap.id +
        frozenIntrinsicPredecessorRemainderReal Q p L N := by
  apply LinearMap.ext
  intro x
  change
    intrinsicPredecessorPart p N
        (frozenParityCompressedCanonical Q p L (N + 1)
          (x : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      ((-(Real.log L : ℂ)) • LinearMap.id +
        frozenIntrinsicPredecessorRemainderReal Q p L N) x
  rw [frozenParityCompressedCanonical_eq_neg_log_id_add_remainder Q p (N + 1) hL]
  simp [frozenIntrinsicPredecessorRemainderReal]

/-- Production fixed-cell corollary: the actual intrinsic predecessor itself
has the exact real-axis form `-log L * id + remainder`. -/
theorem intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hcell : L ∈ fixedCanonicalCutoffCell Q)
    (p : ReversalParity) (N : ℕ) :
    intrinsicPredecessorBlock p L N =
      (-(Real.log L : ℂ)) • LinearMap.id +
        frozenIntrinsicPredecessorRemainderReal Q p L N := by
  have hL : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hcell
  rw [← frozenIntrinsicPredecessorBlock_eq_actual_fixedCell hQ hcell p N,
    frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder Q p N hL]

end Zeta23.CCM

#print axioms Zeta23.CCM.frozenParityCompressedCanonical_eq_actual_fixedCell
#print axioms Zeta23.CCM.frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
#print axioms Zeta23.CCM.frozenParityCompressedCanonical_eq_neg_log_id_add_remainder
#print axioms Zeta23.CCM.frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
#print axioms Zeta23.CCM.intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
