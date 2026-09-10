import Zeta23.CCM.FrozenCanonicalSourceComplex
import Zeta23.CCM.FrozenIntrinsicPredecessorAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: complex intrinsic predecessor and log cover

This module pushes the complex frozen source remainder through the exact same
fixed parity and intrinsic predecessor projections as production.  It then
places the explicit logarithmic scalar on the logarithmic cover `L = exp z`.

The lifted remainder is deck-periodic because it depends on `z` only through
`exp z`.  This is the correct monodromy architecture: there is no global
single-valued base-plane `Log` assumption.

No determinant nonidentity, dense regularity, energy sign, negative-root
exclusion, or RH claim is made here.
-/

/-- Parity compression of the complex frozen source remainder. -/
def complexFrozenParityCompressedRemainderCLM
    (Q : ℕ) (p : ReversalParity) (z : ℂ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →L[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  let V := euclideanParityBoundaryFlatSubspace p N
  V.orthogonalProjectionOnto.comp
    ((LinearMap.toContinuousLinearMap
        (complexFrozenCanonicalSourceRemainder Q z N).toEuclideanLin).comp V.subtypeL)

/-- Linear-map form of the complex frozen parity-compressed remainder. -/
def complexFrozenParityCompressedRemainder
    (Q : ℕ) (p : ReversalParity) (z : ℂ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  (complexFrozenParityCompressedRemainderCLM Q p z N).toLinearMap

@[simp] theorem complexFrozenParityCompressedRemainder_apply
    (Q : ℕ) (p : ReversalParity) (z : ℂ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    complexFrozenParityCompressedRemainder Q p z N x =
      (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((complexFrozenCanonicalSourceRemainder Q z N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) := rfl

/-- Exact positive-real-axis bridge for the parity-compressed remainder. -/
@[simp] theorem complexFrozenParityCompressedRemainder_ofReal
    (Q : ℕ) (p : ReversalParity) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    complexFrozenParityCompressedRemainder Q p (L : ℂ) N =
      frozenParityCompressedRemainder Q p L N := by
  apply LinearMap.ext
  intro x
  rw [complexFrozenParityCompressedRemainder_apply,
    frozenParityCompressedRemainder_apply,
    complexFrozenCanonicalSourceRemainder_ofReal Q hL N]

/-- Full intrinsic predecessor compression of the complex frozen remainder. -/
def complexFrozenIntrinsicPredecessorRemainder
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (intrinsicPredecessorPart p N).comp
    ((complexFrozenParityCompressedRemainder Q p z (N + 1)).comp
      (intrinsicParityPredecessorSubspace p N).subtype)

/-- Exact positive-real-axis bridge for the actual intrinsic predecessor
remainder. -/
@[simp] theorem complexFrozenIntrinsicPredecessorRemainder_ofReal
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    complexFrozenIntrinsicPredecessorRemainder Q p N (L : ℂ) =
      frozenIntrinsicPredecessorRemainderReal Q p L N := by
  apply LinearMap.ext
  intro x
  unfold complexFrozenIntrinsicPredecessorRemainder
  unfold frozenIntrinsicPredecessorRemainderReal
  rw [complexFrozenParityCompressedRemainder_ofReal Q p hL (N + 1)]

/-- Deck-periodic lifted remainder on the logarithmic cover. -/
def liftedFrozenIntrinsicPredecessorRemainder
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  complexFrozenIntrinsicPredecessorRemainder Q p N (Complex.exp z)

/-- Lifted intrinsic predecessor family.  The entire nonperiodic scalar is the
explicit `-z * id`; the remainder depends on `z` only through `exp z`. -/
def liftedFrozenIntrinsicPredecessorBlock
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (-z) • LinearMap.id +
    liftedFrozenIntrinsicPredecessorRemainder Q p N z

/-- The lifted remainder is exactly invariant under one logarithmic deck
translation. -/
theorem liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    liftedFrozenIntrinsicPredecessorRemainder Q p N
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      liftedFrozenIntrinsicPredecessorRemainder Q p N z := by
  unfold liftedFrozenIntrinsicPredecessorRemainder
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- On the logarithmic cover, one deck translation changes the full lifted
block only by the corresponding scalar multiple of the identity. -/
theorem liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    liftedFrozenIntrinsicPredecessorBlock Q p N
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      liftedFrozenIntrinsicPredecessorBlock Q p N z -
        (2 * (Real.pi : ℂ) * Complex.I) • LinearMap.id := by
  rw [liftedFrozenIntrinsicPredecessorBlock,
    liftedFrozenIntrinsicPredecessorBlock,
    liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I]
  module

/-- Exact production bridge: over a physical cutoff cell, evaluating the lifted
family at the real logarithm recovers the actual production
`intrinsicPredecessorBlock`. -/
theorem liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hcell : L ∈ fixedCanonicalCutoffCell Q)
    (p : ReversalParity) (N : ℕ) :
    liftedFrozenIntrinsicPredecessorBlock Q p N (Real.log L : ℂ) =
      intrinsicPredecessorBlock p L N := by
  have hL : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hcell
  have hexp : Complex.exp (Real.log L : ℂ) = (L : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hL]
  rw [liftedFrozenIntrinsicPredecessorBlock,
    liftedFrozenIntrinsicPredecessorRemainder, hexp,
    complexFrozenIntrinsicPredecessorRemainder_ofReal Q p N hL]
  rw [intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
    hQ hcell p N]

end Zeta23.CCM

#print axioms Zeta23.CCM.complexFrozenIntrinsicPredecessorRemainder_ofReal
#print axioms Zeta23.CCM.liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
#print axioms Zeta23.CCM.liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
#print axioms Zeta23.CCM.liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
