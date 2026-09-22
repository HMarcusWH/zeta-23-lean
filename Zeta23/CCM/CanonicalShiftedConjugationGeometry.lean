import Zeta23.CCM.CanonicalConjugationGeometry
import Zeta23.CCM.FirstBadShiftedSchur

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Canonical shifted conjugation geometry

The canonical predecessor block and its safe real negative shift are defined
over the reals.  This module pushes the conjugation geometry of PR #236 through
the Schur predecessor block and its finite-dimensional inverse.

No secular-root hypothesis, eigenvalue-simplicity hypothesis, sign conclusion,
branch exclusion, negative-root exclusion, or RH claim is used.
-/

@[simp] theorem intrinsicPredecessorConj_add
    (p : ReversalParity) (N : ℕ)
    (x y : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorConj p N (x + y) =
      intrinsicPredecessorConj p N x + intrinsicPredecessorConj p N y := by
  apply Subtype.ext
  apply Subtype.ext
  exact euclideanConj_add _ _

@[simp] theorem intrinsicPredecessorConj_neg
    (p : ReversalParity) (N : ℕ)
    (x : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorConj p N (-x) =
      - intrinsicPredecessorConj p N x := by
  apply Subtype.ext
  apply Subtype.ext
  exact euclideanConj_neg _

@[simp] theorem intrinsicPredecessorConj_sub
    (p : ReversalParity) (N : ℕ)
    (x y : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorConj p N (x - y) =
      intrinsicPredecessorConj p N x - intrinsicPredecessorConj p N y := by
  apply Subtype.ext
  apply Subtype.ext
  exact euclideanConj_sub _ _

@[simp] theorem intrinsicPredecessorConj_smul
    (p : ReversalParity) (N : ℕ)
    (a : ℂ) (x : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorConj p N (a • x) =
      star a • intrinsicPredecessorConj p N x := by
  apply Subtype.ext
  apply Subtype.ext
  exact euclideanConj_smul a _

@[simp] theorem intrinsicPredecessorConj_involutive
    (p : ReversalParity) (N : ℕ)
    (x : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorConj p N (intrinsicPredecessorConj p N x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact euclideanConj_involutive _

/-- The projected predecessor block commutes with coordinate conjugation. -/
theorem intrinsicPredecessorBlock_conj
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorBlock p L N
        (intrinsicPredecessorConj p N w) =
      intrinsicPredecessorConj p N
        (intrinsicPredecessorBlock p L N w) := by
  change
    intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1)
          ((intrinsicPredecessorConj p N w :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))) =
      intrinsicPredecessorConj p N
        (intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))))
  rw [coe_intrinsicPredecessorConj, parityCompressedCanonical_conj,
    intrinsicPredecessorPart_conj]

/-- The shell-to-predecessor block commutes with coordinate conjugation. -/
theorem intrinsicShellToPredecessor_conj
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (s : intrinsicParitySuccShell p N) :
    intrinsicShellToPredecessor p L N
        (intrinsicShellConj p N s) =
      intrinsicPredecessorConj p N
        (intrinsicShellToPredecessor p L N s) := by
  change
    intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1)
          ((intrinsicShellConj p N s :
              intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))) =
      intrinsicPredecessorConj p N
        (intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1)
            (s : euclideanParityBoundaryFlatSubspace p (N + 1))))
  rw [coe_intrinsicShellConj, parityCompressedCanonical_conj,
    intrinsicPredecessorPart_conj]

/-- The canonical cubic shell forcing is fixed by conjugation. -/
theorem intrinsicCubicShellForcing_conj_fixed
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicPredecessorConj p N
        (intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N)) =
      intrinsicShellToPredecessor p L N
        (intrinsicCubicShellPart p N) := by
  have h :=
    intrinsicShellToPredecessor_conj p L N
      (intrinsicCubicShellPart p N)
  rw [intrinsicCubicShellPart_conj_fixed] at h
  exact h.symm

/-- The safe real shifted predecessor block commutes with conjugation. -/
theorem shiftedIntrinsicPredecessorBlock_conj
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (lam : ℝ)
    (w : intrinsicParityPredecessorSubspace p N) :
    shiftedIntrinsicPredecessorBlock p L N lam
        (intrinsicPredecessorConj p N w) =
      intrinsicPredecessorConj p N
        (shiftedIntrinsicPredecessorBlock p L N lam w) := by
  change
    intrinsicPredecessorBlock p L N (intrinsicPredecessorConj p N w) -
        (lam : ℂ) • intrinsicPredecessorConj p N w =
      intrinsicPredecessorConj p N
        (intrinsicPredecessorBlock p L N w - (lam : ℂ) • w)
  rw [intrinsicPredecessorBlock_conj, intrinsicPredecessorConj_sub,
    intrinsicPredecessorConj_smul]
  simp

/-- The canonical safe negative-shift predecessor resolvent commutes with
coordinate conjugation. -/
theorem shiftedIntrinsicPredecessorResolvent_conj
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (y : intrinsicParityPredecessorSubspace p N) :
    shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
        (intrinsicPredecessorConj p N y) =
      intrinsicPredecessorConj p N
        (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam y) := by
  let A := shiftedIntrinsicPredecessorBlock p L N lam
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hright :
      ∀ z : intrinsicParityPredecessorSubspace p N, A (R z) = z := by
    intro z
    let E := shiftedIntrinsicPredecessorEquiv p hL N hprev lam hlam
    change E (E.symm z) = z
    exact E.apply_symm_apply z
  apply shiftedIntrinsicPredecessorBlock_injective p hL N hprev (lam := lam) hlam
  change A (R (intrinsicPredecessorConj p N y)) =
    A (intrinsicPredecessorConj p N (R y))
  rw [hright]
  change intrinsicPredecessorConj p N y =
    A (intrinsicPredecessorConj p N (R y))
  rw [shiftedIntrinsicPredecessorBlock_conj]
  rw [hright]

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorBlock_conj
#print axioms Zeta23.CCM.intrinsicShellToPredecessor_conj
#print axioms Zeta23.CCM.shiftedIntrinsicPredecessorBlock_conj
#print axioms Zeta23.CCM.shiftedIntrinsicPredecessorResolvent_conj
