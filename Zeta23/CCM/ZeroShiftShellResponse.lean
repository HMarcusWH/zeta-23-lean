import Zeta23.CCM.ZeroShiftSchurEndpoint
import Zeta23.CCM.CubicNormalizedSchur

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3a: canonical zero-shift shell response

PR #125 proves that in the decoupled zero-shift branch the canonical trial
vector

  u₀ = -x₀ + c,

with `A x₀ = B c`, has zero predecessor coordinate after application of the
full successor operator `T`.  Since the exact intrinsic decomposition is
`V = W ⊕ S`, that already forces `T u₀` into the one-dimensional shell.

The repository already has a canonical cubic coordinate on `S`; no basis or
new choice is required.  This module therefore defines the canonical scalar
response `sigma₀`, proves

  sigma₀ • c = T u₀,

and identifies the #125 zero-shift endpoint exactly as

  S₀ = star(sigma₀) * <c,c>.

The conjugation is essential: Mathlib's complex inner product is conjugate
linear in the first argument and linear in the second.

Firewalls:
* only this specific zero-shift trial vector is shown to have pure-shell image;
* no shell invariance under `T` is claimed;
* `u₀` is not promoted to an eigenvector;
* no zero-shift inverse is introduced;
* no resonant branch is excluded;
* no monotonicity, root uniqueness, negative-root exclusion, positivity
  closure, finite-to-infinite closure, or RH theorem is claimed.
-/

/-- Canonical scalar response of the full successor operator on the decoupled
zero-shift trial vector, read in the already-normalized cubic quotient
coordinate. -/
def cubicZeroShiftShellResponseScalar
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N) : ℂ :=
  intrinsicCubicQuotientCoordinate p N
    (parityCompressedCanonical p L (N + 1)
      (cubicZeroShiftTrialVector p L N x₀))

/-- If `A x₀ = B c`, then the full successor image of the zero-shift trial
vector is exactly its intrinsic shell projection.  This is the exact
basis-free statement that `T u₀` is pure shell. -/
theorem parityCompressedCanonical_cubicZeroShiftTrialVector_eq_shellPart
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    parityCompressedCanonical p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) =
      ((intrinsicShellPart p N
          (parityCompressedCanonical p L (N + 1)
            (cubicZeroShiftTrialVector p L N x₀)) :
          intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let y := parityCompressedCanonical p L (N + 1)
    (cubicZeroShiftTrialVector p L N x₀)
  have hyPred : intrinsicPredecessorPart p N y = 0 := by
    simpa [y] using
      intrinsicPredecessorPart_parityCompressedCanonical_cubicZeroShiftTrialVector_eq_zero
        p L N x₀ hx₀
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  rw [hyPred] at hrec
  simpa [y] using hrec.symm

/-- Membership-form wrapper for the pure-shell response theorem. -/
theorem parityCompressedCanonical_cubicZeroShiftTrialVector_mem_shell
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    parityCompressedCanonical p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) ∈
      intrinsicParitySuccShell p N := by
  let y := parityCompressedCanonical p L (N + 1)
    (cubicZeroShiftTrialVector p L N x₀)
  have hy :
      y =
        ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [y] using
      parityCompressedCanonical_cubicZeroShiftTrialVector_eq_shellPart
        p L N x₀ hx₀
  rw [hy]
  exact (intrinsicShellPart p N y).property

/-- E4-A3a scalar-response endpoint: the canonical cubic response scalar
reconstructs the entire full-operator image of the zero-shift trial vector. -/
theorem cubicZeroShiftShellResponseScalar_smul_cubic_eq
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    cubicZeroShiftShellResponseScalar p L N x₀ •
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
      parityCompressedCanonical p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) := by
  let y := parityCompressedCanonical p L (N + 1)
    (cubicZeroShiftTrialVector p L N x₀)
  have hcoordShell :=
    intrinsicCubicShellCoordinate_smul_cubic_eq
      p N hN (intrinsicShellPart p N y)
  have hcoordCarrier :
      intrinsicCubicShellCoordinate p N (intrinsicShellPart p N y) •
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
        ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    have h := congrArg
      (fun t : intrinsicParitySuccShell p N =>
        (t : euclideanParityBoundaryFlatSubspace p (N + 1)))
      hcoordShell
    change
      intrinsicCubicShellCoordinate p N (intrinsicShellPart p N y) •
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
        ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) at h
    exact h
  have hy :
      y =
        ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [y] using
      parityCompressedCanonical_cubicZeroShiftTrialVector_eq_shellPart
        p L N x₀ hx₀
  change
    intrinsicCubicShellCoordinate p N (intrinsicShellPart p N y) •
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) = y
  exact hcoordCarrier.trans hy.symm

/-- The #125 zero-shift Schur endpoint is exactly the canonical one-dimensional
shell response, with the first-slot conjugation required by the complex inner
product convention. -/
theorem cubicZeroShiftSchurEndpoint_eq_star_shellResponse_mul_inner
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    cubicZeroShiftSchurEndpoint p L N x₀ =
      star (cubicZeroShiftShellResponseScalar p L N x₀) *
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let c := intrinsicCubicShellPart p N
  let u := cubicZeroShiftTrialVector p L N x₀
  let sigma := cubicZeroShiftShellResponseScalar p L N x₀
  have hQ :=
    inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
      p L N x₀ hx₀
  have hresponse :
      sigma • (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        parityCompressedCanonical p L (N + 1) u := by
    simpa [sigma, c, u] using
      cubicZeroShiftShellResponseScalar_smul_cubic_eq
        p L N hN x₀ hx₀
  have hcx :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    exact inner_intrinsicShell_predecessor_eq_zero p N c x₀
  have hcu :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) u =
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    change
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (((-x₀ : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) +
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) = _
    rw [inner_add_right]
    have hneg :
        inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            ((-x₀ : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
      change
        inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (-(x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))) = 0
      rw [inner_neg_right, hcx, neg_zero]
    rw [hneg, zero_add]
  calc
    cubicZeroShiftSchurEndpoint p L N x₀ =
        inner ℂ
          (parityCompressedCanonical p L (N + 1) u) u := by
      simpa [u] using hQ.symm
    _ = inner ℂ
          (sigma • (c : euclideanParityBoundaryFlatSubspace p (N + 1))) u := by
      exact (congrArg (fun y => inner ℂ y u) hresponse).symm
    _ = star sigma *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) u := by
      rw [inner_smul_left]
    _ = star sigma *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rw [hcu]
    _ = star (cubicZeroShiftShellResponseScalar p L N x₀) *
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCompressedCanonical_cubicZeroShiftTrialVector_eq_shellPart
#print axioms Zeta23.CCM.cubicZeroShiftShellResponseScalar_smul_cubic_eq
#print axioms Zeta23.CCM.cubicZeroShiftSchurEndpoint_eq_star_shellResponse_mul_inner
