import Zeta23.CCM.ZeroShiftSchurDichotomy

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A2-ENDPOINT: canonical zero-shift Schur endpoint

PR #124 proves that the projected predecessor block

  A = P_W T|_W

has orthogonal kernel/range geometry and splits the zero-shift problem into a
decoupled branch and a resonant branch. In the decoupled branch the canonical
cubic coupling `b = B c` admits a zero-shift preimage `A x₀ = b`, and #124
proves that `⟪x₀,b⟫` is independent of the selected preimage.

This module turns that scalar independence into the actual zero-shift Schur
endpoint. The zero-shift trial vector is `u₀ = -x₀ + c`. Its predecessor
residual vanishes exactly, and its full quadratic value is the endpoint

  S₀ = ⟪T c,c⟫ - ⟪x₀,b⟫.

Adding any predecessor displacement gives an exact complete-square identity.
Predecessor nonnegativity therefore makes `S₀` the minimum quadratic value on
the affine fibre with the canonical cubic shell coordinate. Evaluating that
identity at the already-formalized negative secular eigenmode shows that any
safe negative explicit Schur root forces `Re S₀ < 0` in the decoupled branch.

Firewalls:
* no whole-space inverse of `A` at zero is defined or used;
* the endpoint is canonical only through #124 solution-independence;
* `ker A` remains the kernel of the projected successor predecessor block;
* no resolvent limit or monotonicity theorem is used;
* no resonant branch is excluded;
* no negative-root exclusion, positivity closure, finite-to-infinite closure,
  or RH theorem is claimed.
-/

/-- The zero-shift cubic Schur endpoint attached to a selected solution
`A x₀ = b`. #124 proves below that its value is independent of the selected
solution whenever the same coupling vector `b` is hit. -/
def cubicZeroShiftSchurEndpoint
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N) : ℂ :=
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  inner ℂ
      (parityCompressedCanonical p L (N + 1)
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
      (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
    inner ℂ
      (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
      (b : euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The zero-shift Schur endpoint is independent of which preimage of the
canonical cubic coupling is selected. -/
theorem cubicZeroShiftSchurEndpoint_eq_of_preimages
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x y : intrinsicParityPredecessorSubspace p N)
    (hx : intrinsicPredecessorBlock p L N x =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    (hy : intrinsicPredecessorBlock p L N y =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    cubicZeroShiftSchurEndpoint p L N x =
      cubicZeroShiftSchurEndpoint p L N y := by
  dsimp [cubicZeroShiftSchurEndpoint]
  rw [inner_intrinsicPredecessorBlock_preimage_eq
    p L N
    (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    x y hx hy]

/-- Canonical zero-shift trial vector in the decoupled branch. Its shell part is
the canonical cubic shell vector, while its predecessor part is `-x₀`. -/
def cubicZeroShiftTrialVector
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N) :
    euclideanParityBoundaryFlatSubspace p (N + 1) :=
  ((-x₀ : intrinsicParityPredecessorSubspace p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) +
    (intrinsicCubicShellPart p N :
      euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The predecessor coordinate of the zero-shift trial vector is exactly
`-x₀`. -/
theorem intrinsicPredecessorPart_cubicZeroShiftTrialVector
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorPart p N
        (cubicZeroShiftTrialVector p L N x₀) = -x₀ := by
  simp [cubicZeroShiftTrialVector, intrinsicPredecessorPart]

/-- The shell coordinate of the zero-shift trial vector is exactly the
canonical cubic shell vector. -/
theorem intrinsicShellPart_cubicZeroShiftTrialVector
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N) :
    intrinsicShellPart p N
        (cubicZeroShiftTrialVector p L N x₀) =
      intrinsicCubicShellPart p N := by
  simp [cubicZeroShiftTrialVector, intrinsicShellPart]

/-- The predecessor projection of `T s` is the shell-to-predecessor block `B s`
inside inner products against predecessor vectors. -/
theorem inner_intrinsicPredecessor_parityCompressedCanonical_shell_eq
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N)
    (s : intrinsicParitySuccShell p N) :
    inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        (parityCompressedCanonical p L (N + 1)
          (s : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicShellToPredecessor p L N s :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let y := parityCompressedCanonical p L (N + 1)
    (s : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicPredecessor_shell_eq_zero
    p N w (intrinsicShellPart p N y)
  change
    inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) y =
      inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicPredecessorPart p N y :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
  calc
    inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) y =
      inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        (((intrinsicPredecessorPart p N y :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))) := by
              rw [hrec]
    _ = inner ℂ
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicPredecessorPart p N y :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
            rw [inner_add_right, hort, add_zero]

/-- If `A x₀ = b`, then the zero-shift trial vector has zero predecessor
residual under the full successor compressed operator. -/
theorem intrinsicPredecessorPart_parityCompressedCanonical_cubicZeroShiftTrialVector_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1)
          (cubicZeroShiftTrialVector p L N x₀)) = 0 := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let w : intrinsicParityPredecessorSubspace p N := -x₀
  let u := cubicZeroShiftTrialVector p L N x₀
  have hx : intrinsicPredecessorBlock p L N x₀ = b := by
    simpa [b, c] using hx₀
  have huPred : intrinsicPredecessorPart p N u = w := by
    simpa [u, w] using
      intrinsicPredecessorPart_cubicZeroShiftTrialVector p L N x₀
  have huShell : intrinsicShellPart p N u = c := by
    simpa [u, c] using
      intrinsicShellPart_cubicZeroShiftTrialVector p L N x₀
  have hrec := intrinsicPredecessorPart_add_shellPart p N u
  calc
    intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1) u) =
      intrinsicPredecessorPart p N
        (parityCompressedCanonical p L (N + 1)
          (((w : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) +
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))) := by
              rw [← huPred, ← huShell]
              rw [hrec]
    _ = intrinsicPredecessorBlock p L N w + b := by
      simp [intrinsicPredecessorBlock, intrinsicShellToPredecessor, b,
        map_add]
    _ = 0 := by
      rw [show w = -x₀ by rfl, map_neg, hx]
      abel

/-- The image of the zero-shift trial vector is orthogonal to every predecessor
vector because its predecessor coordinate vanishes. -/
theorem inner_parityCompressedCanonical_cubicZeroShiftTrialVector_predecessor_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ d : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (cubicZeroShiftTrialVector p L N x₀))
        (d : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  let y := parityCompressedCanonical p L (N + 1)
    (cubicZeroShiftTrialVector p L N x₀)
  have hyPred : intrinsicPredecessorPart p N y = 0 := by
    simpa [y] using
      intrinsicPredecessorPart_parityCompressedCanonical_cubicZeroShiftTrialVector_eq_zero
        p L N x₀ hx₀
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicShell_predecessor_eq_zero
    p N (intrinsicShellPart p N y) d
  calc
    inner ℂ y
        (d : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (((intrinsicPredecessorPart p N y :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)))
        (d : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
          rw [hrec]
    _ = 0 := by
      rw [inner_add_left, hyPred]
      simpa using hort

/-- Exact zero-shift quadratic identity: the full quadratic value of the
zero-shift trial vector is precisely the zero-shift Schur endpoint. -/
theorem inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (cubicZeroShiftTrialVector p L N x₀))
        (cubicZeroShiftTrialVector p L N x₀) =
      cubicZeroShiftSchurEndpoint p L N x₀ := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let u := cubicZeroShiftTrialVector p L N x₀
  have hx : intrinsicPredecessorBlock p L N x₀ = b := by
    simpa [b, c] using hx₀
  have hTuX :
      inner ℂ
          (parityCompressedCanonical p L (N + 1) u)
          (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    simpa [u] using
      inner_parityCompressedCanonical_cubicZeroShiftTrialVector_predecessor_eq_zero
        p L N x₀ x₀ hx₀
  have hTuU :
      inner ℂ
          (parityCompressedCanonical p L (N + 1) u) u =
        inner ℂ
          (parityCompressedCanonical p L (N + 1) u)
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    change
      inner ℂ
          (parityCompressedCanonical p L (N + 1) u)
          (((-x₀ : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) +
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) = _
    rw [inner_add_right]
    have hneg :
        inner ℂ
            (parityCompressedCanonical p L (N + 1) u)
            ((-x₀ : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
      change
        inner ℂ
            (parityCompressedCanonical p L (N + 1) u)
            (-(x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))) = 0
      rw [inner_neg_right, hTuX, neg_zero]
    rw [hneg, zero_add]
  have hsym :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    exact parityCompressedCanonical_isSymmetric p L (N + 1)
      (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
      (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hxb :
      inner ℂ
          (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [b, c] using
      inner_intrinsicPredecessor_parityCompressedCanonical_shell_eq
        p L N x₀ c
  calc
    inner ℂ
        (parityCompressedCanonical p L (N + 1) u) u =
      inner ℂ
        (parityCompressedCanonical p L (N + 1) u)
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := hTuU
    _ = - inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) +
        inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      change
        inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (((-x₀ : intrinsicParityPredecessorSubspace p N) :
                euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) = _
      rw [map_add, map_neg, inner_add_left, inner_neg_left]
    _ = cubicZeroShiftSchurEndpoint p L N x₀ := by
      rw [hsym, hxb]
      change
        - inner ℂ
            (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
          inner ℂ
              (parityCompressedCanonical p L (N + 1)
                (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
            inner ℂ
              (x₀ : euclideanParityBoundaryFlatSubspace p (N + 1))
              (b : euclideanParityBoundaryFlatSubspace p (N + 1))
      abel

/-- Exact complete-square identity along the predecessor fibre. -/
theorem inner_cubicZeroShiftTrialVector_add_predecessor
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ d : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (cubicZeroShiftTrialVector p L N x₀ +
            (d : euclideanParityBoundaryFlatSubspace p (N + 1))))
        (cubicZeroShiftTrialVector p L N x₀ +
          (d : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      cubicZeroShiftSchurEndpoint p L N x₀ +
        inner ℂ
          ((intrinsicPredecessorBlock p L N d :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (d : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let u := cubicZeroShiftTrialVector p L N x₀
  have hQ0 :=
    inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
      p L N x₀ hx₀
  have hcross₁ :
      inner ℂ
          (parityCompressedCanonical p L (N + 1) u)
          (d : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    simpa [u] using
      inner_parityCompressedCanonical_cubicZeroShiftTrialVector_predecessor_eq_zero
        p L N x₀ d hx₀
  have hcross₂ :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (d : euclideanParityBoundaryFlatSubspace p (N + 1))) u = 0 := by
    have hsym := parityCompressedCanonical_isSymmetric p L (N + 1)
      (d : euclideanParityBoundaryFlatSubspace p (N + 1)) u
    have hdu :
        inner ℂ
            (d : euclideanParityBoundaryFlatSubspace p (N + 1))
            (parityCompressedCanonical p L (N + 1) u) = 0 := by
      rw [inner_eq_zero_symm]
      exact hcross₁
    rw [hsym, hdu]
  have hQd := inner_intrinsicPredecessorBlock_self p L N d
  change
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (u + (d : euclideanParityBoundaryFlatSubspace p (N + 1))))
        (u + (d : euclideanParityBoundaryFlatSubspace p (N + 1))) = _
  calc
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (u + (d : euclideanParityBoundaryFlatSubspace p (N + 1))))
        (u + (d : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      (inner ℂ (parityCompressedCanonical p L (N + 1) u) u +
        inner ℂ (parityCompressedCanonical p L (N + 1) u)
          (d : euclideanParityBoundaryFlatSubspace p (N + 1))) +
      (inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (d : euclideanParityBoundaryFlatSubspace p (N + 1))) u +
        inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (d : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (d : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
            simp only [map_add, inner_add_left, inner_add_right]
    _ = cubicZeroShiftSchurEndpoint p L N x₀ +
        inner ℂ
          ((intrinsicPredecessorBlock p L N d :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (d : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rw [hQ0, hcross₁, hcross₂, ← hQd]
      abel

/-- A safe negative explicit Schur root forces the canonical zero-shift Schur
endpoint to be strictly negative in the decoupled branch. This is a direct
finite complete-square argument; no resolvent limit or monotonicity is used. -/
theorem cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicExplicitSchurScalar p hL N hprev lam hlam = 0) :
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) < 0 := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let ulam := cubicSecularTrialVector p hL N hprev lam hlam
  let d : intrinsicParityPredecessorSubspace p N := x₀ - R b
  have huadd :
      cubicZeroShiftTrialVector p L N x₀ +
          (d : euclideanParityBoundaryFlatSubspace p (N + 1)) = ulam := by
    change
      (-(x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))) +
        ((x₀ : euclideanParityBoundaryFlatSubspace p (N + 1)) -
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))) =
      -((R b : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
    abel
  have heig :
      parityCompressedCanonical p L (N + 1) ulam = (lam : ℂ) • ulam := by
    simpa [ulam] using
      (cubicExplicitSchurScalar_eq_zero_iff_trial_eigenmode
        p hL N hN hprev lam hlam).mp hroot
  have hulamNe : ulam ≠ 0 := by
    simpa [ulam] using
      cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam
  have hnormpos : 0 < ‖ulam‖ ^ 2 := by
    have hpos : 0 < ‖ulam‖ := norm_pos_iff.mpr hulamNe
    positivity
  have hqneg :
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L (N + 1) ulam) ulam) < 0 := by
    rw [heig]
    have hsmul :
        inner ℂ ((lam : ℂ) • ulam) ulam =
          lam • inner ℂ ulam ulam := by
      exact inner_smul_real_left (𝕜 := ℂ) ulam ulam lam
    rw [hsmul, Complex.smul_re]
    have hnorm :
        Complex.re (inner ℂ ulam ulam) = ‖ulam‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) ulam).symm
    rw [hnorm, smul_eq_mul]
    exact mul_neg_of_neg_of_pos hlam hnormpos
  have hcomp :=
    inner_cubicZeroShiftTrialVector_add_predecessor
      p L N x₀ d hx₀
  rw [huadd] at hcomp
  have hcompRe := congrArg Complex.re hcomp
  rw [Complex.add_re] at hcompRe
  have hdnonneg :=
    re_inner_intrinsicPredecessorBlock_nonnegative p hL N hprev d
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicZeroShiftSchurEndpoint_eq_of_preimages
#print axioms Zeta23.CCM.inner_cubicZeroShiftTrialVector_add_predecessor
#print axioms Zeta23.CCM.cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
