import Zeta23.CCM.CubicExplicitSecular
import Mathlib.Analysis.InnerProductSpace.Symmetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E3-B1: secular metric control

PR #121 identifies the exact canonical quotient secular scalar with the
conjugate of the explicit #113-oriented Schur scalar. This module supplies the
metric facts deliberately left open there: projected predecessor symmetry,
quantitative shifted coercivity, symmetry and positivity of the negative-shift
resolvent quadratic value, and realness of the explicit secular scalar.

The predecessor block remains the projected block `A = P_W T|_W`; no
predecessor invariance is assumed. Every inverse is `A - lam I` with `lam < 0`.
There is no inverse at zero, no positive predecessor gap, no monotonicity or
root-exclusion theorem, and no RH theorem.
-/

/-- Removing the shell component of `T w₁` does not change its inner product
with a predecessor vector in the second slot. -/
theorem inner_intrinsicPredecessorBlock_left
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w₁ w₂ : intrinsicParityPredecessorSubspace p N) :
    inner ℂ
        ((intrinsicPredecessorBlock p L N w₁ :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let y := parityCompressedCanonical p L (N + 1)
    (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicShell_predecessor_eq_zero
    p N (intrinsicShellPart p N y) w₂
  change
    inner ℂ
      ((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) =
    inner ℂ y
      (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1))
  calc
    inner ℂ
        ((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) +
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
          rw [inner_add_left, hort, add_zero]
    _ = inner ℂ y
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
          rw [hrec]

/-- Removing the shell component of `T w₂` does not change its inner product
with a predecessor vector in the first slot. -/
theorem inner_intrinsicPredecessorBlock_right
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w₁ w₂ : intrinsicParityPredecessorSubspace p N) :
    inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicPredecessorBlock p L N w₂ :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        (parityCompressedCanonical p L (N + 1)
          (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let y := parityCompressedCanonical p L (N + 1)
    (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicPredecessor_shell_eq_zero
    p N w₁ (intrinsicShellPart p N y)
  change
    inner ℂ
      (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
      ((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) =
    inner ℂ
      (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1)) y
  calc
    inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        (((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) +
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))) := by
          rw [inner_add_right, hort, add_zero]
    _ = inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1)) y := by
          rw [hrec]

/-- The projected predecessor block is symmetric in the exact induced inner
product. This is a projection consequence of the already-proved symmetry of
the full parity-compressed canonical operator; no invariance is used. -/
theorem intrinsicPredecessorBlock_isSymmetric
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := intrinsicParityPredecessorSubspace p N)
      (intrinsicPredecessorBlock p L N) := by
  intro w₁ w₂
  change
    inner ℂ
        ((intrinsicPredecessorBlock p L N w₁ :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicPredecessorBlock p L N w₂ :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
  calc
    _ = inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1)) :=
      inner_intrinsicPredecessorBlock_left p L N w₁ w₂
    _ = inner ℂ
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        (parityCompressedCanonical p L (N + 1)
          (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1))) :=
      parityCompressedCanonical_isSymmetric p L (N + 1)
        (w₁ : euclideanParityBoundaryFlatSubspace p (N + 1))
        (w₂ : euclideanParityBoundaryFlatSubspace p (N + 1))
    _ = _ := (inner_intrinsicPredecessorBlock_right p L N w₁ w₂).symm

/-- A real scalar shift preserves predecessor-block symmetry. -/
theorem shiftedIntrinsicPredecessorBlock_isSymmetric
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := intrinsicParityPredecessorSubspace p N)
      (shiftedIntrinsicPredecessorBlock p L N lam) := by
  intro x y
  change
    inner ℂ
        (intrinsicPredecessorBlock p L N x - (lam : ℂ) • x) y =
      inner ℂ x
        (intrinsicPredecessorBlock p L N y - (lam : ℂ) • y)
  rw [inner_sub_left, inner_sub_right,
    intrinsicPredecessorBlock_isSymmetric p L N x y]
  simp

/-- Quantitative shifted coercivity from predecessor nonnegativity. For a
negative shift, `A - lam I` has a lower quadratic floor `-lam`. -/
theorem re_inner_shiftedIntrinsicPredecessorBlock_ge
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (w : intrinsicParityPredecessorSubspace p N) :
    (-lam) * ‖w‖ ^ 2 ≤
      Complex.re
        (inner ℂ (shiftedIntrinsicPredecessorBlock p L N lam w) w) := by
  have hnonneg :
      0 ≤ Complex.re
        (inner ℂ (intrinsicPredecessorBlock p L N w) w) := by
    simpa using
      re_inner_intrinsicPredecessorBlock_nonnegative p hL N hprev w
  change
    (-lam) * ‖w‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (intrinsicPredecessorBlock p L N w - (lam : ℂ) • w) w)
  rw [inner_sub_left, Complex.sub_re]
  have hsmul :
      inner ℂ ((lam : ℂ) • w) w =
        lam • inner ℂ w w := by
    exact inner_smul_real_left (𝕜 := ℂ) w w lam
  rw [hsmul, Complex.smul_re]
  have hnorm : Complex.re (inner ℂ w w) = ‖w‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  rw [hnorm]
  linarith

/-- The resolvent quadratic value controls the squared resolvent norm from
below at every safe negative shift. -/
theorem neg_mul_norm_sq_resolvent_le_re_inner
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    (-lam) *
        ‖shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b) := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let x := R b
  have hco :=
    re_inner_shiftedIntrinsicPredecessorBlock_ge p hL N hprev hlam x
  have hright : shiftedIntrinsicPredecessorBlock p L N lam x = b := by
    simpa [x, R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam b
  have hsym := shiftedIntrinsicPredecessorBlock_isSymmetric p L N lam x x
  rw [hright] at hsym
  change
    (-lam) * ‖x‖ ^ 2 ≤
      Complex.re
        (inner ℂ (shiftedIntrinsicPredecessorBlock p L N lam x) x) at hco
  rw [hright, hsym] at hco
  simpa [x, R] using hco

/-- Cauchy--Schwarz upper control for the resolvent quadratic value. -/
theorem re_inner_resolvent_le_norm_mul_norm
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    Complex.re
        (inner ℂ
          (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b) ≤
      ‖shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b‖ * ‖b‖ := by
  let x := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b
  calc
    Complex.re (inner ℂ x b) ≤ |Complex.re (inner ℂ x b)| := le_abs_self _
    _ ≤ ‖inner ℂ x b‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖b‖ := norm_inner_le_norm x b

/-- Multiplicative resolvent norm bound. This is the primary denominator-free
form; division by `-lam` is only a convenience corollary. -/
theorem neg_mul_norm_resolvent_le
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    (-lam) *
        ‖shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b‖ ≤
      ‖b‖ := by
  let x := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b
  by_cases hx : x = 0
  · simp [x, hx]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hlow :=
      neg_mul_norm_sq_resolvent_le_re_inner p hL N hprev hlam b
    have hupp :=
      re_inner_resolvent_le_norm_mul_norm p hL N hprev hlam b
    have hcomb : (-lam) * ‖x‖ ^ 2 ≤ ‖x‖ * ‖b‖ := by
      exact le_trans (by simpa [x] using hlow) (by simpa [x] using hupp)
    have hmul :
        ‖x‖ * ((-lam) * ‖x‖) ≤ ‖x‖ * ‖b‖ := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcomb
    have hmain : (-lam) * ‖x‖ ≤ ‖b‖ :=
      (mul_le_mul_left hxpos).mp hmul
    simpa [x] using hmain

/-- Convenience quotient form of the resolvent norm estimate. -/
theorem norm_resolvent_le_div
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    ‖shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b‖ ≤
      ‖b‖ / (-lam) := by
  have h := neg_mul_norm_resolvent_le p hL N hprev hlam b
  exact (le_div_iff₀ (neg_pos.mpr hlam)).2 (by simpa [mul_comm] using h)

/-- The inverse of the symmetric shifted predecessor block is symmetric. -/
theorem shiftedIntrinsicPredecessorResolvent_isSymmetric
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := intrinsicParityPredecessorSubspace p N)
      (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam) := by
  intro x y
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hsym := shiftedIntrinsicPredecessorBlock_isSymmetric p L N lam (R x) (R y)
  have hx : shiftedIntrinsicPredecessorBlock p L N lam (R x) = x := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam x
  have hy : shiftedIntrinsicPredecessorBlock p L N lam (R y) = y := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam y
  rw [hx, hy] at hsym
  simpa [R] using hsym.symm

/-- The resolvent quadratic value is fixed by complex conjugation and therefore
real. -/
theorem star_inner_resolvent_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    star
        (inner ℂ
          (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b) =
      inner ℂ
        (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hsym := shiftedIntrinsicPredecessorResolvent_isSymmetric
    p hL N hprev hlam b b
  change inner ℂ (R b) b = inner ℂ b (R b) at hsym
  calc
    star (inner ℂ (R b) b) = inner ℂ b (R b) := by simp
    _ = inner ℂ (R b) b := hsym.symm

/-- The negative-shift resolvent quadratic value is nonnegative. -/
theorem re_inner_resolvent_nonnegative
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ
        (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b) := by
  have hlow := neg_mul_norm_sq_resolvent_le_re_inner p hL N hprev hlam b
  have hbase :
      0 ≤ (-lam) *
        ‖shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b‖ ^ 2 :=
    mul_nonneg (le_of_lt (neg_pos.mpr hlam)) (sq_nonneg _)
  exact hbase.trans hlow

/-- Denominator-free quadratic resolvent bound. -/
theorem neg_mul_re_inner_resolvent_le_norm_sq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    (-lam) * Complex.re
        (inner ℂ
          (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b) b) ≤
      ‖b‖ ^ 2 := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hupp := re_inner_resolvent_le_norm_mul_norm p hL N hprev hlam b
  have hnorm := neg_mul_norm_resolvent_le p hL N hprev hlam b
  have hnonneg : 0 ≤ -lam := le_of_lt (neg_pos.mpr hlam)
  calc
    (-lam) * Complex.re (inner ℂ (R b) b) ≤
        (-lam) * (‖R b‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (by simpa [R] using hupp) hnonneg
    _ = ((-lam) * ‖R b‖) * ‖b‖ := by ring
    _ ≤ ‖b‖ * ‖b‖ :=
      mul_le_mul_of_nonneg_right (by simpa [R] using hnorm) (norm_nonneg b)
    _ = ‖b‖ ^ 2 := by ring

/-- Real part of the canonical cubic shell shifted diagonal term. -/
theorem re_cubicShell_shift_eq
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ) :
    Complex.re
        (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1)))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1)) -
          (lam : ℂ) *
            inner ℂ
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))) =
      Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1)))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) -
        lam *
          ‖(intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 := by
  have hnorm :
      Complex.re
        (inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))) =
      ‖(intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ)
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))).symm
  rw [Complex.sub_re, Complex.mul_re]
  simp [hnorm]

/-- E3-B1 realness theorem for the explicit #121 Schur scalar. -/
theorem star_cubicExplicitSchurScalar_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star (cubicExplicitSchurScalar p hL N hprev lam hlam) =
      cubicExplicitSchurScalar p hL N hprev lam hlam := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hTcstar :
      star
          (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    calc
      star
          (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) := by simp
      _ = inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) :=
        (parityCompressedCanonical_isSymmetric p L (N + 1)
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))).symm
  have hRstar :
      star
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [R] using star_inner_resolvent_eq p hL N hprev hlam b
  change
    star
      (inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        (lam : ℂ) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))) =
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
      (lam : ℂ) *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
      inner ℂ
        ((R b : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1))
  simp [hTcstar, hRstar]

/-- With E3-B1 metric realness available, the exact #121 bridge loses the
conjugation: the quotient secular scalar is the explicit real Schur scalar
divided by the positive shell self-inner normalization. -/
theorem cubicSecularScalar_eq_cubicExplicitSchurScalar_div
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar p hL N hprev lam hlam =
      cubicExplicitSchurScalar p hL N hprev lam hlam /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  rw [cubicSecularScalar_eq_star_cubicExplicitSchurScalar_div
    p hL N hN hprev lam hlam]
  rw [star_cubicExplicitSchurScalar_eq p hL N hprev lam hlam]

/-- At an exact explicit secular root, the real shifted shell diagonal equals
the nonnegative resolvent quadratic value. -/
theorem cubicExplicitSchurRoot_shift_nonnegative
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicExplicitSchurScalar p hL N hprev lam hlam = 0) :
    0 ≤
      Complex.re
        (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1)))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1)) -
          (lam : ℂ) *
            inner ℂ
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have heq :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        (lam : ℂ) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        ((R b : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    change
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        (lam : ℂ) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 at hroot
    exact sub_eq_zero.mp hroot
  rw [show intrinsicCubicShellPart p N = c by rfl]
  rw [heq]
  simpa [R, b] using re_inner_resolvent_nonnegative p hL N hprev hlam b

/-- First theorem-backed deformation constraint at the `mu = 0` predecessor
floor. At a negative explicit secular root, the shifted shell diagonal cannot
exceed the cubic coupling budget. -/
theorem cubicExplicitSchurRoot_metric_bound
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicExplicitSchurScalar p hL N hprev lam hlam = 0) :
    (-lam) *
      Complex.re
        (inner ℂ
            (parityCompressedCanonical p L (N + 1)
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1)))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1)) -
          (lam : ℂ) *
            inner ℂ
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))) ≤
      ‖intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)‖ ^ 2 := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have heq :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        (lam : ℂ) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        ((R b : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    change
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        (lam : ℂ) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
        inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 at hroot
    exact sub_eq_zero.mp hroot
  rw [show intrinsicCubicShellPart p N = c by rfl]
  rw [heq]
  simpa [R, b] using
    neg_mul_re_inner_resolvent_le_norm_sq p hL N hprev hlam b

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorBlock_isSymmetric
#print axioms Zeta23.CCM.re_inner_shiftedIntrinsicPredecessorBlock_ge
#print axioms Zeta23.CCM.neg_mul_norm_resolvent_le
#print axioms Zeta23.CCM.shiftedIntrinsicPredecessorResolvent_isSymmetric
#print axioms Zeta23.CCM.star_cubicExplicitSchurScalar_eq
#print axioms Zeta23.CCM.cubicSecularScalar_eq_cubicExplicitSchurScalar_div
#print axioms Zeta23.CCM.cubicExplicitSchurRoot_metric_bound
