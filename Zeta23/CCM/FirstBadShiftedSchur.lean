import Zeta23.CCM.FirstBadIntrinsicBlock
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-D2: intrinsic direct sum and shifted Schur reduction

PR #112 theorem-locked the intrinsic predecessor subspace `W`, the intrinsic
one-step shell `S`, `W ⊔ S = ⊤`, `finrank S = 1`, and a first-bad negative
eigenmode with nonzero shell content.  This module turns that geometry into the
safe block reduction needed for a Schur/Feshbach argument.

The predecessor block is the projected block `A = P_W T|_W`; no invariance of
`W` or `S` under the compressed canonical operator is assumed.  For a negative
first-bad eigenvalue `lam < 0`, predecessor nonnegativity implies that
`A - lam I` is invertible.  The predecessor coordinates are therefore uniquely
resolved from the one-dimensional shell coordinate, and the eigenvalue equation
reduces to a scalar shifted Schur identity.

Firewalls:
* never use `A⁻¹` at zero;
* no shell invariance is claimed;
* no negative-index-one theorem is used;
* no unitary parity transport, interlacing, positivity, finite-to-infinite, or
  RH theorem is claimed.
-/

/-- The intrinsic predecessor and intrinsic successor shell are disjoint. -/
theorem intrinsicPredecessor_disjoint_shell
    (p : ReversalParity) (N : ℕ) :
    Disjoint (intrinsicParityPredecessorSubspace p N)
      (intrinsicParitySuccShell p N) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxW, hxS⟩
  have hxW' := hxW
  change
    ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      euclideanParityEmbeddedSuccSubspace p N at hxW'
  have hxS' := hxS
  change
    ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace p (N + 1) at hxS'
  have hinner :
      inner ℂ
          ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0 := by
    exact Submodule.inner_left_of_mem_orthogonal hxW' hxS'.1
  have hx0Ambient :
      ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0 :=
    (inner_self_eq_zero).mp hinner
  have hx0 : x = 0 := by
    apply Subtype.ext
    exact hx0Ambient
  simpa [hx0]

/-- The intrinsic predecessor and intrinsic successor shell form a genuine
complementary pair in the successor parity subtype. -/
theorem intrinsicPredecessor_isCompl_shell
    (p : ReversalParity) (N : ℕ) :
    IsCompl (intrinsicParityPredecessorSubspace p N)
      (intrinsicParitySuccShell p N) := by
  constructor
  · exact intrinsicPredecessor_disjoint_shell p N
  · rw [codisjoint_iff]
    exact intrinsicPredecessor_sup_shell p N

/-- Canonical intrinsic direct-sum coordinates `(W × S) ≃ V`. -/
def intrinsicPredecessorShellEquiv
    (p : ReversalParity) (N : ℕ) :
    (intrinsicParityPredecessorSubspace p N ×
      intrinsicParitySuccShell p N) ≃ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p (N + 1) :=
  Submodule.prodEquivOfIsCompl
    (intrinsicParityPredecessorSubspace p N)
    (intrinsicParitySuccShell p N)
    (intrinsicPredecessor_isCompl_shell p N)

/-- Canonical predecessor coordinate in the intrinsic `W ⊕ S` decomposition. -/
def intrinsicPredecessorPart
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p (N + 1) →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  Submodule.projectionOnto
    (intrinsicParityPredecessorSubspace p N)
    (intrinsicParitySuccShell p N)
    (intrinsicPredecessor_isCompl_shell p N)

/-- Canonical shell coordinate in the intrinsic `W ⊕ S` decomposition. -/
def intrinsicShellPart
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p (N + 1) →ₗ[ℂ]
      intrinsicParitySuccShell p N :=
  Submodule.projectionOnto
    (intrinsicParitySuccShell p N)
    (intrinsicParityPredecessorSubspace p N)
    (intrinsicPredecessor_isCompl_shell p N).symm

/-- Canonical predecessor plus canonical shell reconstructs every successor
vector. -/
theorem intrinsicPredecessorPart_add_shellPart
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    ((intrinsicPredecessorPart p N v :
        intrinsicParityPredecessorSubspace p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) +
      ((intrinsicShellPart p N v : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) = v := by
  exact Submodule.projection_add_projection_eq_self
    (intrinsicPredecessor_isCompl_shell p N) v

/-- The canonical shell coordinate vanishes exactly on the intrinsic
predecessor. -/
theorem intrinsicShellPart_eq_zero_iff
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)} :
    intrinsicShellPart p N v = 0 ↔
      v ∈ intrinsicParityPredecessorSubspace p N := by
  exact Submodule.projectionOnto_apply_eq_zero_iff
    (intrinsicPredecessor_isCompl_shell p N).symm

/-- Shell vectors are orthogonal to predecessor vectors. -/
theorem inner_intrinsicShell_predecessor_eq_zero
    (p : ReversalParity) (N : ℕ)
    (s : intrinsicParitySuccShell p N)
    (w : intrinsicParityPredecessorSubspace p N) :
    inner ℂ
      ((s : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      ((w : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  change
    inner ℂ
      (((s : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
      (((w : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0
  have hs := s.property
  change
    (((s : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace p (N + 1) at hs
  exact Submodule.inner_left_of_mem_orthogonal w.property hs.1

/-- Predecessor vectors are orthogonal to shell vectors. -/
theorem inner_intrinsicPredecessor_shell_eq_zero
    (p : ReversalParity) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N)
    (s : intrinsicParitySuccShell p N) :
    inner ℂ
      ((w : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      ((s : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  change
    inner ℂ
      (((w : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
      (((s : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0
  have hs := s.property
  change
    (((s : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace p (N + 1) at hs
  exact Submodule.inner_right_of_mem_orthogonal w.property hs.1

/-- For a first-bad negative eigenmode, the *canonical* intrinsic shell
coordinate is nonzero. -/
theorem negative_eigenmode_intrinsicShellPart_ne_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    intrinsicShellPart p N v ≠ 0 := by
  have hnotCentered :=
    negative_eigenmode_not_centeredImage
      p hL N hprev hlam hvne hveig
  have hnotAmbient :=
    not_mem_euclideanParityEmbeddedSuccSubspace_of_not_centeredImage
      p N hnotCentered
  have hnotIntrinsic : v ∉ intrinsicParityPredecessorSubspace p N := by
    simpa only [mem_intrinsicParityPredecessorSubspace_iff] using hnotAmbient
  intro hs0
  apply hnotIntrinsic
  exact (intrinsicShellPart_eq_zero_iff p N).mp hs0

/-- Projected predecessor block `A = P_W T|_W`.  This definition does not
assert that the compressed canonical operator preserves `W`. -/
def intrinsicPredecessorBlock
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (intrinsicPredecessorPart p N).comp
    ((parityCompressedCanonical p L (N + 1)).comp
      (intrinsicParityPredecessorSubspace p N).subtype)

/-- Shell-to-predecessor block `B = P_W T|_S`. -/
def intrinsicShellToPredecessor
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParitySuccShell p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (intrinsicPredecessorPart p N).comp
    ((parityCompressedCanonical p L (N + 1)).comp
      (intrinsicParitySuccShell p N).subtype)

/-- The projected predecessor block has exactly the same self-inner value as
the full compressed operator on predecessor vectors. -/
theorem inner_intrinsicPredecessorBlock_self
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    inner ℂ
        ((intrinsicPredecessorBlock p L N w :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let y := parityCompressedCanonical p L (N + 1)
    (w : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicShell_predecessor_eq_zero
    p N (intrinsicShellPart p N y) w
  change
    inner ℂ
      ((intrinsicPredecessorPart p N y : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)) =
    inner ℂ y
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
  rw [← hrec, inner_add_left, hort, add_zero]

/-- Predecessor nonnegativity descends to the projected predecessor block. -/
theorem re_inner_intrinsicPredecessorBlock_nonnegative
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (w : intrinsicParityPredecessorSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ
        ((intrinsicPredecessorBlock p L N w :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  rw [inner_intrinsicPredecessorBlock_self]
  rw [re_inner_parityCompressedCanonical_self]
  let wAmbient : euclideanParityEmbeddedSuccSubspace p N :=
    ⟨(((w : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))), w.property⟩
  exact re_inner_successor_nonnegative_on_embeddedPredecessor
    p hL N hprev wAmbient

/-- Safe shifted predecessor block `A - lam I`. -/
def shiftedIntrinsicPredecessorBlock
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  intrinsicPredecessorBlock p L N -
    (lam : ℂ) • LinearMap.id

/-- A negative shift has trivial kernel because the predecessor block is
nonnegative. -/
theorem shiftedIntrinsicPredecessorBlock_eq_zero_implies
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {w : intrinsicParityPredecessorSubspace p N}
    (hshift : shiftedIntrinsicPredecessorBlock p L N lam w = 0) :
    w = 0 := by
  by_contra hwne
  have hAw :
      intrinsicPredecessorBlock p L N w = (lam : ℂ) • w := by
    change
      intrinsicPredecessorBlock p L N w - (lam : ℂ) • w = 0 at hshift
    exact sub_eq_zero.mp hshift
  have hAwAmbient :
      ((intrinsicPredecessorBlock p L N w :
          intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) =
        (lam : ℂ) •
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    exact congrArg
      (fun z : intrinsicParityPredecessorSubspace p N =>
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))) hAw
  have hnonneg :=
    re_inner_intrinsicPredecessorBlock_nonnegative p hL N hprev w
  rw [hAwAmbient, inner_smul_real_left] at hnonneg
  have hnonneg' :
      0 ≤ lam * Complex.re
        (inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    simpa [Algebra.smul_def, Complex.mul_re] using hnonneg
  have hnorm :
      Complex.re
        (inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        ‖(w : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ)
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))).symm
  rw [hnorm] at hnonneg'
  have hwAmbientNe :
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    intro hw0
    apply hwne
    exact Subtype.ext hw0
  have hneg :
      lam * ‖(w : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hlam (show
      0 < ‖(w : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 by
        positivity)
  exact (not_lt_of_ge hnonneg') hneg

/-- `A - lam I` is injective for every `lam < 0`. -/
theorem shiftedIntrinsicPredecessorBlock_injective
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    Function.Injective (shiftedIntrinsicPredecessorBlock p L N lam) := by
  intro x y hxy
  have hzero :
      shiftedIntrinsicPredecessorBlock p L N lam (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub := shiftedIntrinsicPredecessorBlock_eq_zero_implies
    p hL N hprev hlam hzero
  exact sub_eq_zero.mp hsub

/-- The safe negative shift is a linear equivalence on the finite-dimensional
predecessor block. -/
def shiftedIntrinsicPredecessorEquiv
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicParityPredecessorSubspace p N ≃ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N := by
  let Ashift := shiftedIntrinsicPredecessorBlock p L N lam
  have hinj : Function.Injective Ashift :=
    shiftedIntrinsicPredecessorBlock_injective p hL N hprev hlam
  have hsurj : Function.Surjective Ashift :=
    LinearMap.injective_iff_surjective.mp hinj
  exact LinearEquiv.ofBijective Ashift ⟨hinj, hsurj⟩

/-- Canonical shifted predecessor resolvent `(A - lam I)⁻¹`. -/
def shiftedIntrinsicPredecessorResolvent
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  (shiftedIntrinsicPredecessorEquiv p hL N hprev lam hlam).symm.toLinearMap

/-- The predecessor projection of an eigenmode satisfies the shifted block
equation `(A - lam I) w = -B s`. -/
theorem eigenmode_shiftedPredecessorBlock_eq
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    {lam : ℝ}
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    shiftedIntrinsicPredecessorBlock p L N lam
        (intrinsicPredecessorPart p N v) =
      - intrinsicShellToPredecessor p L N (intrinsicShellPart p N v) := by
  let w := intrinsicPredecessorPart p N v
  let s := intrinsicShellPart p N v
  have hrec := intrinsicPredecessorPart_add_shellPart p N v
  have hblock :
      intrinsicPredecessorBlock p L N w +
          intrinsicShellToPredecessor p L N s =
        (lam : ℂ) • w := by
    calc
      intrinsicPredecessorBlock p L N w +
          intrinsicShellToPredecessor p L N s =
        intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1)
            ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (s : euclideanParityBoundaryFlatSubspace p (N + 1)))) := by
            simp [intrinsicPredecessorBlock, intrinsicShellToPredecessor,
              map_add]
      _ = intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1) v) := by
            rw [hrec]
      _ = intrinsicPredecessorPart p N ((lam : ℂ) • v) := by
            rw [hveig]
      _ = (lam : ℂ) • w := by
            rw [map_smul]
  change
    intrinsicPredecessorBlock p L N w - (lam : ℂ) • w =
      - intrinsicShellToPredecessor p L N s
  calc
    intrinsicPredecessorBlock p L N w - (lam : ℂ) • w =
        intrinsicPredecessorBlock p L N w -
          (intrinsicPredecessorBlock p L N w +
            intrinsicShellToPredecessor p L N s) := by rw [hblock]
    _ = - intrinsicShellToPredecessor p L N s := by abel

/-- The entire predecessor coordinate is resolved from the one-dimensional
shell coordinate by the safe shifted inverse. -/
theorem eigenmode_predecessorPart_eq_neg_resolvent_shell
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    intrinsicPredecessorPart p N v =
      - shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
          (intrinsicShellToPredecessor p L N (intrinsicShellPart p N v)) := by
  let E := shiftedIntrinsicPredecessorEquiv p hL N hprev lam hlam
  have hblock := eigenmode_shiftedPredecessorBlock_eq p L N hveig
  have happ := congrArg E.symm hblock
  change
    E.symm
        (shiftedIntrinsicPredecessorBlock p L N lam
          (intrinsicPredecessorPart p N v)) =
      E.symm
        (- intrinsicShellToPredecessor p L N (intrinsicShellPart p N v)) at happ
  have hEapply :
      E (intrinsicPredecessorPart p N v) =
        shiftedIntrinsicPredecessorBlock p L N lam
          (intrinsicPredecessorPart p N v) := by
    rfl
  have hleft :
      E.symm
          (shiftedIntrinsicPredecessorBlock p L N lam
            (intrinsicPredecessorPart p N v)) =
        intrinsicPredecessorPart p N v := by
    rw [← hEapply]
    exact E.symm_apply_apply _
  rw [hleft] at happ
  simpa [shiftedIntrinsicPredecessorResolvent, E] using happ

/-- Basis-free scalar shifted Schur identity for a negative first-bad
eigenmode.  The actual canonical shell component is used, so no arbitrary
normalization of the one-dimensional shell is required. -/
theorem eigenmode_shiftedSchur_identity
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    let s := intrinsicShellPart p N v
    let b := intrinsicShellToPredecessor p L N s
    let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
    inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) -
      (lam : ℂ) *
        inner ℂ
          (s : euclideanParityBoundaryFlatSubspace p (N + 1))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) -
      inner ℂ
        ((R b : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  dsimp
  let w := intrinsicPredecessorPart p N v
  let s := intrinsicShellPart p N v
  let b := intrinsicShellToPredecessor p L N s
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hrec := intrinsicPredecessorPart_add_shellPart p N v
  have hwres : w = - R b := by
    simpa [w, s, b, R] using
      eigenmode_predecessorPart_eq_neg_resolvent_shell
        p hL N hprev hlam hveig
  have hsym :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (s : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    exact parityCompressedCanonical_isSymmetric p L (N + 1)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
      (s : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hBT :
      inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (s : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    let y := parityCompressedCanonical p L (N + 1)
      (s : euclideanParityBoundaryFlatSubspace p (N + 1))
    have hyrec := intrinsicPredecessorPart_add_shellPart p N y
    have hort := inner_intrinsicPredecessor_shell_eq_zero
      p N w (intrinsicShellPart p N y)
    change
      inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) y =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))
    rw [← hyrec, inner_add_right, hort, add_zero]
    rfl
  have hcross :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        - inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rw [hsym, hBT, hwres]
    simp
  have heigInner := congrArg
    (fun z : euclideanParityBoundaryFlatSubspace p (N + 1) =>
      inner ℂ z (s : euclideanParityBoundaryFlatSubspace p (N + 1)))
    hveig
  have hws0 := inner_intrinsicPredecessor_shell_eq_zero p N w s
  have heq :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) +
        inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (s : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      (lam : ℂ) *
        inner ℂ
          (s : euclideanParityBoundaryFlatSubspace p (N + 1))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rw [← hrec] at heigInner
    rw [map_add, inner_add_left] at heigInner
    have hlaminner :
        inner ℂ
            ((lam : ℂ) •
              ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
                (s : euclideanParityBoundaryFlatSubspace p (N + 1))))
            (s : euclideanParityBoundaryFlatSubspace p (N + 1)) =
          (lam : ℂ) *
            inner ℂ
              (s : euclideanParityBoundaryFlatSubspace p (N + 1))
              (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rw [inner_smul_left, inner_add_left, hws0, zero_add]
      simp
    exact heigInner.trans hlaminner
  rw [hcross] at heq
  rw [← heq]
  ring

/-- Complete D2 package for one negative first-bad eigenmode: canonical shell
content is nonzero, the shifted predecessor block is invertible, all
predecessor coordinates are resolved from the shell, and the basis-free scalar
Schur identity holds. -/
theorem negative_eigenmode_shiftedSchur_package
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    intrinsicShellPart p N v ≠ 0 ∧
      Function.Bijective (shiftedIntrinsicPredecessorBlock p L N lam) ∧
      intrinsicPredecessorPart p N v =
        - shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
            (intrinsicShellToPredecessor p L N (intrinsicShellPart p N v)) ∧
      (let s := intrinsicShellPart p N v
       let b := intrinsicShellToPredecessor p L N s
       let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
       inner ℂ
           (parityCompressedCanonical p L (N + 1)
             (s : euclideanParityBoundaryFlatSubspace p (N + 1)))
           (s : euclideanParityBoundaryFlatSubspace p (N + 1)) -
         (lam : ℂ) *
           inner ℂ
             (s : euclideanParityBoundaryFlatSubspace p (N + 1))
             (s : euclideanParityBoundaryFlatSubspace p (N + 1)) -
         inner ℂ
           ((R b : intrinsicParityPredecessorSubspace p N) :
             euclideanParityBoundaryFlatSubspace p (N + 1))
           (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0) := by
  have hsne := negative_eigenmode_intrinsicShellPart_ne_zero
    p hL N hprev hlam hvne hveig
  have hinj := shiftedIntrinsicPredecessorBlock_injective
    p hL N hprev hlam
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hres := eigenmode_predecessorPart_eq_neg_resolvent_shell
    p hL N hprev hlam hveig
  have hschur := eigenmode_shiftedSchur_identity
    p hL N hprev hlam hveig
  exact ⟨hsne, ⟨hinj, hsurj⟩, hres, hschur⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessor_isCompl_shell
#print axioms Zeta23.CCM.negative_eigenmode_intrinsicShellPart_ne_zero
#print axioms Zeta23.CCM.re_inner_intrinsicPredecessorBlock_nonnegative
#print axioms Zeta23.CCM.shiftedIntrinsicPredecessorBlock_injective
#print axioms Zeta23.CCM.eigenmode_predecessorPart_eq_neg_resolvent_shell
#print axioms Zeta23.CCM.eigenmode_shiftedSchur_identity
#print axioms Zeta23.CCM.negative_eigenmode_shiftedSchur_package
