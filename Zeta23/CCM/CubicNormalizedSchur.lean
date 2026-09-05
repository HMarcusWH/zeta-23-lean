import Zeta23.CCM.CubicShellIncidence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E2: canonical cubic coordinate and normalized Schur

PR #113 gives canonical intrinsic `W ⊕ S` coordinates and a basis-free shifted
Schur identity written in the actual shell component of a negative first-bad
eigenmode. PR #115 proves that the parity-uniform cubic channel has nonzero
coordinate in the same one-dimensional shell.

This module uses that cubic shell vector as the canonical scalar coordinate on
the one new N-flow degree of freedom. The full eigenvector is then rescaled so
its shell component is exactly the canonical cubic shell vector, allowing the
existing #113 Schur theorem to be reused without a new block calculation or an
arbitrary shell basis.

Firewalls:
* a nonzero cubic shell coordinate does not make the full cubic vector pure shell;
* no shell invariance is claimed;
* D remains algebraic, not unitary/isometric;
* no nonzeroness of `cubicDefectFunctional` is claimed;
* only `A - lam I` for `lam < 0` is used, never `A⁻¹` at zero;
* the normalized Schur identity is a reduction, not a contradiction;
* no positivity, finite-to-infinite closure, or RH theorem is claimed.
-/

/-- Canonical complex scalar coordinate on the intrinsic one-step shell, using
`intrinsicCubicShellPart` as the distinguished nonzero direction. The
definition is total; `1 ≤ N` is required only for theorems asserting that this
is a faithful coordinate. Mathlib's complex inner product is linear in the
second argument. -/
def intrinsicCubicShellCoordinate
    (p : ReversalParity) (N : ℕ) :
    intrinsicParitySuccShell p N →ₗ[ℂ] ℂ where
  toFun := fun s =>
    inner ℂ
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) /
      inner ℂ
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
  map_add' := by
    intro x y
    change
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((x : euclideanParityBoundaryFlatSubspace p (N + 1)) +
            (y : euclideanParityBoundaryFlatSubspace p (N + 1))) /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (x : euclideanParityBoundaryFlatSubspace p (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) +
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (y : euclideanParityBoundaryFlatSubspace p (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
    rw [inner_add_right]
    ring
  map_smul' := by
    intro a x
    change
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (a • (x : euclideanParityBoundaryFlatSubspace p (N + 1))) /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
      a •
        (inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (x : euclideanParityBoundaryFlatSubspace p (N + 1)) /
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1)))
    rw [inner_smul_right]
    simp only [smul_eq_mul]
    ring

/-- The canonical cubic shell vector has coordinate one. -/
theorem intrinsicCubicShellCoordinate_cubic
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    intrinsicCubicShellCoordinate p N (intrinsicCubicShellPart p N) = 1 := by
  have hc : intrinsicCubicShellPart p N ≠ 0 :=
    intrinsicCubicShellPart_ne_zero p N hN
  have hcCarrier :
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    intro hzero
    apply hc
    apply Subtype.ext
    exact hzero
  have hcc :
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    intro hzero
    apply hcCarrier
    exact inner_self_eq_zero.mp hzero
  change
    inner ℂ
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) /
      inner ℂ
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) = 1
  exact div_self hcc

/-- Every vector in the one-dimensional intrinsic shell is reconstructed from
its canonical cubic coordinate. This is the E1b scalar-alignment theorem. -/
theorem intrinsicCubicShellCoordinate_smul_cubic_eq
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    (s : intrinsicParitySuccShell p N) :
    intrinsicCubicShellCoordinate p N s • intrinsicCubicShellPart p N = s := by
  obtain ⟨a, ha⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (finrank_intrinsicParitySuccShell p N hN)
      (intrinsicCubicShellPart_ne_zero p N hN) s
  rw [← ha, map_smul, intrinsicCubicShellCoordinate_cubic p N hN]
  simp

/-- The cubic shell coordinate vanishes exactly on the zero shell vector. -/
theorem intrinsicCubicShellCoordinate_eq_zero_iff
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    {s : intrinsicParitySuccShell p N} :
    intrinsicCubicShellCoordinate p N s = 0 ↔ s = 0 := by
  constructor
  · intro hzero
    have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq p N hN s
    rw [hzero, zero_smul] at hrep
    exact hrep.symm
  · rintro rfl
    exact map_zero (intrinsicCubicShellCoordinate p N)

/-- Canonical scalar coordinate on the successor carrier modulo the centered
predecessor: first take the intrinsic shell projection, then read its cubic
coordinate. -/
def intrinsicCubicQuotientCoordinate
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p (N + 1) →ₗ[ℂ] ℂ :=
  (intrinsicCubicShellCoordinate p N).comp (intrinsicShellPart p N)

/-- The canonical cubic quotient coordinate vanishes exactly on vectors
inherited from the centered predecessor. -/
theorem intrinsicCubicQuotientCoordinate_eq_zero_iff
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)} :
    intrinsicCubicQuotientCoordinate p N v = 0 ↔
      v ∈ intrinsicParityPredecessorSubspace p N := by
  constructor
  · intro hzero
    have hscoord :
        intrinsicCubicShellCoordinate p N (intrinsicShellPart p N v) = 0 := by
      simpa [intrinsicCubicQuotientCoordinate] using hzero
    have hs0 : intrinsicShellPart p N v = 0 :=
      (intrinsicCubicShellCoordinate_eq_zero_iff p N hN).mp hscoord
    exact (intrinsicShellPart_eq_zero_iff p N).mp hs0
  · intro hv
    have hs0 : intrinsicShellPart p N v = 0 :=
      (intrinsicShellPart_eq_zero_iff p N).mpr hv
    simp [intrinsicCubicQuotientCoordinate, hs0]

/-- The parity-uniform successor cubic vector is normalized to quotient
coordinate one. -/
theorem intrinsicCubicQuotientCoordinate_successorParityCubicVector
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    intrinsicCubicQuotientCoordinate p N (successorParityCubicVector p N) = 1 := by
  change
    intrinsicCubicShellCoordinate p N
      (intrinsicShellPart p N (successorParityCubicVector p N)) = 1
  simpa [intrinsicCubicShellPart] using
    intrinsicCubicShellCoordinate_cubic p N hN

/-- On the odd successor carrier, the exact #112 cubic defect functional is
literally the canonical coordinate of the exact parity intertwining defect in
the unique new N-flow direction. This does not assert that the functional is
nonzero on any particular input. -/
theorem intrinsicCubicQuotientCoordinate_intertwiningDefect
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (z : euclideanEvenBoundaryFlatSubspace (N + 1)) :
    intrinsicCubicQuotientCoordinate .odd N
        (evenOddCompressedIntertwiningDefect L (N + 1) z) =
      cubicDefectFunctional L (N + 1) z := by
  have hfac :
      (evenOddCompressedIntertwiningDefect L (N + 1) z :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      cubicDefectFunctional L (N + 1) z •
        successorParityCubicVector .odd N := by
    simpa [successorParityCubicVector] using
      evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
        hL (N + 1) (by omega) z
  rw [hfac, map_smul,
    intrinsicCubicQuotientCoordinate_successorParityCubicVector .odd N hN]
  simp

/-- A genuine negative first-bad eigenmode has nonzero canonical cubic quotient
coordinate because #113 proves its shell projection is nonzero and the cubic
coordinate is faithful on the one-dimensional shell. -/
theorem negative_eigenmode_intrinsicCubicQuotientCoordinate_ne_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
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
    intrinsicCubicQuotientCoordinate p N v ≠ 0 := by
  have hsne :=
    negative_eigenmode_intrinsicShellPart_ne_zero
      p hL N hprev hlam hvne hveig
  intro hzero
  have hscoord :
      intrinsicCubicShellCoordinate p N (intrinsicShellPart p N v) = 0 := by
    simpa [intrinsicCubicQuotientCoordinate] using hzero
  have hs0 : intrinsicShellPart p N v = 0 :=
    (intrinsicCubicShellCoordinate_eq_zero_iff p N hN).mp hscoord
  exact hsne hs0

/-- Rescale a successor vector so its canonical cubic quotient coordinate is
one whenever that coordinate is nonzero. The definition is total. -/
def cubicNormalizedSuccessorVector
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    euclideanParityBoundaryFlatSubspace p (N + 1) :=
  (intrinsicCubicQuotientCoordinate p N v)⁻¹ • v

/-- Scalar normalization preserves the compressed eigenvalue equation. -/
theorem cubicNormalizedSuccessorVector_eigenmode
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    {lam : ℝ}
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    parityCompressedCanonical p L (N + 1)
        (cubicNormalizedSuccessorVector p N v) =
      (lam : ℂ) • cubicNormalizedSuccessorVector p N v := by
  change
    parityCompressedCanonical p L (N + 1)
        ((intrinsicCubicQuotientCoordinate p N v)⁻¹ • v) =
      (lam : ℂ) •
        ((intrinsicCubicQuotientCoordinate p N v)⁻¹ • v)
  rw [map_smul, hveig, smul_smul, smul_smul]
  exact congrArg (fun a : ℂ => a • v) (mul_comm _ _)

/-- If the cubic quotient coordinate is nonzero, normalization makes the shell
component exactly the canonical cubic shell vector. -/
theorem intrinsicShellPart_cubicNormalizedSuccessorVector
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hκ : intrinsicCubicQuotientCoordinate p N v ≠ 0) :
    intrinsicShellPart p N (cubicNormalizedSuccessorVector p N v) =
      intrinsicCubicShellPart p N := by
  have hκ' :
      intrinsicCubicShellCoordinate p N (intrinsicShellPart p N v) ≠ 0 := by
    simpa [intrinsicCubicQuotientCoordinate] using hκ
  have hrep :=
    intrinsicCubicShellCoordinate_smul_cubic_eq
      p N hN (intrinsicShellPart p N v)
  dsimp [cubicNormalizedSuccessorVector]
  rw [map_smul]
  rw [← hrep]
  simp [intrinsicCubicQuotientCoordinate, hκ', smul_smul]

/-- E2 endpoint: after canonical normalization of a genuine negative first-bad
eigenmode, #113's shifted Schur identity is written directly on the canonical
cubic shell line. -/
theorem eigenmode_cubicNormalized_shiftedSchur_identity
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
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
    let c := intrinsicCubicShellPart p N
    let b := intrinsicShellToPredecessor p L N c
    let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
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
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  have hκ :=
    negative_eigenmode_intrinsicCubicQuotientCoordinate_ne_zero
      p hL N hN hprev hlam hvne hveig
  let vhat := cubicNormalizedSuccessorVector p N v
  have hveigHat :
      parityCompressedCanonical p L (N + 1) vhat = (lam : ℂ) • vhat := by
    simpa [vhat] using
      cubicNormalizedSuccessorVector_eigenmode p L N hveig
  have hshellHat :
      intrinsicShellPart p N vhat = intrinsicCubicShellPart p N := by
    simpa [vhat] using
      intrinsicShellPart_cubicNormalizedSuccessorVector p N hN hκ
  have hschur :=
    eigenmode_shiftedSchur_identity p hL N hprev hlam hveigHat
  simpa [hshellHat] using hschur

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicCubicShellCoordinate_smul_cubic_eq
#print axioms Zeta23.CCM.intrinsicCubicQuotientCoordinate_eq_zero_iff
#print axioms Zeta23.CCM.intrinsicCubicQuotientCoordinate_intertwiningDefect
#print axioms Zeta23.CCM.eigenmode_cubicNormalized_shiftedSchur_identity
