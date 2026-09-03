import Zeta23.CCM.ConstrainedParitySpectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-A: intrinsic predecessor / shell geometry

This module internalizes the exact centered predecessor image inside the
successor parity-constrained Euclidean subtype. It proves that the intrinsic
orthogonal successor shell is one-dimensional, upgrades #107 non-inheritance
to a nonzero orthogonal shell projection, and packages predecessor
nonnegativity directly on the successor compressed operator.

No shell invariance, negative-index theorem, KKT equation, Schur/Feshbach
formula, positivity theorem, finite-to-infinite theorem, or RH theorem is
claimed here.
-/

/-- Exact centered predecessor inclusion between parity-constrained Euclidean
subtypes. -/
def parityEmbeddedPredecessorLinearMap
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p (N + 1) where
  toFun := fun x =>
    ⟨euclideanCenteredZeroExtend (Nat.le_succ N) x,
      euclideanCenteredZeroExtend_mem_euclideanParityBoundaryFlatSubspace
        p (Nat.le_succ N) x.property⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

theorem parityEmbeddedPredecessorLinearMap_injective
    (p : ReversalParity) (N : ℕ) :
    Function.Injective (parityEmbeddedPredecessorLinearMap p N) := by
  intro x y hxy
  apply Subtype.ext
  apply (euclideanCenteredZeroExtend (Nat.le_succ N)).injective
  exact congrArg Subtype.val hxy

/-- The exact centered predecessor image, now internal to the successor parity
Hilbert space. -/
def parityEmbeddedPredecessorSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (euclideanParityBoundaryFlatSubspace p (N + 1)) :=
  LinearMap.range (parityEmbeddedPredecessorLinearMap p N)

theorem finrank_parityEmbeddedPredecessorSubspace
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (parityEmbeddedPredecessorSubspace p N) = N - 1 := by
  let f := parityEmbeddedPredecessorLinearMap p N
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (parityEmbeddedPredecessorLinearMap_injective p N)
  have hdim := f.finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero] at hdim
  change Module.finrank ℂ (LinearMap.range f) = N - 1
  rw [hdim]
  exact finrank_euclideanParityBoundaryFlatSubspace p N hN

/-- Intrinsic one-step parity shell inside the successor parity subtype. -/
def intrinsicParitySuccShell
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (euclideanParityBoundaryFlatSubspace p (N + 1)) :=
  Submodule.orthogonal (𝕜 := ℂ) (parityEmbeddedPredecessorSubspace p N)

/-- Orthogonal projection onto the intrinsic one-step parity shell, with the
complex scalar fixed explicitly to avoid ambiguous RCLike inference on the
parity subtype. -/
def intrinsicParitySuccProjection
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p (N + 1) →L[ℂ]
      intrinsicParitySuccShell p N :=
  (intrinsicParitySuccShell p N).orthogonalProjectionOnto

theorem finrank_intrinsicParitySuccShell
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (intrinsicParitySuccShell p N) = 1 := by
  have hdim :=
    Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ)
      (parityEmbeddedPredecessorSubspace p N)
  rw [finrank_parityEmbeddedPredecessorSubspace p N hN,
    finrank_euclideanParityBoundaryFlatSubspace p (N + 1) (by omega)] at hdim
  change
    N - 1 + Module.finrank ℂ (intrinsicParitySuccShell p N) =
      N + 1 - 1 at hdim
  omega

/-- #107's ambient "not inherited" statement is exactly non-membership in the
intrinsic predecessor range. -/
theorem not_mem_parityEmbeddedPredecessorSubspace_of_not_centeredImage
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hnot :
      ¬ ∃ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N ∧
        euclideanCenteredZeroExtend (Nat.le_succ N) x =
          (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) :
    v ∉ parityEmbeddedPredecessorSubspace p N := by
  intro hv
  rcases hv with ⟨x, hx⟩
  apply hnot
  refine ⟨x, x.property, ?_⟩
  exact congrArg Subtype.val hx

/-- A vector outside the predecessor has a nonzero projection to the intrinsic
orthogonal successor shell. -/
theorem orthogonalProjection_intrinsicParitySuccShell_ne_zero_of_not_mem
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hv : v ∉ parityEmbeddedPredecessorSubspace p N) :
    intrinsicParitySuccProjection p N v ≠ 0 := by
  intro hproj
  have hvorth :
      v ∈ Submodule.orthogonal (𝕜 := ℂ) (intrinsicParitySuccShell p N) := by
    have hproj' :
        (intrinsicParitySuccShell p N).orthogonalProjectionOnto v = 0 := by
      exact hproj
    exact
      ((intrinsicParitySuccShell p N).orthogonalProjectionOnto_eq_zero_iff).mp
        hproj'
  have hvpred : v ∈ parityEmbeddedPredecessorSubspace p N := by
    simpa [intrinsicParitySuccShell] using hvorth
  exact hv hvpred

/-- Direct shell-projection form of the #107 non-inheritance theorem. -/
theorem negative_eigenmode_intrinsicShell_projection_ne_zero
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
    intrinsicParitySuccProjection p N v ≠ 0 := by
  apply orthogonalProjection_intrinsicParitySuccShell_ne_zero_of_not_mem
  apply not_mem_parityEmbeddedPredecessorSubspace_of_not_centeredImage
  exact negative_eigenmode_not_centeredImage
    p hL N hprev hlam hvne hveig

/-- Predecessor nonnegativity, expressed directly on the successor compressed
operator and the intrinsic predecessor subspace. -/
theorem re_inner_parityCompressedCanonical_nonnegative_on_predecessor
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (w : parityEmbeddedPredecessorSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ
        (parityCompressedCanonical p L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  rcases w.property with ⟨x, hx⟩
  rw [re_inner_parityCompressedCanonical_self]
  have hnonneg :=
    re_inner_successor_nonnegative_on_centeredImage
      p hL N hprev
      (x : EuclideanSpace ℂ (Fin (2 * N + 1))) x.property
  rw [← congrArg Subtype.val hx]
  exact hnonneg

end Zeta23.CCM

#print axioms Zeta23.CCM.finrank_parityEmbeddedPredecessorSubspace
#print axioms Zeta23.CCM.finrank_intrinsicParitySuccShell
#print axioms Zeta23.CCM.negative_eigenmode_intrinsicShell_projection_ne_zero
#print axioms Zeta23.CCM.re_inner_parityCompressedCanonical_nonnegative_on_predecessor
