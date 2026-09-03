import Zeta23.CCM.ConstrainedParitySpectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-A: predecessor image and the existing parity shell

The project already has the exact ambient successor geometry:
`euclideanParityEmbeddedSuccSubspace p N` is the centered predecessor image,
`euclideanParitySuccShell p N` is its orthogonal complement inside the
successor parity sector, and #105 proved that shell has complex finrank one.

This module connects #107's negative first-bad eigenmode to that existing shell.
In particular, "not inherited from the predecessor" is upgraded to a nonzero
orthogonal projection onto the already-proved one-dimensional shell.

Keeping the shell in the ambient Euclidean space avoids any artificial
inner-product instance choices on the constrained subtype.

No shell invariance, negative-index theorem, KKT equation, Schur/Feshbach
formula, positivity theorem, finite-to-infinite theorem, or RH theorem is
claimed here.
-/

/-- Orthogonal projection onto the already-proved ambient one-step parity
shell. -/
def paritySuccShellProjection
    (p : ReversalParity) (N : ℕ) :
    EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) →L[ℂ]
      euclideanParitySuccShell p N :=
  (euclideanParitySuccShell p N).orthogonalProjectionOnto

/-- #107's "not a centered predecessor image" is exactly non-membership in the
ambient predecessor image already used to define the #105 successor shell. -/
theorem not_mem_euclideanParityEmbeddedSuccSubspace_of_not_centeredImage
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hnot :
      ¬ ∃ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N ∧
        euclideanCenteredZeroExtend (Nat.le_succ N) x =
          (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) :
    (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∉
      euclideanParityEmbeddedSuccSubspace p N := by
  intro hv
  rcases hv with ⟨x, hx, hxv⟩
  exact hnot ⟨x, hx, hxv⟩

/-- In the successor parity sector, a vector outside the centered predecessor
image must have a nonzero orthogonal projection onto the existing successor
shell.

This is the precise ambient-space form of "the first-bad mode genuinely uses
the one new parity direction." -/
theorem paritySuccShellProjection_ne_zero_of_not_embedded
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvnot :
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∉
        euclideanParityEmbeddedSuccSubspace p N) :
    paritySuccShellProjection p N
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ≠ 0 := by
  intro hproj
  let W := euclideanParityEmbeddedSuccSubspace p N
  let V := euclideanParityBoundaryFlatSubspace p (N + 1)
  let S := euclideanParitySuccShell p N
  have hvorth :
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈ Sᗮ := by
    have hproj' : S.orthogonalProjectionOnto
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0 := by
      exact hproj
    exact (S.orthogonalProjectionOnto_eq_zero_iff).mp hproj'
  have hspan : W ⊔ S = V := by
    dsimp [W, S, V]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (euclideanParityEmbeddedSuccSubspace_le p N)
  have hvSup :
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈ W ⊔ S := by
    rw [hspan]
    exact v.property
  rw [Submodule.mem_sup] at hvSup
  rcases hvSup with ⟨w, hw, s, hs, hws⟩
  have hworth : w ∈ Sᗮ := by
    rw [S.mem_orthogonal]
    intro t ht
    have htWorth : t ∈ Wᗮ := by
      exact ht.1
    exact Submodule.inner_left_of_mem_orthogonal hw htWorth
  have hsorth : s ∈ Sᗮ := by
    have hsub :
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) - w ∈ Sᗮ :=
      Sᗮ.sub_mem hvorth hworth
    have hsEq :
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) - w = s := by
      rw [← hws]
      abel
    rwa [hsEq] at hsub
  have hss : inner ℂ s s = 0 :=
    (S.mem_orthogonal s).mp hsorth s hs
  have hs0 : s = 0 := (inner_self_eq_zero).mp hss
  have hwv :
      w = (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
    rw [← hws, hs0, add_zero]
  apply hvnot
  rw [← hwv]
  exact hw

/-- Direct shell-projection form of #107's negative-eigenmode
non-inheritance theorem. -/
theorem negative_eigenmode_paritySuccShell_projection_ne_zero
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
    paritySuccShellProjection p N
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ≠ 0 := by
  apply paritySuccShellProjection_ne_zero_of_not_embedded
  apply not_mem_euclideanParityEmbeddedSuccSubspace_of_not_centeredImage
  exact negative_eigenmode_not_centeredImage
    p hL N hprev hlam hvne hveig

/-- Exact N-flow keeps the successor canonical quadratic form nonnegative on
the ambient centered predecessor image. -/
theorem re_inner_successor_nonnegative_on_embeddedPredecessor
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (w : euclideanParityEmbeddedSuccSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ
        ((canonicalSourceMatrix L (N + 1)).toEuclideanLin
          (w : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
        (w : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) := by
  rcases w.property with ⟨x, hx, hxw⟩
  have hnonneg :=
    re_inner_successor_nonnegative_on_centeredImage
      p hL N hprev x hx
  rw [hxw] at hnonneg
  exact hnonneg

end Zeta23.CCM

#print axioms Zeta23.CCM.paritySuccShellProjection_ne_zero_of_not_embedded
#print axioms Zeta23.CCM.negative_eigenmode_paritySuccShell_projection_ne_zero
#print axioms Zeta23.CCM.re_inner_successor_nonnegative_on_embeddedPredecessor
