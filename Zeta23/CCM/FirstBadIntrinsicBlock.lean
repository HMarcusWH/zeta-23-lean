import Zeta23.CCM.FirstBadRigidity
import Zeta23.CCM.GlobalFirstBad
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-D1: intrinsic predecessor / shell block

The #105/#109 shell lives in the ambient Euclidean coefficient space.  This
module internalizes both the centered predecessor image and its already-proved
ambient orthogonal-intersection shell as submodules of the exact successor
parity-constrained subtype.  The resulting native shell is linearly equivalent
to the ambient shell and therefore has complex dimension one.

No shell invariance, Schur/Feshbach formula, negative-index theorem,
positivity theorem, finite-to-infinite theorem, or RH theorem is claimed.
-/

/-- Centered predecessor image, now regarded natively inside the successor
parity-constrained Euclidean subtype. -/
def intrinsicParityPredecessorSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (euclideanParityBoundaryFlatSubspace p (N + 1)) :=
  (euclideanParityEmbeddedSuccSubspace p N).comap
    (euclideanParityBoundaryFlatSubspace p (N + 1)).subtype

@[simp] theorem mem_intrinsicParityPredecessorSubspace_iff
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    v ∈ intrinsicParityPredecessorSubspace p N ↔
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace p N := Iff.rfl

/-- The intrinsic predecessor is linearly equivalent to the already-proved
ambient predecessor image. -/
def intrinsicParityPredecessorEquivAmbient
    (p : ReversalParity) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N ≃ₗ[ℂ]
      euclideanParityEmbeddedSuccSubspace p N where
  toFun := fun v =>
    ⟨((v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))), v.property⟩
  invFun := fun w =>
    ⟨⟨(w : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))),
        euclideanParityEmbeddedSuccSubspace_le p N w.property⟩,
      w.property⟩
  left_inv := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    rfl

/-- The intrinsic predecessor has exactly the predecessor parity dimension. -/
theorem finrank_intrinsicParityPredecessorSubspace
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (intrinsicParityPredecessorSubspace p N) = N - 1 := by
  calc
    Module.finrank ℂ (intrinsicParityPredecessorSubspace p N) =
        Module.finrank ℂ (euclideanParityEmbeddedSuccSubspace p N) :=
      (intrinsicParityPredecessorEquivAmbient p N).finrank_eq
    _ = N - 1 := finrank_euclideanParityEmbeddedSuccSubspace p N hN

/-- Native one-step shell inside the successor parity-constrained carrier.
It is the pullback of the already-proved ambient shell
`Wᗮ ⊓ V` along the successor subtype inclusion. -/
def intrinsicParitySuccShell
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (euclideanParityBoundaryFlatSubspace p (N + 1)) :=
  (euclideanParitySuccShell p N).comap
    (euclideanParityBoundaryFlatSubspace p (N + 1)).subtype

@[simp] theorem mem_intrinsicParitySuccShell_iff
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    v ∈ intrinsicParitySuccShell p N ↔
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParitySuccShell p N := Iff.rfl

/-- The native shell is linearly equivalent to the ambient one-step shell. -/
def intrinsicParitySuccShellEquivAmbient
    (p : ReversalParity) (N : ℕ) :
    intrinsicParitySuccShell p N ≃ₗ[ℂ] euclideanParitySuccShell p N where
  toFun := fun s =>
    ⟨((s : euclideanParityBoundaryFlatSubspace p (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))), s.property⟩
  invFun := fun s =>
    ⟨⟨(s : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))), by
        have hs := s.property
        change
          (s : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
            (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
              euclideanParityBoundaryFlatSubspace p (N + 1) at hs
        exact hs.2⟩,
      s.property⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    rfl

/-- The native successor shell is exactly one complex dimension. -/
theorem finrank_intrinsicParitySuccShell
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (intrinsicParitySuccShell p N) = 1 := by
  calc
    Module.finrank ℂ (intrinsicParitySuccShell p N) =
        Module.finrank ℂ (euclideanParitySuccShell p N) :=
      (intrinsicParitySuccShellEquivAmbient p N).finrank_eq
    _ = 1 := finrank_euclideanParitySuccShell p N hN

/-- The intrinsic predecessor plus its native orthogonal shell spans the full
successor parity carrier.  The proof is transported through the ambient
identity `W ⊔ (Wᗮ ⊓ V) = V`, avoiding any subtype-inner-product inference. -/
theorem intrinsicPredecessor_sup_shell
    (p : ReversalParity) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N ⊔
      intrinsicParitySuccShell p N = ⊤ := by
  apply top_unique
  intro v _hv
  have hspan :
      euclideanParityEmbeddedSuccSubspace p N ⊔
          euclideanParitySuccShell p N =
        euclideanParityBoundaryFlatSubspace p (N + 1) := by
    change
      euclideanParityEmbeddedSuccSubspace p N ⊔
          ((euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
        euclideanParityBoundaryFlatSubspace p (N + 1)
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (euclideanParityEmbeddedSuccSubspace_le p N)
  have hvAmbient :
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace p N ⊔
          euclideanParitySuccShell p N := by
    rw [hspan]
    exact v.property
  rw [Submodule.mem_sup] at hvAmbient
  rcases hvAmbient with ⟨w, hw, s, hs, hws⟩
  have hsCarrier :
      s ∈ euclideanParityBoundaryFlatSubspace p (N + 1) := by
    have hs' := hs
    change
      s ∈ (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace p (N + 1) at hs'
    exact hs'.2
  let wV : euclideanParityBoundaryFlatSubspace p (N + 1) :=
    ⟨w, euclideanParityEmbeddedSuccSubspace_le p N hw⟩
  let sV : euclideanParityBoundaryFlatSubspace p (N + 1) :=
    ⟨s, hsCarrier⟩
  have hwV : wV ∈ intrinsicParityPredecessorSubspace p N := by
    exact hw
  have hsV : sV ∈ intrinsicParitySuccShell p N := by
    exact hs
  rw [Submodule.mem_sup]
  refine ⟨wV, hwV, sV, hsV, ?_⟩
  apply Subtype.ext
  exact hws

/-- Every successor constrained vector decomposes as predecessor plus an
orthogonal-shell vector. -/
theorem exists_intrinsicPredecessor_add_shell
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    ∃ w : intrinsicParityPredecessorSubspace p N,
      ∃ s : intrinsicParitySuccShell p N,
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) = v := by
  have hv :
      v ∈ intrinsicParityPredecessorSubspace p N ⊔
        intrinsicParitySuccShell p N := by
    rw [intrinsicPredecessor_sup_shell p N]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hv
  rcases hv with ⟨w, hw, s, hs, hws⟩
  exact ⟨⟨w, hw⟩, ⟨s, hs⟩, hws⟩

/-- A vector outside the intrinsic predecessor necessarily has a nonzero shell
component in every predecessor-plus-shell decomposition. -/
theorem exists_intrinsicPredecessor_add_shell_ne_zero_of_not_mem
    (p : ReversalParity) (N : ℕ)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvnot : v ∉ intrinsicParityPredecessorSubspace p N) :
    ∃ w : intrinsicParityPredecessorSubspace p N,
      ∃ s : intrinsicParitySuccShell p N,
        s ≠ 0 ∧
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) = v := by
  obtain ⟨w, s, hws⟩ := exists_intrinsicPredecessor_add_shell p N v
  have hsne : s ≠ 0 := by
    intro hs0
    apply hvnot
    have hvw :
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = v := by
      simpa [hs0] using hws
    rw [← hvw]
    exact w.property
  exact ⟨w, s, hsne, hws⟩

/-- #107/#109's first-bad negative eigenmode therefore admits a native block
decomposition with a genuinely nonzero one-dimensional shell component. -/
theorem negative_eigenmode_exists_intrinsic_shell_component
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
    ∃ w : intrinsicParityPredecessorSubspace p N,
      ∃ s : intrinsicParitySuccShell p N,
        s ≠ 0 ∧
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) = v := by
  have hnotCentered :=
    negative_eigenmode_not_centeredImage
      p hL N hprev hlam hvne hveig
  have hnotAmbient :=
    not_mem_euclideanParityEmbeddedSuccSubspace_of_not_centeredImage
      p N hnotCentered
  have hnotIntrinsic : v ∉ intrinsicParityPredecessorSubspace p N := by
    simpa only [mem_intrinsicParityPredecessorSubspace_iff] using hnotAmbient
  exact exists_intrinsicPredecessor_add_shell_ne_zero_of_not_mem
    p N hnotIntrinsic

end Zeta23.CCM

#print axioms Zeta23.CCM.finrank_intrinsicParityPredecessorSubspace
#print axioms Zeta23.CCM.finrank_intrinsicParitySuccShell
#print axioms Zeta23.CCM.intrinsicPredecessor_sup_shell
#print axioms Zeta23.CCM.exists_intrinsicPredecessor_add_shell_ne_zero_of_not_mem
#print axioms Zeta23.CCM.negative_eigenmode_exists_intrinsic_shell_component
