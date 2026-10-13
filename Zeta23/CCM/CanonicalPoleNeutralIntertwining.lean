import Zeta23.CCM.CanonicalPoleNeutralGeometry

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ComplexConjugate

-- Keep the standard inherited subtype metric transparent to the elaborator.
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The exact additional defect introduced by native pole-neutral compression.

The original legal parity defect is already a proved cubic rank-one source.
Further orthogonal compression contributes an actual output residual. The
identities below keep that residual explicit; no invariance or replacement of
the corrected source by the original legal source is assumed.

This supplies part of M08's source geometry. Reducing the final residual to the
paper's explicit scalar correction, and the accompanying normal and dimension
formulas, remain separate obligations.
-/

/-- Actual legal output removed by further even pole-neutral compression. -/
def poleNeutralEvenOutputResidual (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : euclideanEvenBoundaryFlatSubspace K :=
  evenCompressedCanonical L K u.val - (poleNeutralEvenCompressedCanonical L K u).val

theorem poleNeutralEvenOutputResidual_mem_orthogonal (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralEvenOutputResidual L K u ∈
      Submodule.orthogonal (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
        (poleNeutralEvenSubspace L K) := by
  change evenCompressedCanonical L K u.val -
    (poleNeutralEvenSubspace L K).starProjection (evenCompressedCanonical L K u.val) ∈ _
  exact (poleNeutralEvenSubspace L K).sub_starProjection_mem_orthogonal _

/-- The actual centered-index defect of the two further compressed blocks. -/
def poleNeutralCompressedIndexDefect {L : ℝ} (hL : 0 < L) (K : ℕ) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
  (poleNeutralOddCompressedCanonical L K).comp (poleNeutralIndexLinearMap hL K) -
    (poleNeutralIndexLinearMap hL K).comp (poleNeutralEvenCompressedCanonical L K)

/-- Projected legal cubic channel on the native odd pole-neutral carrier. -/
def poleNeutralCubicCompressionVector (L : ℝ) (K : ℕ) : poleNeutralOddSubspace L K :=
  (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
    (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
      (oddCubicCompressionVector K)

/-- Exact additional-compression identity. In particular, dropping the second
term would require a new theorem about the removed actual even output. -/
theorem poleNeutralCompressedIndexDefect_eq_projected_legal_add_residual
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCompressedIndexDefect hL K u =
      (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
        (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
          (evenOddCompressedIntertwiningDefect L K u.val) +
      (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
        (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
          (euclideanEvenToOddIndexLinearMap K (poleNeutralEvenOutputResidual L K u)) := by
  let Q : euclideanOddBoundaryFlatSubspace K →L[ℂ] poleNeutralOddSubspace L K :=
    Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K)
  let D := euclideanEvenToOddIndexLinearMap K
  let A := evenCompressedCanonical L K
  let B := oddCompressedCanonical L K
  have hkeep : Q (D (poleNeutralEvenCompressedCanonical L K u).val) =
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) := by
    change Q ((poleNeutralIndexLinearMap hL K
      (poleNeutralEvenCompressedCanonical L K u)).val) = _
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
      (K := poleNeutralOddSubspace L K) _
  change Q (B (D u.val)) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) =
      Q (B (D u.val) - D (A u.val)) +
        Q (D (A u.val - (poleNeutralEvenCompressedCanonical L K u).val))
  simp only [map_sub]
  rw [hkeep]
  abel

/-- The first term is the native legal source, exactly as already proved;
the extra neutral-compression residual is retained with its required plus sign. -/
theorem poleNeutralCompressedIndexDefect_eq_cubicSource_add_residual
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralCompressedIndexDefect hL K u =
      cubicDefectFunctional L K u.val • poleNeutralCubicCompressionVector L K +
      (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
        (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
          (euclideanEvenToOddIndexLinearMap K (poleNeutralEvenOutputResidual L K u)) := by
  rw [poleNeutralCompressedIndexDefect_eq_projected_legal_add_residual hL K u,
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul hL K hK u.val,
    map_smul]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutralEvenOutputResidual_mem_orthogonal
#print axioms Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_projected_legal_add_residual
#print axioms Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_cubicSource_add_residual
