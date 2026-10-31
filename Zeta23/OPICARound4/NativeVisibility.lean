import Zeta23.OPICARound4.NativeSpectralMeasure

noncomputable section

namespace Zeta23.OPICARound4
open CCM

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The source vector misses this entire eigenspace. -/
def GroupedInputInvisible {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (g : F) (β : GroupedSpectrum B) : Prop := groupedSpectralProjector hB β g = 0

/-- The transported output functional vanishes on this entire eigenspace. -/
def GroupedOutputInvisible {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (f : E →ₗ[ℂ] ℂ) (β : GroupedSpectrum B) : Prop :=
  (f.comp D.symm.toLinearMap).comp (groupedSpectralProjector hB β) = 0

theorem grouped_input_invisible_coefficient_zero {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (β : GroupedSpectrum B) (h : GroupedInputInvisible hB g β) :
    groupedSpectralCoefficient hB D g f β = 0 := by
  simp only [groupedSpectralCoefficient, GroupedInputInvisible] at *
  rw [h, map_zero, map_zero]

theorem grouped_output_invisible_coefficient_zero {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (β : GroupedSpectrum B) (h : GroupedOutputInvisible hB D f β) :
    groupedSpectralCoefficient hB D g f β = 0 := by
  exact congrArg (fun k : F →ₗ[ℂ] ℂ => k g) h

theorem grouped_invisible_residue_zero {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (β : GroupedSpectrum B)
    (h : GroupedInputInvisible hB g β ∨ GroupedOutputInvisible hB D f β) :
    groupedSignedResidue hB D g f β = 0 := by
  have hc : groupedSpectralCoefficient hB D g f β = 0 := by
    rcases h with h | h
    · exact grouped_input_invisible_coefficient_zero hB D g f β h
    · exact grouped_output_invisible_coefficient_zero hB D g f β h
  simp only [groupedSignedResidue, hc, Complex.zero_re]

/-- Zero signed mass says that one exact grouped pairing vanishes. It does
not say that the eigenspace, source component, or output functional is absent. -/
theorem grouped_residue_zero_iff_pairing_zero {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (β : GroupedSpectrum B) :
    groupedSignedResidue hB D g f β = 0 ↔
      groupedSpectralCoefficient hB D g f β = 0 := by
  rw [← groupedSignedResidue_cast hA hB D g f hrank β]
  exact Complex.ofReal_eq_zero.symm

/-- An eigenvalue remains an eigenvalue when its source mass is zero. This
explicit zero-source specialization falsifies disappearance of an eigenspace
from a zero residue, including at repeated eigenvalues. -/
theorem zero_residue_does_not_remove_eigenspace {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F) (f : E →ₗ[ℂ] ℂ)
    (β : GroupedSpectrum B) :
    groupedSpectralCoefficient hB D 0 f β = 0 ∧
      Module.End.eigenspace B (β : ℂ) ≠ ⊥ := by
  constructor
  · simp [groupedSpectralCoefficient]
  · exact Module.End.hasEigenvalue_iff.mp β.property

/-- Source-invisible eigenmodes give exact shared modes under the actual
algebraic transfer. Invisibility never licenses deleting a shared mode. -/
theorem rank_one_visible_or_shared_mode {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (D : V ≃ₗ[ℂ] W) (g : W) (f : V →ₗ[ℂ] ℂ)
    (hrank : RankOneIntertwining A B D g f) (lam : ℂ)
    (u : V) (hu0 : u ≠ 0) (hu : A u = lam • u) :
    f u ≠ 0 ∨ ∃ v : W, v ≠ 0 ∧ B v = lam • v ∧ v = D u := by
  by_cases hf : f u = 0
  · right
    refine ⟨D u, ?_, ?_, rfl⟩
    · exact fun hz => hu0 (D.injective (by simpa using hz))
    · have hh := hrank u
      rw [hf, zero_smul, hu, map_smul] at hh
      exact sub_eq_zero.mp hh
  · exact Or.inl hf

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

theorem native_even_visible_or_shared_mode {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu0 : u ≠ 0) (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 ∨
      ∃ v : poleNeutralOddSubspace L K, v ≠ 0 ∧
        poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v ∧
        v = poleNeutralIndexEquiv hL K (by omega) u := by
  exact rank_one_visible_or_shared_mode
    (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
    (poleNeutralCorrectedCubicFunctional L K)
    (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) (lam : ℂ) u hu0 hu

theorem native_odd_visible_or_shared_mode {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralOddSubspace L K)
    (hu0 : u ≠ 0) (hu : poleNeutralOddCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCubicPairingFunctional L K u ≠ 0 ∨
      ∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
        poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v ∧
        v = poleNeutralIndexAdjointEquiv hL K hK u := by
  exact rank_one_visible_or_shared_mode
    (poleNeutralOddCompressedCanonical L K) (poleNeutralEvenCompressedCanonical L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K) (native_odd_rank_one_unshifted hL K hK)
    (lam : ℂ) u hu0 hu

end Zeta23.OPICARound4
