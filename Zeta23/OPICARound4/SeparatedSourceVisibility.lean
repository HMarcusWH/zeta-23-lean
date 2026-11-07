import Zeta23.OPICARound4.NativeVisibility
import Zeta23.OPICARound4.NativeWitnessCosts

noncomputable section
namespace Zeta23.OPICARound4
open CCM Module.End

private theorem source_visible_of_disjoint_rank_one
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (hsep : ∀ mu : ℂ, HasEigenvalue A mu → ¬ HasEigenvalue B mu)
    (mu : ℂ) (u : E) (hu0 : u ≠ 0) (hu : A u = mu • u) : f u ≠ 0 := by
  rcases rank_one_visible_or_shared_mode A B D g f hrank mu u hu0 hu with h | ⟨v,hv0,hv,_⟩
  · exact h
  · exact False.elim (hsep mu
      (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hu,hu0⟩)
      (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hv,hv0⟩))

private theorem reciprocal_source_visible_of_disjoint_rank_one
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (hsep : ∀ mu : ℂ, HasEigenvalue A mu → ¬ HasEigenvalue B mu)
    (mu : ℂ) (w : F) (hw0 : w ≠ 0) (hw : B w = mu • w) : f (D.symm w) ≠ 0 := by
  intro hf
  have hv0 : D.symm w ≠ 0 := by
    intro h
    apply hw0
    simpa only [D.apply_symm_apply,map_zero] using congrArg D h
  have hv : A (D.symm w) = mu • D.symm w := by
    apply D.injective
    have h := hrank (D.symm w)
    rw [D.apply_symm_apply,hf,zero_smul,hw] at h
    rw [map_smul,D.apply_symm_apply]
    exact (sub_eq_zero.mp h).symm
  exact hsep mu (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hv,hv0⟩)
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hw,hw0⟩)

private theorem eigenspace_finrank_le_one_of_every_mode_visible
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (f : E →ₗ[ℂ] ℂ) (mu : ℂ)
    (hvis : ∀ u : E, u ≠ 0 → A u = mu • u → f u ≠ 0) :
    Module.finrank ℂ (eigenspace A mu) ≤ 1 := by
  let q := f.comp (eigenspace A mu).subtype
  have hi : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro u hu
    by_contra h
    have hu0 : (u : E) ≠ 0 := fun e => h (Subtype.ext e)
    exact hvis u hu0 (mem_eigenspace_iff.mp u.property) hu
  simpa using q.finrank_le_finrank_of_injective hi

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Complete spectral separation excludes source silence in either native channel.
The corrected even source and the inverse-adjoint cubic test remain distinct. -/
theorem separated_native_even_eigen_channels_visible {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →
      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu)
    (mu : ℂ) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = mu • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralCubicPairingFunctional L K ((poleNeutralIndexAdjointEquiv hL K hK).symm u) ≠ 0 := by
  refine ⟨?_,?_⟩
  · exact source_visible_of_disjoint_rank_one _ _
      (poleNeutralIndexEquiv hL K (by omega)) _ _
      (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) hsep mu u hu0 hu
  · exact reciprocal_source_visible_of_disjoint_rank_one _ _
      (poleNeutralIndexAdjointEquiv hL K hK) _ _
      (native_odd_rank_one_unshifted hL K hK)
      (fun z hz ho => hsep z ho hz) mu u hu0 hu

theorem separated_native_odd_eigen_channels_visible {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →
      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu)
    (mu : ℂ) (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = mu • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 ∧
      poleNeutralCorrectedCubicSource L K ((poleNeutralIndexEquiv hL K (by omega)).symm w) ≠ 0 := by
  refine ⟨?_,?_⟩
  · exact source_visible_of_disjoint_rank_one _ _
      (poleNeutralIndexAdjointEquiv hL K hK) _ _
      (native_odd_rank_one_unshifted hL K hK)
      (fun z hz ho => hsep z ho hz) mu w hw0 hw
  · exact reciprocal_source_visible_of_disjoint_rank_one _ _
      (poleNeutralIndexEquiv hL K (by omega)) _ _
      (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) hsep mu w hw0 hw

/-- The whole eigenspace is retained; its dimension bound follows from an
injective scalar source functional. No sign or quantitative source lower bound is asserted. -/
theorem separated_native_even_eigenspace_finrank_le_one {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →
      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu) (mu : ℂ) :
    Module.finrank ℂ (eigenspace (poleNeutralEvenCompressedCanonical L K) mu) ≤ 1 := by
  apply eigenspace_finrank_le_one_of_every_mode_visible _ (poleNeutralCorrectedCubicFunctional L K)
  intro u hu0 hu
  exact (separated_native_even_eigen_channels_visible hL K hK hsep mu u hu0 hu).1

theorem separated_native_odd_eigenspace_finrank_le_one {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →
      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu) (mu : ℂ) :
    Module.finrank ℂ (eigenspace (poleNeutralOddCompressedCanonical L K) mu) ≤ 1 := by
  apply eigenspace_finrank_le_one_of_every_mode_visible _ (poleNeutralCubicPairingFunctional L K)
  intro w hw0 hw
  exact (separated_native_odd_eigen_channels_visible hL K hK hsep mu w hw0 hw).1

end Zeta23.OPICARound4
