import Zeta23.OPICARound4.NativeVisibility

noncomputable section
namespace Zeta23.OPICARound4
open CCM

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Under the full selfadjoint rank-one transport hypotheses a zero projected
pairing comes from input or output invisibility. A third cancellation mechanism
is possible for general cross observations, but is excluded here by semisimplicity. -/
theorem rank_one_kernel_pairing_rigidity (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (hc : f (D.symm (B.ker.starProjection g)) = 0) :
    B.ker.starProjection g = 0 ∨
      (f.comp D.symm.toLinearMap).comp B.ker.starProjection.toLinearMap = 0 := by
  by_cases hq : B.ker.starProjection g = 0
  · exact Or.inl hq
  right
  apply LinearMap.ext
  intro z
  change f (D.symm (B.ker.starProjection z)) = 0
  by_contra hz
  let R : Submodule ℂ F := (D.toLinearMap.comp A).range
  have hp (v : F) : B (B.ker.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (B.ker.starProjection_apply_mem v)
  have hg : g ∈ R := by
    have hh := hrank (D.symm (B.ker.starProjection z))
    rw [D.apply_symm_apply, hp] at hh
    have hD : D (A (D.symm (B.ker.starProjection z))) =
        -(f (D.symm (B.ker.starProjection z))) • g := by
      have hh' := congrArg (fun v : F => -v) hh
      simpa only [zero_sub, neg_neg, ← neg_smul] using hh'
    refine ⟨(-(f (D.symm (B.ker.starProjection z))))⁻¹ •
      D.symm (B.ker.starProjection z), ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, hD, smul_smul,
      inv_mul_cancel₀ (neg_ne_zero.mpr hz), one_smul]
  have hBrange : B.range ≤ R := by
    rintro _ ⟨v, rfl⟩
    have hh := hrank (D.symm v)
    rw [D.apply_symm_apply] at hh
    have he : B v = D (A (D.symm v)) + f (D.symm v) • g := by
      exact (sub_eq_iff_eq_add').mp hh
    rw [he]
    exact R.add_mem ⟨D.symm v, rfl⟩ (R.smul_mem _ hg)
  have horth : B.kerᗮ = B.range := by
    rw [← hB.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hv : g - B.ker.starProjection g ∈ B.range := by
    rw [← horth]
    exact B.ker.sub_starProjection_mem_orthogonal g
  have hqr : B.ker.starProjection g ∈ R := by
    have hh := R.sub_mem hg (hBrange hv)
    simpa only [sub_sub_cancel] using hh
  obtain ⟨t, ht⟩ := hqr
  have hta : A t = D.symm (B.ker.starProjection g) := by
    apply D.injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, D.apply_symm_apply] using ht
  have hka : A (D.symm (B.ker.starProjection g)) = 0 := by
    have hh := hrank (D.symm (B.ker.starProjection g))
    rw [D.apply_symm_apply, hp, hc, zero_smul, zero_sub] at hh
    apply D.injective
    simpa using neg_eq_zero.mp hh
  have hi := hA t (D.symm (B.ker.starProjection g))
  rw [hta, hka, inner_zero_right] at hi
  have hzero := (inner_self_eq_zero (𝕜 := ℂ)).mp hi
  apply hq
  have hh := congrArg D hzero
  simpa only [D.apply_symm_apply, map_zero] using hh

/-- The canonical whole-eigenspace projector is the ordinary star projection. -/
theorem groupedSpectralProjector_eq_starProjection {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (β : GroupedSpectrum B) :
    groupedSpectralProjector hB β =
      (Module.End.eigenspace B (β : ℂ)).starProjection.toLinearMap := by
  rfl

/-- Pure grouped cancellation with both sides visible would create a Jordan
chain, which similarity to the selfadjoint A excludes. -/
theorem grouped_zero_coefficient_rigidity {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (β : GroupedSpectrum B) (hc : groupedSpectralCoefficient hB D g f β = 0) :
    GroupedInputInvisible hB g β ∨ GroupedOutputInvisible hB D f β := by
  let b := groupedEigenvalue hB β
  let A₀ := A - (b : ℂ) • LinearMap.id
  let B₀ := B - (b : ℂ) • LinearMap.id
  have hA₀ : A₀.IsSymmetric :=
    hA.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  have hB₀ : B₀.IsSymmetric :=
    hB.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  have hker : B₀.ker = Module.End.eigenspace B (β : ℂ) := by
    rw [Module.End.eigenspace_def]
    change (B - (groupedEigenvalue hB β : ℂ) • LinearMap.id).ker = _
    rw [groupedEigenvalue_cast]
    rfl
  have hp : B₀.ker.starProjection.toLinearMap = groupedSpectralProjector hB β := by
    rw [hker, groupedSpectralProjector_eq_starProjection]
  have hc₀ : f (D.symm (B₀.ker.starProjection g)) = 0 := by
    change f (D.symm (B₀.ker.starProjection.toLinearMap g)) = 0
    rw [hp]
    exact hc
  have hh := rank_one_kernel_pairing_rigidity A₀ B₀ hA₀ hB₀ D g f
    (hrank.shift (b : ℂ)) hc₀
  rcases hh with hin | hout
  · left
    change groupedSpectralProjector hB β g = 0
    rw [← hp]
    exact hin
  · right
    change (f.comp D.symm.toLinearMap).comp (groupedSpectralProjector hB β) = 0
    rw [← hp]
    exact hout

/-- Exact zero-mass classification under the full Hermitian transport model.
It does not exclude either input or output invisible shared eigenmodes. -/
theorem grouped_residue_zero_iff_input_or_output_invisible
    {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (β : GroupedSpectrum B) :
    groupedSignedResidue hB D g f β = 0 ↔
      GroupedInputInvisible hB g β ∨ GroupedOutputInvisible hB D f β := by
  constructor
  · intro hc
    exact grouped_zero_coefficient_rigidity hA hB D g f hrank β
      ((grouped_residue_zero_iff_pairing_zero hA hB D g f hrank β).mp hc)
  · exact grouped_invisible_residue_zero hB D g f β

end Zeta23.OPICARound4

#print axioms Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity
#print axioms Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible
