import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Singular-safe native tie compatibility with the full kernel component.

The shifted odd operator is the actual native operator at `lam`. Its kernel
may have arbitrary multiplicity. The source range witness comes directly
from the actual rank-one identity and actual even eigenmode. No strict
resolvent or complementary inverse is used without a range theorem.
-/

def poleNeutralOddShiftedKernelProjection (L : ℝ) (K : ℕ) (lam : ℝ) :
    poleNeutralOddSubspace L K →L[ℂ]
      LinearMap.ker (poleNeutralOddShiftedCanonical L K lam) :=
  Submodule.orthogonalProjectionOnto (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
    (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam))

theorem poleNeutralOddShiftedCanonical_isSymmetric (L : ℝ) (K : ℕ) (lam : ℝ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddShiftedCanonical L K lam) :=
  (poleNeutralOddCompressedCanonical_isSymmetric L K).sub
    (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)

/-- Every actual shifted output is orthogonal to its actual shifted kernel. -/
theorem poleNeutralOddShifted_output_mem_kernel_orthogonal (L : ℝ) (K : ℕ) (lam : ℝ)
    (w : poleNeutralOddSubspace L K) :
    poleNeutralOddShiftedCanonical L K lam w ∈
      (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam))ᗮ := by
  intro v hv
  have hz := LinearMap.mem_ker.mp hv
  rw [← poleNeutralOddShiftedCanonical_isSymmetric L K lam v w, hz, inner_zero_left]

theorem poleNeutralOddShiftedKernelProjection_apply_output_eq_zero (L : ℝ)
    (K : ℕ) (lam : ℝ) (w : poleNeutralOddSubspace L K) :
    poleNeutralOddShiftedKernelProjection L K lam (poleNeutralOddShiftedCanonical L K lam w) = 0 := by
  apply (Submodule.orthogonalProjectionOnto_eq_zero_iff
    (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
    (K := LinearMap.ker (poleNeutralOddShiftedCanonical L K lam))).mpr
  exact poleNeutralOddShifted_output_mem_kernel_orthogonal L K lam w

/-- An actual even eigenmode supplies the range witness before any inverse. -/
theorem poleNeutral_even_eigen_source_mem_odd_shifted_range {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K ∈
      LinearMap.range (poleNeutralOddShiftedCanonical L K lam) := by
  have hr := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
  have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
    simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  rw [ha, map_zero, sub_zero] at hr
  exact ⟨poleNeutralIndexLinearMap hL K u, hr⟩

/-- Native kernel compatibility, with arbitrary odd-kernel multiplicity. -/
theorem poleNeutral_even_eigen_shifted_kernel_compatibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u •
      poleNeutralOddShiftedKernelProjection L K lam (poleNeutralCubicCompressionVector L K) = 0 := by
  have hr := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
  have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
    simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  rw [ha, map_zero, sub_zero] at hr
  have hp := congrArg (poleNeutralOddShiftedKernelProjection L K lam) hr
  rw [poleNeutralOddShiftedKernelProjection_apply_output_eq_zero, map_smul] at hp
  exact hp.symm

def poleNeutralEvenEigen_indexKernelComponent {L : ℝ} (hL : 0 < L) (K : ℕ) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) : LinearMap.ker (poleNeutralOddShiftedCanonical L K lam) :=
  poleNeutralOddShiftedKernelProjection L K lam (poleNeutralIndexLinearMap hL K u)

def poleNeutralEvenEigen_indexComplementComponent {L : ℝ} (hL : 0 < L) (K : ℕ) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) : poleNeutralOddSubspace L K :=
  poleNeutralIndexLinearMap hL K u - (poleNeutralEvenEigen_indexKernelComponent hL K lam u).val

/-- Preserve the full shifted-kernel component of the actual index image. -/
theorem poleNeutralEvenEigen_index_eq_kernel_add_complement {L : ℝ} (hL : 0 < L)
    (K : ℕ) (lam : ℝ) (u : poleNeutralEvenSubspace L K) :
    poleNeutralIndexLinearMap hL K u =
      (poleNeutralEvenEigen_indexKernelComponent hL K lam u).val +
        poleNeutralEvenEigen_indexComplementComponent hL K lam u := by
  unfold poleNeutralEvenEigen_indexComplementComponent
  abel

theorem poleNeutralEvenEigen_indexComplement_mem_kernel_orthogonal {L : ℝ} (hL : 0 < L)
    (K : ℕ) (lam : ℝ) (u : poleNeutralEvenSubspace L K) :
    poleNeutralEvenEigen_indexComplementComponent hL K lam u ∈
      (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam))ᗮ := by
  rw [poleNeutralEvenEigen_indexComplementComponent, poleNeutralEvenEigen_indexKernelComponent,
    poleNeutralOddShiftedKernelProjection, Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.sub_starProjection_mem_orthogonal
    (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
    (K := LinearMap.ker (poleNeutralOddShiftedCanonical L K lam)) (poleNeutralIndexLinearMap hL K u)

/-- The actual complement solves the same source equation; the retained
kernel component is annihilated by the actual shifted operator. -/
theorem poleNeutral_even_eigen_complement_source_eq {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralOddShiftedCanonical L K lam (poleNeutralEvenEigen_indexComplementComponent hL K lam u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
  have hr := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
  have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
    simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  rw [ha, map_zero, sub_zero] at hr
  have hz := LinearMap.mem_ker.mp (poleNeutralEvenEigen_indexKernelComponent hL K lam u).property
  rw [poleNeutralEvenEigen_indexComplementComponent, map_sub, hz, sub_zero]
  exact hr

/-- A native tied bottom retains all kernel components and supplies the
source compatibility and actual range condition. No simplicity is required. -/
theorem poleNeutral_tied_ground_singular_safe_package {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK) :
    ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u = (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u ∧
      poleNeutralCorrectedCubicSource L K u •
        poleNeutralOddShiftedKernelProjection L K (poleNeutralOddRayleighBottom L K hL hK)
          (poleNeutralCubicCompressionVector L K) = 0 ∧
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K ∈
        LinearMap.range (poleNeutralOddShiftedCanonical L K (poleNeutralOddRayleighBottom L K hL hK)) := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  refine ⟨u, hu0, hu, ?_, ?_⟩
  · rw [← htie]
    exact poleNeutral_even_eigen_shifted_kernel_compatibility hL K hK _ u hu
  · rw [← htie]
    exact poleNeutral_even_eigen_source_mem_odd_shifted_range hL K hK _ u hu

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutralOddShifted_output_mem_kernel_orthogonal
#print axioms Zeta23.CCM.poleNeutral_even_eigen_source_mem_odd_shifted_range
#print axioms Zeta23.CCM.poleNeutral_even_eigen_shifted_kernel_compatibility
#print axioms Zeta23.CCM.poleNeutralEvenEigen_index_eq_kernel_add_complement
#print axioms Zeta23.CCM.poleNeutralEvenEigen_indexComplement_mem_kernel_orthogonal
#print axioms Zeta23.CCM.poleNeutral_even_eigen_complement_source_eq
#print axioms Zeta23.CCM.poleNeutral_tied_ground_singular_safe_package
