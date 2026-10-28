import Zeta23.OPICARound4
import Zeta23.OPICARound4.Validation.Support

noncomputable section

namespace Zeta23.OPICARound4.Validation

open CCM OPICARound3 OPICARound4

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Independently stated Pythagoras consumer with the native shell subtype. -/
theorem physical_shell_norm_consumer
    (J : E →ₗᵢ[ℂ] F) (e : isometricDetectorComplement J) (x : E) :
    ‖(e : F) - J x‖ ^ 2 = ‖(e : F)‖ ^ 2 + ‖x‖ ^ 2 :=
  shell_sub_norm_sq J e x

/-- Independent statement-level consumer for the actual regular Schur response. -/
theorem regular_witness_norm_consumer
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :
    ‖regularSchurWitness J T e hb‖ ^ 2 =
      ‖(e : F)‖ ^ 2 +
        ‖kernelSafeResponse (predecessorBlock J T) _ hb‖ ^ 2 :=
  regular_witness_norm_sq J T e hb

/-- Independent statement-level consumer for the kernel-safe resonant cost. -/
theorem resonant_witness_norm_consumer
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J) :
    ‖resonantSchurWitness J T e‖ ^ 2 =
      ‖(e : F)‖ ^ 2 +
      ‖(resonantSchurCoefficient J T e : ℂ)‖ ^ 2 *
        ‖(predecessorBlock J T).ker.starProjection
          (J.toLinearMap.adjoint (T e.val))‖ ^ 2 :=
  resonant_witness_norm_sq J T e

/-- The negative Schur vector is not assumed to have unit norm. -/
theorem regular_witness_rayleigh_consumer
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (e : isometricDetectorComplement J) (he : ‖(e : F)‖ = 1)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :
    rayleighEnergy T (regularSchurWitness J T e hb) =
      oneShellSchurScalar J T e hb /
        (1 + ‖kernelSafeResponse (predecessorBlock J T) _ hb‖ ^ 2) :=
  regular_witness_rayleigh J T hT e he hb

/-- Energy -1 is divided by the full resonant witness norm. -/
theorem resonant_witness_rayleigh_consumer
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (e : isometricDetectorComplement J) (he : ‖(e : F)‖ = 1)
    (hz : (predecessorBlock J T).ker.starProjection
      (J.toLinearMap.adjoint (T e.val)) ≠ 0) :
    rayleighEnergy T (resonantSchurWitness J T e) =
      -1 / (1 + ‖(resonantSchurCoefficient J T e : ℂ)‖ ^ 2 *
        ‖(predecessorBlock J T).ker.starProjection
          (J.toLinearMap.adjoint (T e.val))‖ ^ 2) :=
  resonant_witness_rayleigh J T hT e he hz

/-- A common shift does not change the *relative* defect. -/
theorem common_scalar_shift_consumer
    {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup H] [Module ℂ H]
    (A : G →ₗ[ℂ] G) (B : H →ₗ[ℂ] H)
    (D : G →ₗ[ℂ] H) (c : ℂ) :
    (B - c • LinearMap.id).comp D -
        D.comp (A - c • LinearMap.id) = B.comp D - D.comp A :=
  common_scalar_shift_invariant A B D c

/-- This source-row invariance requires actual orthogonality. -/
theorem orthogonal_source_row_consumer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : H →ₗ[ℂ] H) (c : ℂ) (h u : H)
    (hu : inner ℂ h u = 0) :
    inner ℂ h ((M - c • (LinearMap.id : H →ₗ[ℂ] H)) u) = inner ℂ h (M u) :=
  orthogonal_source_row_shift M c h u hu

/-- The independent arithmetic premise remains visible in the exact type. -/
theorem even_source_bound_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (hbound : (poleNeutralCorrectedCubicSource L K
      (poleNeutralEvenShiftedRay hL K hK lam hlam)).re < 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    False :=
  no_even_eigen_from_independent_ray_bound hL K hK lam hlam hbound ⟨u, hu0, hu⟩

/-- Odd-adjoint input is not substitutable for the even source functional. -/
theorem odd_source_bound_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (hbound : (poleNeutralCubicPairingFunctional L K
      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re < 1)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    False :=
  no_odd_eigen_from_independent_ray_bound hL K hK lam hlam hbound ⟨w, hw0, hw⟩

end Zeta23.OPICARound4.Validation

#print axioms Zeta23.OPICARound4.shell_sub_norm_sq
#print axioms Zeta23.OPICARound4.regular_witness_norm_sq
#print axioms Zeta23.OPICARound4.resonant_witness_norm_sq
#print axioms Zeta23.OPICARound4.regular_witness_rayleigh
#print axioms Zeta23.OPICARound4.resonant_witness_rayleigh
#print axioms Zeta23.OPICARound4.common_scalar_shift_invariant
#print axioms Zeta23.OPICARound4.orthogonal_source_row_shift
#print axioms Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound
#print axioms Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound
#print axioms Zeta23.OPICARound4.Validation.physical_shell_norm_consumer
#print axioms Zeta23.OPICARound4.Validation.even_source_bound_consumer
#print axioms Zeta23.OPICARound4.Validation.odd_source_bound_consumer
#print axioms Zeta23.OPICARound4.Validation.regular_witness_norm_consumer
#print axioms Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer
#print axioms Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer
#print axioms Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer
#print axioms Zeta23.OPICARound4.Validation.common_scalar_shift_consumer
#print axioms Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer

-- BEGIN ROUND4 COMPLETE DECLARATION AUDIT
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.even_absolute_energy_anchor"
#check @Zeta23.OPICARound4.even_absolute_energy_anchor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.even_absolute_energy_anchor"
#print axioms Zeta23.OPICARound4.even_absolute_energy_anchor
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.odd_absolute_energy_anchor"
#check @Zeta23.OPICARound4.odd_absolute_energy_anchor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.odd_absolute_energy_anchor"
#print axioms Zeta23.OPICARound4.odd_absolute_energy_anchor
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.real_scalar_shift_energy"
#check @Zeta23.OPICARound4.real_scalar_shift_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.real_scalar_shift_energy"
#print axioms Zeta23.OPICARound4.real_scalar_shift_energy
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.scalar_shift_negative_control"
#check @Zeta23.OPICARound4.scalar_shift_negative_control
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.scalar_shift_negative_control"
#print axioms Zeta23.OPICARound4.scalar_shift_negative_control
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound"
#check @Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound"
#check @Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_index_inverse_cost"
#check @Zeta23.OPICARound4.native_index_inverse_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_index_inverse_cost"
#print axioms Zeta23.OPICARound4.native_index_inverse_cost
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_bottom_le_quotient"
#check @Zeta23.OPICARound4.native_even_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_bottom_le_quotient"
#print axioms Zeta23.OPICARound4.native_even_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_bottom_le_quotient"
#check @Zeta23.OPICARound4.native_odd_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_bottom_le_quotient"
#print axioms Zeta23.OPICARound4.native_odd_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_bottom_le_quotient"
#check @Zeta23.OPICARound4.native_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_bottom_le_quotient"
#print axioms Zeta23.OPICARound4.native_bottom_le_quotient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.newborn_bottom_le_normalized_energy"
#check @Zeta23.OPICARound4.newborn_bottom_le_normalized_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.newborn_bottom_le_normalized_energy"
#print axioms Zeta23.OPICARound4.newborn_bottom_le_normalized_energy
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.newborn_witness_norm_branches"
#check @Zeta23.OPICARound4.newborn_witness_norm_branches
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.newborn_witness_norm_branches"
#print axioms Zeta23.OPICARound4.newborn_witness_norm_branches
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.even_negative_witness_ground"
#check @Zeta23.OPICARound4.even_negative_witness_ground
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.even_negative_witness_ground"
#print axioms Zeta23.OPICARound4.even_negative_witness_ground
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.odd_negative_witness_ground"
#check @Zeta23.OPICARound4.odd_negative_witness_ground
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.odd_negative_witness_ground"
#print axioms Zeta23.OPICARound4.odd_negative_witness_ground
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.common_cutoff_negative_ground_alternatives"
#check @Zeta23.OPICARound4.common_cutoff_negative_ground_alternatives
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.common_cutoff_negative_ground_alternatives"
#print axioms Zeta23.OPICARound4.common_cutoff_negative_ground_alternatives
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.even_eigenvectors_source_collinear"
#check @Zeta23.OPICARound4.even_eigenvectors_source_collinear
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.even_eigenvectors_source_collinear"
#print axioms Zeta23.OPICARound4.even_eigenvectors_source_collinear
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.odd_eigenvectors_source_collinear"
#check @Zeta23.OPICARound4.odd_eigenvectors_source_collinear
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.odd_eigenvectors_source_collinear"
#print axioms Zeta23.OPICARound4.odd_eigenvectors_source_collinear
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.negative_subspace_finrank_le_shell"
#check @Zeta23.OPICARound4.negative_subspace_finrank_le_shell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.negative_subspace_finrank_le_shell"
#print axioms Zeta23.OPICARound4.negative_subspace_finrank_le_shell
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.one_shell_negative_index_at_most_one"
#check @Zeta23.OPICARound4.one_shell_negative_index_at_most_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.one_shell_negative_index_at_most_one"
#print axioms Zeta23.OPICARound4.one_shell_negative_index_at_most_one
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.negative_vector_spans_negative_line"
#check @Zeta23.OPICARound4.negative_vector_spans_negative_line
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.negative_vector_spans_negative_line"
#print axioms Zeta23.OPICARound4.negative_vector_spans_negative_line
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.one_shell_negative_index_exact"
#check @Zeta23.OPICARound4.one_shell_negative_index_exact
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.one_shell_negative_index_exact"
#print axioms Zeta23.OPICARound4.one_shell_negative_index_exact
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeIndexInverseAdjoint"
#check @Zeta23.OPICARound4.nativeIndexInverseAdjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeIndexInverseAdjoint"
#print axioms Zeta23.OPICARound4.nativeIndexInverseAdjoint
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeIndexAdjointInverseAdjoint"
#check @Zeta23.OPICARound4.nativeIndexAdjointInverseAdjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeIndexAdjointInverseAdjoint"
#print axioms Zeta23.OPICARound4.nativeIndexAdjointInverseAdjoint
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hermitian_resolvent_signed_upper"
#check @Zeta23.OPICARound4.hermitian_resolvent_signed_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hermitian_resolvent_signed_upper"
#print axioms Zeta23.OPICARound4.hermitian_resolvent_signed_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_signed_upper"
#check @Zeta23.OPICARound4.native_even_signed_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_signed_upper"
#print axioms Zeta23.OPICARound4.native_even_signed_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_inverse_adjoint_eq_inverse"
#check @Zeta23.OPICARound4.native_odd_inverse_adjoint_eq_inverse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_inverse_adjoint_eq_inverse"
#print axioms Zeta23.OPICARound4.native_odd_inverse_adjoint_eq_inverse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_signed_upper"
#check @Zeta23.OPICARound4.native_odd_signed_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_signed_upper"
#print axioms Zeta23.OPICARound4.native_odd_signed_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.frozen_source_cell_consumer"
#check @Zeta23.OPICARound4.RegularCells.frozen_source_cell_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.frozen_source_cell_consumer"
#print axioms Zeta23.OPICARound4.RegularCells.frozen_source_cell_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.frozen_source_neutral_action"
#check @Zeta23.OPICARound4.RegularCells.frozen_source_neutral_action
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.frozen_source_neutral_action"
#print axioms Zeta23.OPICARound4.RegularCells.frozen_source_neutral_action
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.common_scalar_shift_invariant"
#check @Zeta23.OPICARound4.common_scalar_shift_invariant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.common_scalar_shift_invariant"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.orthogonal_source_row_shift"
#check @Zeta23.OPICARound4.orthogonal_source_row_shift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.orthogonal_source_row_shift"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.realCrossResidue"
#check @Zeta23.OPICARound4.realCrossResidue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.realCrossResidue"
#print axioms Zeta23.OPICARound4.realCrossResidue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.realCrossResidue_sum"
#check @Zeta23.OPICARound4.realCrossResidue_sum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.realCrossResidue_sum"
#print axioms Zeta23.OPICARound4.realCrossResidue_sum
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.realCrossResidue_variation_le"
#check @Zeta23.OPICARound4.realCrossResidue_variation_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.realCrossResidue_variation_le"
#print axioms Zeta23.OPICARound4.realCrossResidue_variation_le
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.diagonalSpectralResolvent"
#check @Zeta23.OPICARound4.diagonalSpectralResolvent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.diagonalSpectralResolvent"
#print axioms Zeta23.OPICARound4.diagonalSpectralResolvent
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.diagonal_resolvent_response"
#check @Zeta23.OPICARound4.diagonal_resolvent_response
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.diagonal_resolvent_response"
#print axioms Zeta23.OPICARound4.diagonal_resolvent_response
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.diagonal_signed_norm_upper"
#check @Zeta23.OPICARound4.diagonal_signed_norm_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.diagonal_signed_norm_upper"
#print axioms Zeta23.OPICARound4.diagonal_signed_norm_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signedSpectralResponse"
#check @Zeta23.OPICARound4.signedSpectralResponse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signedSpectralResponse"
#print axioms Zeta23.OPICARound4.signedSpectralResponse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_response_hasDerivAt"
#check @Zeta23.OPICARound4.signed_response_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_response_hasDerivAt"
#print axioms Zeta23.OPICARound4.signed_response_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.resolvent_kernel_unit_interval"
#check @Zeta23.OPICARound4.resolvent_kernel_unit_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.resolvent_kernel_unit_interval"
#print axioms Zeta23.OPICARound4.resolvent_kernel_unit_interval
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_kernel_upper"
#check @Zeta23.OPICARound4.signed_kernel_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_kernel_upper"
#print axioms Zeta23.OPICARound4.signed_kernel_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_resolvent_upper"
#check @Zeta23.OPICARound4.signed_resolvent_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_resolvent_upper"
#print axioms Zeta23.OPICARound4.signed_resolvent_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_response_lt_one_of_budget"
#check @Zeta23.OPICARound4.signed_response_lt_one_of_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_response_lt_one_of_budget"
#print axioms Zeta23.OPICARound4.signed_response_lt_one_of_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signedPrefix"
#check @Zeta23.OPICARound4.signedPrefix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signedPrefix"
#print axioms Zeta23.OPICARound4.signedPrefix
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_prefix_abel"
#check @Zeta23.OPICARound4.signed_prefix_abel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_prefix_abel"
#print axioms Zeta23.OPICARound4.signed_prefix_abel
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signed_prefix_nonnegative"
#check @Zeta23.OPICARound4.signed_prefix_nonnegative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signed_prefix_nonnegative"
#print axioms Zeta23.OPICARound4.signed_prefix_nonnegative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceAtomPairing_eq_physical_inner"
#check @Zeta23.OPICARound4.sourceAtomPairing_eq_physical_inner
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceAtomPairing_eq_physical_inner"
#print axioms Zeta23.OPICARound4.sourceAtomPairing_eq_physical_inner
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest"
#check @Zeta23.OPICARound4.correctedSourceTest
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest"
#print axioms Zeta23.OPICARound4.correctedSourceTest
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_eq_inner"
#check @Zeta23.OPICARound4.correctedSourceTest_eq_inner
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_eq_inner"
#print axioms Zeta23.OPICARound4.correctedSourceTest_eq_inner
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_lower_endpoint"
#check @Zeta23.OPICARound4.correctedSourceTest_lower_endpoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_lower_endpoint"
#print axioms Zeta23.OPICARound4.correctedSourceTest_lower_endpoint
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_upper_endpoint"
#check @Zeta23.OPICARound4.correctedSourceTest_upper_endpoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_upper_endpoint"
#print axioms Zeta23.OPICARound4.correctedSourceTest_upper_endpoint
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_hasDerivAt"
#check @Zeta23.OPICARound4.correctedSourceTest_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_hasDerivAt"
#print axioms Zeta23.OPICARound4.correctedSourceTest_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_prime_pairing"
#check @Zeta23.OPICARound4.correctedSourceTest_prime_pairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_prime_pairing"
#print axioms Zeta23.OPICARound4.correctedSourceTest_prime_pairing
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTest_complete_arithmetic"
#check @Zeta23.OPICARound4.correctedSourceTest_complete_arithmetic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTest_complete_arithmetic"
#print axioms Zeta23.OPICARound4.correctedSourceTest_complete_arithmetic
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_test_prerequisites"
#check @Zeta23.OPICARound4.actual_even_ray_test_prerequisites
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_test_prerequisites"
#print axioms Zeta23.OPICARound4.actual_even_ray_test_prerequisites
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_test_prerequisites"
#check @Zeta23.OPICARound4.actual_odd_resolvent_test_prerequisites
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_test_prerequisites"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_test_prerequisites
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow"
#check @Zeta23.OPICARound4.correctedSourceRow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow"
#print axioms Zeta23.OPICARound4.correctedSourceRow
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow_pairing"
#check @Zeta23.OPICARound4.correctedSourceRow_pairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow_pairing"
#print axioms Zeta23.OPICARound4.correctedSourceRow_pairing
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow_orthogonal"
#check @Zeta23.OPICARound4.correctedSourceRow_orthogonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow_orthogonal"
#print axioms Zeta23.OPICARound4.correctedSourceRow_orthogonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow_native"
#check @Zeta23.OPICARound4.correctedSourceRow_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow_native"
#print axioms Zeta23.OPICARound4.correctedSourceRow_native
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow_pole_cancelled"
#check @Zeta23.OPICARound4.correctedSourceRow_pole_cancelled
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow_pole_cancelled"
#print axioms Zeta23.OPICARound4.correctedSourceRow_pole_cancelled
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceRow_scalar_shift"
#check @Zeta23.OPICARound4.correctedSourceRow_scalar_shift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceRow_scalar_shift"
#print axioms Zeta23.OPICARound4.correctedSourceRow_scalar_shift
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rank_one_trace_displacement"
#check @Zeta23.OPICARound4.rank_one_trace_displacement
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rank_one_trace_displacement"
#print axioms Zeta23.OPICARound4.rank_one_trace_displacement
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rank_one_metric_identity"
#check @Zeta23.OPICARound4.rank_one_metric_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rank_one_metric_identity"
#print axioms Zeta23.OPICARound4.rank_one_metric_identity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_trace_displacement"
#check @Zeta23.OPICARound4.native_even_trace_displacement
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_trace_displacement"
#print axioms Zeta23.OPICARound4.native_even_trace_displacement
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_trace_displacement"
#check @Zeta23.OPICARound4.native_odd_trace_displacement
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_trace_displacement"
#print axioms Zeta23.OPICARound4.native_odd_trace_displacement
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_inverse_cost_consumer"
#check @Zeta23.OPICARound4.Validation.native_inverse_cost_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_inverse_cost_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_inverse_cost_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.even_physical_quotient_consumer"
#check @Zeta23.OPICARound4.Validation.even_physical_quotient_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.even_physical_quotient_consumer"
#print axioms Zeta23.OPICARound4.Validation.even_physical_quotient_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.odd_physical_quotient_consumer"
#check @Zeta23.OPICARound4.Validation.odd_physical_quotient_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.odd_physical_quotient_consumer"
#print axioms Zeta23.OPICARound4.Validation.odd_physical_quotient_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_newborn_normalized_cost_consumer"
#check @Zeta23.OPICARound4.Validation.native_newborn_normalized_cost_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_newborn_normalized_cost_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_newborn_normalized_cost_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.common_cutoff_source_or_shared_ground_consumer"
#check @Zeta23.OPICARound4.Validation.common_cutoff_source_or_shared_ground_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.common_cutoff_source_or_shared_ground_consumer"
#print axioms Zeta23.OPICARound4.Validation.common_cutoff_source_or_shared_ground_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.corrected_native_row_consumer"
#check @Zeta23.OPICARound4.Validation.corrected_native_row_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.corrected_native_row_consumer"
#print axioms Zeta23.OPICARound4.Validation.corrected_native_row_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.complete_arithmetic_consumer"
#check @Zeta23.OPICARound4.Validation.complete_arithmetic_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.complete_arithmetic_consumer"
#print axioms Zeta23.OPICARound4.Validation.complete_arithmetic_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.source_test_endpoint_consumer"
#check @Zeta23.OPICARound4.Validation.source_test_endpoint_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.source_test_endpoint_consumer"
#print axioms Zeta23.OPICARound4.Validation.source_test_endpoint_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.source_test_derivative_consumer"
#check @Zeta23.OPICARound4.Validation.source_test_derivative_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.source_test_derivative_consumer"
#print axioms Zeta23.OPICARound4.Validation.source_test_derivative_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.exact_negative_index_consumer"
#check @Zeta23.OPICARound4.Validation.exact_negative_index_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.exact_negative_index_consumer"
#print axioms Zeta23.OPICARound4.Validation.exact_negative_index_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.trace_displacement_consumer"
#check @Zeta23.OPICARound4.Validation.trace_displacement_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.trace_displacement_consumer"
#print axioms Zeta23.OPICARound4.Validation.trace_displacement_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.nonunit_metric_consumer"
#check @Zeta23.OPICARound4.Validation.nonunit_metric_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.nonunit_metric_consumer"
#print axioms Zeta23.OPICARound4.Validation.nonunit_metric_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.signed_resolvent_budget_consumer"
#check @Zeta23.OPICARound4.Validation.signed_resolvent_budget_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.signed_resolvent_budget_consumer"
#print axioms Zeta23.OPICARound4.Validation.signed_resolvent_budget_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.signed_prefix_comparison_consumer"
#check @Zeta23.OPICARound4.Validation.signed_prefix_comparison_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.signed_prefix_comparison_consumer"
#print axioms Zeta23.OPICARound4.Validation.signed_prefix_comparison_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.frozen_source_cell_consumer"
#check @Zeta23.OPICARound4.Validation.frozen_source_cell_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.frozen_source_cell_consumer"
#print axioms Zeta23.OPICARound4.Validation.frozen_source_cell_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_even_signed_bound_consumer"
#check @Zeta23.OPICARound4.Validation.actual_even_signed_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_even_signed_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_even_signed_bound_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_odd_signed_bound_consumer"
#check @Zeta23.OPICARound4.Validation.actual_odd_signed_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_odd_signed_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_odd_signed_bound_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.physical_shell_norm_consumer"
#check @Zeta23.OPICARound4.Validation.physical_shell_norm_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.physical_shell_norm_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.regular_witness_norm_consumer"
#check @Zeta23.OPICARound4.Validation.regular_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.regular_witness_norm_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer"
#check @Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer"
#check @Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer"
#check @Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.common_scalar_shift_consumer"
#check @Zeta23.OPICARound4.Validation.common_scalar_shift_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.common_scalar_shift_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer"
#check @Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.even_source_bound_consumer"
#check @Zeta23.OPICARound4.Validation.even_source_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.even_source_bound_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.odd_source_bound_consumer"
#check @Zeta23.OPICARound4.Validation.odd_source_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.odd_source_bound_consumer"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.shell_sub_norm_sq"
#check @Zeta23.OPICARound4.shell_sub_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.shell_sub_norm_sq"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.regular_witness_norm_sq"
#check @Zeta23.OPICARound4.regular_witness_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.regular_witness_norm_sq"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.resonant_witness_norm_sq"
#check @Zeta23.OPICARound4.resonant_witness_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.resonant_witness_norm_sq"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rayleighEnergy"
#check @Zeta23.OPICARound4.rayleighEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rayleighEnergy"
#print axioms Zeta23.OPICARound4.rayleighEnergy
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.regular_witness_rayleigh"
#check @Zeta23.OPICARound4.regular_witness_rayleigh
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.regular_witness_rayleigh"
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.resonant_witness_rayleigh"
#check @Zeta23.OPICARound4.resonant_witness_rayleigh
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.resonant_witness_rayleigh"
