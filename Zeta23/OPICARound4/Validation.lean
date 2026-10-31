import Zeta23.OPICARound4.Validation.GroundConstraints
import Zeta23.OPICARound4.Validation.DetectorErrors
import Zeta23.OPICARound4.Validation.ErrorReduction
import Zeta23.OPICARound4
import Zeta23.OPICARound4.Validation.IntegrationClosure
import Zeta23.OPICARound4.Validation.IntegrationDictionary
import Zeta23.OPICARound4.Validation.IntegrationObservation
import Zeta23.OPICARound4.Validation.IntegrationSource
import Zeta23.OPICARound4.Validation.IntegrationSpectral
import Zeta23.OPICARound4.Validation.IntegrationVisibilityRigidity
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
#print axioms Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound"
#check @Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound"
#print axioms Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound
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
#print axioms Zeta23.OPICARound4.common_scalar_shift_invariant
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.orthogonal_source_row_shift"
#check @Zeta23.OPICARound4.orthogonal_source_row_shift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.orthogonal_source_row_shift"
#print axioms Zeta23.OPICARound4.orthogonal_source_row_shift
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
#print axioms Zeta23.OPICARound4.Validation.physical_shell_norm_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.regular_witness_norm_consumer"
#check @Zeta23.OPICARound4.Validation.regular_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.regular_witness_norm_consumer"
#print axioms Zeta23.OPICARound4.Validation.regular_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer"
#check @Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer"
#print axioms Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer"
#check @Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer"
#print axioms Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer"
#check @Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer"
#print axioms Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.common_scalar_shift_consumer"
#check @Zeta23.OPICARound4.Validation.common_scalar_shift_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.common_scalar_shift_consumer"
#print axioms Zeta23.OPICARound4.Validation.common_scalar_shift_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer"
#check @Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer"
#print axioms Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.even_source_bound_consumer"
#check @Zeta23.OPICARound4.Validation.even_source_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.even_source_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.even_source_bound_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.odd_source_bound_consumer"
#check @Zeta23.OPICARound4.Validation.odd_source_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.odd_source_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.odd_source_bound_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.shell_sub_norm_sq"
#check @Zeta23.OPICARound4.shell_sub_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.shell_sub_norm_sq"
#print axioms Zeta23.OPICARound4.shell_sub_norm_sq
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.regular_witness_norm_sq"
#check @Zeta23.OPICARound4.regular_witness_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.regular_witness_norm_sq"
#print axioms Zeta23.OPICARound4.regular_witness_norm_sq
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.resonant_witness_norm_sq"
#check @Zeta23.OPICARound4.resonant_witness_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.resonant_witness_norm_sq"
#print axioms Zeta23.OPICARound4.resonant_witness_norm_sq
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rayleighEnergy"
#check @Zeta23.OPICARound4.rayleighEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rayleighEnergy"
#print axioms Zeta23.OPICARound4.rayleighEnergy
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.regular_witness_rayleigh"
#check @Zeta23.OPICARound4.regular_witness_rayleigh
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.regular_witness_rayleigh"
#print axioms Zeta23.OPICARound4.regular_witness_rayleigh
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.resonant_witness_rayleigh"
#check @Zeta23.OPICARound4.resonant_witness_rayleigh
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.resonant_witness_rayleigh"
#print axioms Zeta23.OPICARound4.resonant_witness_rayleigh
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.EvenNegativeGroundRestriction"
#check @Zeta23.OPICARound4.EvenNegativeGroundRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.EvenNegativeGroundRestriction"
#print axioms Zeta23.OPICARound4.EvenNegativeGroundRestriction
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.EventualActualRayClosure"
#check @Zeta23.OPICARound4.EventualActualRayClosure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.EventualActualRayClosure"
#print axioms Zeta23.OPICARound4.EventualActualRayClosure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.EventualNativeJointNegativeIndexCap"
#check @Zeta23.OPICARound4.EventualNativeJointNegativeIndexCap
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.EventualNativeJointNegativeIndexCap"
#print axioms Zeta23.OPICARound4.EventualNativeJointNegativeIndexCap
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.EventualNegativeGroundClosure"
#check @Zeta23.OPICARound4.EventualNegativeGroundClosure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.EventualNegativeGroundClosure"
#print axioms Zeta23.OPICARound4.EventualNegativeGroundClosure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.GroupedInputInvisible"
#check @Zeta23.OPICARound4.GroupedInputInvisible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.GroupedInputInvisible"
#print axioms Zeta23.OPICARound4.GroupedInputInvisible
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.GroupedOutputInvisible"
#check @Zeta23.OPICARound4.GroupedOutputInvisible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.GroupedOutputInvisible"
#print axioms Zeta23.OPICARound4.GroupedOutputInvisible
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.GroupedSpectrum"
#check @Zeta23.OPICARound4.GroupedSpectrum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.GroupedSpectrum"
#print axioms Zeta23.OPICARound4.GroupedSpectrum
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.IntegrationClosureTarget"
#check @Zeta23.OPICARound4.IntegrationClosureTarget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.IntegrationClosureTarget"
#print axioms Zeta23.OPICARound4.IntegrationClosureTarget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.IntegrationJointIndexTarget"
#check @Zeta23.OPICARound4.IntegrationJointIndexTarget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.IntegrationJointIndexTarget"
#print axioms Zeta23.OPICARound4.IntegrationJointIndexTarget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.IntegrationSourceBudgetTarget"
#check @Zeta23.OPICARound4.IntegrationSourceBudgetTarget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.IntegrationSourceBudgetTarget"
#print axioms Zeta23.OPICARound4.IntegrationSourceBudgetTarget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeJointNegativeIndexAtMostOne"
#check @Zeta23.OPICARound4.NativeJointNegativeIndexAtMostOne
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeJointNegativeIndexAtMostOne"
#print axioms Zeta23.OPICARound4.NativeJointNegativeIndexAtMostOne
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeNegativeObservationBound"
#check @Zeta23.OPICARound4.NativeNegativeObservationBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeNegativeObservationBound"
#print axioms Zeta23.OPICARound4.NativeNegativeObservationBound
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativePhysicalNeutralSubspace"
#check @Zeta23.OPICARound4.NativePhysicalNeutralSubspace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativePhysicalNeutralSubspace"
#print axioms Zeta23.OPICARound4.NativePhysicalNeutralSubspace
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.OddNegativeGroundRestriction"
#check @Zeta23.OPICARound4.OddNegativeGroundRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.OddNegativeGroundRestriction"
#print axioms Zeta23.OPICARound4.OddNegativeGroundRestriction
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.centeredMoment_fixedSeedDiagonal"
#check @Zeta23.OPICARound4.RegularCells.centeredMoment_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.centeredMoment_fixedSeedDiagonal"
#print axioms Zeta23.OPICARound4.RegularCells.centeredMoment_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.even_pole_fixedSeedDiagonal"
#check @Zeta23.OPICARound4.RegularCells.even_pole_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.even_pole_fixedSeedDiagonal"
#print axioms Zeta23.OPICARound4.RegularCells.even_pole_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeed"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeed"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeed
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeedToPhysical"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeedToPhysical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeedToPhysical"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedToPhysical
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedEvenSeed_diagonal_iff"
#check @Zeta23.OPICARound4.RegularCells.fixedEvenSeed_diagonal_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedEvenSeed_diagonal_iff"
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeed_diagonal_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeed"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeed"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeed
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeedToPhysical"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeedToPhysical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeedToPhysical"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedToPhysical
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedOddSeed_diagonal_iff"
#check @Zeta23.OPICARound4.RegularCells.fixedOddSeed_diagonal_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedOddSeed_diagonal_iff"
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeed_diagonal_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry_pos"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry_pos"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry_pos
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEquiv"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEquiv"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEquiv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_apply"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_apply"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_apply
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_even_iff"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_even_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_even_iff"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_even_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_odd_iff"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_odd_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_odd_iff"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_odd_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_reverse"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_reverse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_reverse"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_reverse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedGram"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedGram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedGram"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedGram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedGram_eq_physical_inner"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedGram_eq_physical_inner
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedGram_eq_physical_inner"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedGram_eq_physical_inner
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.fixedSeedParameter"
#check @Zeta23.OPICARound4.RegularCells.fixedSeedParameter
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.fixedSeedParameter"
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedParameter
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.mem_fixedEvenSeed_iff"
#check @Zeta23.OPICARound4.RegularCells.mem_fixedEvenSeed_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.mem_fixedEvenSeed_iff"
#print axioms Zeta23.OPICARound4.RegularCells.mem_fixedEvenSeed_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.mem_fixedOddSeed_iff"
#check @Zeta23.OPICARound4.RegularCells.mem_fixedOddSeed_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.mem_fixedOddSeed_iff"
#print axioms Zeta23.OPICARound4.RegularCells.mem_fixedOddSeed_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.odd_pole_fixedSeedDiagonal"
#check @Zeta23.OPICARound4.RegularCells.odd_pole_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.odd_pole_fixedSeedDiagonal"
#print axioms Zeta23.OPICARound4.RegularCells.odd_pole_fixedSeedDiagonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.poleEvenProfile_fixedSeedDiagonalEntry"
#check @Zeta23.OPICARound4.RegularCells.poleEvenProfile_fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.poleEvenProfile_fixedSeedDiagonalEntry"
#print axioms Zeta23.OPICARound4.RegularCells.poleEvenProfile_fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.poleOddProfile_fixedSeedDiagonalEntry"
#check @Zeta23.OPICARound4.RegularCells.poleOddProfile_fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.poleOddProfile_fixedSeedDiagonalEntry"
#print axioms Zeta23.OPICARound4.RegularCells.poleOddProfile_fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.SearchSupport.index_two_contradicts_cap"
#check @Zeta23.OPICARound4.SearchSupport.index_two_contradicts_cap
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.SearchSupport.index_two_contradicts_cap"
#print axioms Zeta23.OPICARound4.SearchSupport.index_two_contradicts_cap
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.SearchSupport.strict_response_of_signed_upper"
#check @Zeta23.OPICARound4.SearchSupport.strict_response_of_signed_upper
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.SearchSupport.strict_response_of_signed_upper"
#print axioms Zeta23.OPICARound4.SearchSupport.strict_response_of_signed_upper
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.StrictlyNegativeNativeSubspace"
#check @Zeta23.OPICARound4.StrictlyNegativeNativeSubspace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.StrictlyNegativeNativeSubspace"
#print axioms Zeta23.OPICARound4.StrictlyNegativeNativeSubspace
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.UniformPrimeDiscrepancyBound"
#check @Zeta23.OPICARound4.UniformPrimeDiscrepancyBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.UniformPrimeDiscrepancyBound"
#print axioms Zeta23.OPICARound4.UniformPrimeDiscrepancyBound
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_ground_closure_consumer"
#check @Zeta23.OPICARound4.Validation.actual_ground_closure_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_ground_closure_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_ground_closure_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_ray_closure_consumer"
#check @Zeta23.OPICARound4.Validation.actual_ray_closure_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_ray_closure_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_ray_closure_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.allNegativeFamilyA"
#check @Zeta23.OPICARound4.Validation.allNegativeFamilyA
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.allNegativeFamilyA"
#print axioms Zeta23.OPICARound4.Validation.allNegativeFamilyA
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.allNegativeFamilyB"
#check @Zeta23.OPICARound4.Validation.allNegativeFamilyB
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.allNegativeFamilyB"
#print axioms Zeta23.OPICARound4.Validation.allNegativeFamilyB
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.allNegativeSpectralValue"
#check @Zeta23.OPICARound4.Validation.allNegativeSpectralValue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.allNegativeSpectralValue"
#print axioms Zeta23.OPICARound4.Validation.allNegativeSpectralValue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.allNegativeSpectralValue_injective"
#check @Zeta23.OPICARound4.Validation.allNegativeSpectralValue_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.allNegativeSpectralValue_injective"
#print axioms Zeta23.OPICARound4.Validation.allNegativeSpectralValue_injective
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.all_negative_family_coordinate_coefficient"
#check @Zeta23.OPICARound4.Validation.all_negative_family_coordinate_coefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.all_negative_family_coordinate_coefficient"
#print axioms Zeta23.OPICARound4.Validation.all_negative_family_coordinate_coefficient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.all_negative_family_hermitian"
#check @Zeta23.OPICARound4.Validation.all_negative_family_hermitian
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.all_negative_family_hermitian"
#print axioms Zeta23.OPICARound4.Validation.all_negative_family_hermitian
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.all_negative_family_rank_one"
#check @Zeta23.OPICARound4.Validation.all_negative_family_rank_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.all_negative_family_rank_one"
#print axioms Zeta23.OPICARound4.Validation.all_negative_family_rank_one
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.arbitrarily_many_negative_atoms"
#check @Zeta23.OPICARound4.Validation.arbitrarily_many_negative_atoms
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.arbitrarily_many_negative_atoms"
#print axioms Zeta23.OPICARound4.Validation.arbitrarily_many_negative_atoms
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer"
#check @Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer"
#print axioms Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.declared_input_reachability_consumer"
#check @Zeta23.OPICARound4.Validation.declared_input_reachability_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.declared_input_reachability_consumer"
#print axioms Zeta23.OPICARound4.Validation.declared_input_reachability_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer"
#check @Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer"
#print axioms Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer"
#check @Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer"
#print axioms Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer"
#check @Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer"
#print axioms Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer"
#check @Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer"
#print axioms Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer"
#check @Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer"
#print axioms Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.finite_observation_energy_consumer"
#check @Zeta23.OPICARound4.Validation.finite_observation_energy_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.finite_observation_energy_consumer"
#print axioms Zeta23.OPICARound4.Validation.finite_observation_energy_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer"
#check @Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer"
#print axioms Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer"
#check @Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer"
#print axioms Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer"
#check @Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer"
#print axioms Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer"
#check @Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer"
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer"
#check @Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer"
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer"
#check @Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer"
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.general_cross_observation_cancellation"
#check @Zeta23.OPICARound4.Validation.general_cross_observation_cancellation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.general_cross_observation_cancellation"
#print axioms Zeta23.OPICARound4.Validation.general_cross_observation_cancellation
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.grouped_upper_away"
#check @Zeta23.OPICARound4.Validation.grouped_upper_away
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.grouped_upper_away"
#print axioms Zeta23.OPICARound4.Validation.grouped_upper_away
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.hermitianUpperResponse"
#check @Zeta23.OPICARound4.Validation.hermitianUpperResponse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.hermitianUpperResponse"
#print axioms Zeta23.OPICARound4.Validation.hermitianUpperResponse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.hermitian_rank_one_upper_pick_identity"
#check @Zeta23.OPICARound4.Validation.hermitian_rank_one_upper_pick_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.hermitian_rank_one_upper_pick_identity"
#print axioms Zeta23.OPICARound4.Validation.hermitian_rank_one_upper_pick_identity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.hermitian_upper_response_expansion"
#check @Zeta23.OPICARound4.Validation.hermitian_upper_response_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.hermitian_upper_response_expansion"
#print axioms Zeta23.OPICARound4.Validation.hermitian_upper_response_expansion
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer"
#check @Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer"
#print axioms Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer"
#check @Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer"
#print axioms Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.invisible_shared_mode_control"
#check @Zeta23.OPICARound4.Validation.invisible_shared_mode_control
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.invisible_shared_mode_control"
#print axioms Zeta23.OPICARound4.Validation.invisible_shared_mode_control
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.nativeEvenUpperResponse"
#check @Zeta23.OPICARound4.Validation.nativeEvenUpperResponse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.nativeEvenUpperResponse"
#print axioms Zeta23.OPICARound4.Validation.nativeEvenUpperResponse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.nativeOddUpperResponse"
#check @Zeta23.OPICARound4.Validation.nativeOddUpperResponse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.nativeOddUpperResponse"
#print axioms Zeta23.OPICARound4.Validation.nativeOddUpperResponse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_even_invisible_eigen_shared"
#check @Zeta23.OPICARound4.Validation.native_even_invisible_eigen_shared
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_even_invisible_eigen_shared"
#print axioms Zeta23.OPICARound4.Validation.native_even_invisible_eigen_shared
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer"
#check @Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_even_upper_pick_identity"
#check @Zeta23.OPICARound4.Validation.native_even_upper_pick_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_even_upper_pick_identity"
#print axioms Zeta23.OPICARound4.Validation.native_even_upper_pick_identity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_even_zero_residue_classification"
#check @Zeta23.OPICARound4.Validation.native_even_zero_residue_classification
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_even_zero_residue_classification"
#print axioms Zeta23.OPICARound4.Validation.native_even_zero_residue_classification
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer"
#check @Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_odd_invisible_eigen_shared"
#check @Zeta23.OPICARound4.Validation.native_odd_invisible_eigen_shared
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_odd_invisible_eigen_shared"
#print axioms Zeta23.OPICARound4.Validation.native_odd_invisible_eigen_shared
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer"
#check @Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_odd_upper_pick_identity"
#check @Zeta23.OPICARound4.Validation.native_odd_upper_pick_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_odd_upper_pick_identity"
#print axioms Zeta23.OPICARound4.Validation.native_odd_upper_pick_identity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_odd_zero_residue_classification"
#check @Zeta23.OPICARound4.Validation.native_odd_zero_residue_classification
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_odd_zero_residue_classification"
#print axioms Zeta23.OPICARound4.Validation.native_odd_zero_residue_classification
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.node_jets_suffice_consumer"
#check @Zeta23.OPICARound4.Validation.node_jets_suffice_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.node_jets_suffice_consumer"
#print axioms Zeta23.OPICARound4.Validation.node_jets_suffice_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer"
#check @Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumA"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumA
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumA"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumA
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumB"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumB
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumB"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumB
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumCoordinateCoefficient"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumCoordinateCoefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumCoordinateCoefficient"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumCoordinateCoefficient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumD"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumD
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumD"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumD
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumDinv"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumDinv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumDinv"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumDinv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumP₁"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumP₁
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumP₁"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumP₁
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeatedSpectrumP₂"
#check @Zeta23.OPICARound4.Validation.repeatedSpectrumP₂
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeatedSpectrumP₂"
#print axioms Zeta23.OPICARound4.Validation.repeatedSpectrumP₂
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeated_spectrum_coordinate_projectors"
#check @Zeta23.OPICARound4.Validation.repeated_spectrum_coordinate_projectors
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeated_spectrum_coordinate_projectors"
#print axioms Zeta23.OPICARound4.Validation.repeated_spectrum_coordinate_projectors
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeated_spectrum_hermitian_controls"
#check @Zeta23.OPICARound4.Validation.repeated_spectrum_hermitian_controls
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeated_spectrum_hermitian_controls"
#print axioms Zeta23.OPICARound4.Validation.repeated_spectrum_hermitian_controls
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeated_spectrum_nonreal_coordinates"
#check @Zeta23.OPICARound4.Validation.repeated_spectrum_nonreal_coordinates
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeated_spectrum_nonreal_coordinates"
#print axioms Zeta23.OPICARound4.Validation.repeated_spectrum_nonreal_coordinates
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeated_spectrum_rank_one"
#check @Zeta23.OPICARound4.Validation.repeated_spectrum_rank_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeated_spectrum_rank_one"
#print axioms Zeta23.OPICARound4.Validation.repeated_spectrum_rank_one
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.repeated_spectrum_transport_inverse"
#check @Zeta23.OPICARound4.Validation.repeated_spectrum_transport_inverse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.repeated_spectrum_transport_inverse"
#print axioms Zeta23.OPICARound4.Validation.repeated_spectrum_transport_inverse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_adaptive_membership"
#check @Zeta23.OPICARound4.actual_even_ray_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_even_ray_adaptive_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_gap_norm"
#check @Zeta23.OPICARound4.actual_even_ray_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_gap_norm"
#print axioms Zeta23.OPICARound4.actual_even_ray_gap_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_priced_membership"
#check @Zeta23.OPICARound4.actual_even_ray_priced_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_priced_membership"
#print axioms Zeta23.OPICARound4.actual_even_ray_priced_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership"
#check @Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm"
#check @Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm"
#print axioms Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership"
#check @Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_gap_norm"
#check @Zeta23.OPICARound4.actual_odd_resolvent_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_gap_norm"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_gap_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_priced_membership"
#check @Zeta23.OPICARound4.actual_odd_resolvent_priced_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_priced_membership"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_priced_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.blind_vector_in_every_finite_gram_kernel"
#check @Zeta23.OPICARound4.blind_vector_in_every_finite_gram_kernel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.blind_vector_in_every_finite_gram_kernel"
#print axioms Zeta23.OPICARound4.blind_vector_in_every_finite_gram_kernel
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.complexSignedSpectralResponse"
#check @Zeta23.OPICARound4.complexSignedSpectralResponse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.complexSignedSpectralResponse"
#print axioms Zeta23.OPICARound4.complexSignedSpectralResponse
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTestDerivative"
#check @Zeta23.OPICARound4.correctedSourceTestDerivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTestDerivative"
#print axioms Zeta23.OPICARound4.correctedSourceTestDerivative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTestDerivative_continuous"
#check @Zeta23.OPICARound4.correctedSourceTestDerivative_continuous
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTestDerivative_continuous"
#print axioms Zeta23.OPICARound4.correctedSourceTestDerivative_continuous
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.diagonal_safe_source_regression"
#check @Zeta23.OPICARound4.diagonal_safe_source_regression
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.diagonal_safe_source_regression"
#print axioms Zeta23.OPICARound4.diagonal_safe_source_regression
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eigenmode_invisible_at_all_powers"
#check @Zeta23.OPICARound4.eigenmode_invisible_at_all_powers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eigenmode_invisible_at_all_powers"
#print axioms Zeta23.OPICARound4.eigenmode_invisible_at_all_powers
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.even_negative_ground_restriction_of_all_ray"
#check @Zeta23.OPICARound4.even_negative_ground_restriction_of_all_ray
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.even_negative_ground_restriction_of_all_ray"
#print axioms Zeta23.OPICARound4.even_negative_ground_restriction_of_all_ray
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds"
#check @Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds"
#print axioms Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventual_ground_closure_of_three_thresholds"
#check @Zeta23.OPICARound4.eventual_ground_closure_of_three_thresholds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventual_ground_closure_of_three_thresholds"
#print axioms Zeta23.OPICARound4.eventual_ground_closure_of_three_thresholds
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventual_noBothNeg_of_actual_ray_closure"
#check @Zeta23.OPICARound4.eventual_noBothNeg_of_actual_ray_closure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventual_noBothNeg_of_actual_ray_closure"
#print axioms Zeta23.OPICARound4.eventual_noBothNeg_of_actual_ray_closure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventual_noBothNeg_of_ground_closure"
#check @Zeta23.OPICARound4.eventual_noBothNeg_of_ground_closure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventual_noBothNeg_of_ground_closure"
#print axioms Zeta23.OPICARound4.eventual_noBothNeg_of_ground_closure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt"
#check @Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt"
#print axioms Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets"
#check @Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets"
#print axioms Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteInputReachableSubspace"
#check @Zeta23.OPICARound4.finiteInputReachableSubspace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteInputReachableSubspace"
#print axioms Zeta23.OPICARound4.finiteInputReachableSubspace
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteObservationGram"
#check @Zeta23.OPICARound4.finiteObservationGram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteObservationGram"
#print axioms Zeta23.OPICARound4.finiteObservationGram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteObservationGram_energy"
#check @Zeta23.OPICARound4.finiteObservationGram_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteObservationGram_energy"
#print axioms Zeta23.OPICARound4.finiteObservationGram_energy
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteObservationGram_kernel_iff"
#check @Zeta23.OPICARound4.finiteObservationGram_kernel_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteObservationGram_kernel_iff"
#print axioms Zeta23.OPICARound4.finiteObservationGram_kernel_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteObservationGram_nonnegative"
#check @Zeta23.OPICARound4.finiteObservationGram_nonnegative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteObservationGram_nonnegative"
#print axioms Zeta23.OPICARound4.finiteObservationGram_nonnegative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_grouped_residue_star"
#check @Zeta23.OPICARound4.finite_grouped_residue_star
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_grouped_residue_star"
#print axioms Zeta23.OPICARound4.finite_grouped_residue_star
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_signed_pick_gram"
#check @Zeta23.OPICARound4.finite_signed_pick_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_signed_pick_gram"
#print axioms Zeta23.OPICARound4.finite_signed_pick_gram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_signed_pick_gram_re"
#check @Zeta23.OPICARound4.finite_signed_pick_gram_re
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_signed_pick_gram_re"
#print axioms Zeta23.OPICARound4.finite_signed_pick_gram_re
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_signed_pick_identity"
#check @Zeta23.OPICARound4.finite_signed_pick_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_signed_pick_identity"
#print axioms Zeta23.OPICARound4.finite_signed_pick_identity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_signed_pick_negative_subspace_bound"
#check @Zeta23.OPICARound4.finite_signed_pick_negative_subspace_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_signed_pick_negative_subspace_bound"
#print axioms Zeta23.OPICARound4.finite_signed_pick_negative_subspace_bound
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_signed_pick_negative_subspace_exact"
#check @Zeta23.OPICARound4.finite_signed_pick_negative_subspace_exact
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_signed_pick_negative_subspace_exact"
#print axioms Zeta23.OPICARound4.finite_signed_pick_negative_subspace_exact
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.fixedSeedFrame"
#check @Zeta23.OPICARound4.fixedSeedFrame
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.fixedSeedFrame"
#print axioms Zeta23.OPICARound4.fixedSeedFrame
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.fixedSeedFrameDerivative"
#check @Zeta23.OPICARound4.fixedSeedFrameDerivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.fixedSeedFrameDerivative"
#print axioms Zeta23.OPICARound4.fixedSeedFrameDerivative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.fixedSeedFrame_hasDerivAt"
#check @Zeta23.OPICARound4.fixedSeedFrame_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.fixedSeedFrame_hasDerivAt"
#print axioms Zeta23.OPICARound4.fixedSeedFrame_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameEnergyDerivative"
#check @Zeta23.OPICARound4.frameEnergyDerivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameEnergyDerivative"
#print axioms Zeta23.OPICARound4.frameEnergyDerivative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameEnergyEntry"
#check @Zeta23.OPICARound4.frameEnergyEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameEnergyEntry"
#print axioms Zeta23.OPICARound4.frameEnergyEntry
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameEnergyEntry_hasDerivAt"
#check @Zeta23.OPICARound4.frameEnergyEntry_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameEnergyEntry_hasDerivAt"
#print axioms Zeta23.OPICARound4.frameEnergyEntry_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameGramDerivative"
#check @Zeta23.OPICARound4.frameGramDerivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameGramDerivative"
#print axioms Zeta23.OPICARound4.frameGramDerivative
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameGramEntry"
#check @Zeta23.OPICARound4.frameGramEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameGramEntry"
#print axioms Zeta23.OPICARound4.frameGramEntry
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frameGramEntry_hasDerivAt"
#check @Zeta23.OPICARound4.frameGramEntry_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frameGramEntry_hasDerivAt"
#print axioms Zeta23.OPICARound4.frameGramEntry_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frame_contradicts_native_joint_index"
#check @Zeta23.OPICARound4.frame_contradicts_native_joint_index
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frame_contradicts_native_joint_index"
#print axioms Zeta23.OPICARound4.frame_contradicts_native_joint_index
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.frame_strictly_negative_native_plane"
#check @Zeta23.OPICARound4.frame_strictly_negative_native_plane
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.frame_strictly_negative_native_plane"
#print axioms Zeta23.OPICARound4.frame_strictly_negative_native_plane
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedEigenvalue"
#check @Zeta23.OPICARound4.groupedEigenvalue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedEigenvalue"
#print axioms Zeta23.OPICARound4.groupedEigenvalue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedEigenvalue_cast"
#check @Zeta23.OPICARound4.groupedEigenvalue_cast
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedEigenvalue_cast"
#print axioms Zeta23.OPICARound4.groupedEigenvalue_cast
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedEigenvalue_injective"
#check @Zeta23.OPICARound4.groupedEigenvalue_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedEigenvalue_injective"
#print axioms Zeta23.OPICARound4.groupedEigenvalue_injective
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedShiftedEquiv"
#check @Zeta23.OPICARound4.groupedShiftedEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedShiftedEquiv"
#print axioms Zeta23.OPICARound4.groupedShiftedEquiv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSignedResidue"
#check @Zeta23.OPICARound4.groupedSignedResidue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSignedResidue"
#print axioms Zeta23.OPICARound4.groupedSignedResidue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSignedResidue_cast"
#check @Zeta23.OPICARound4.groupedSignedResidue_cast
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSignedResidue_cast"
#print axioms Zeta23.OPICARound4.groupedSignedResidue_cast
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSpectralCoefficient"
#check @Zeta23.OPICARound4.groupedSpectralCoefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSpectralCoefficient"
#print axioms Zeta23.OPICARound4.groupedSpectralCoefficient
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSpectralCoefficient_star"
#check @Zeta23.OPICARound4.groupedSpectralCoefficient_star
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSpectralCoefficient_star"
#print axioms Zeta23.OPICARound4.groupedSpectralCoefficient_star
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSpectralProjector"
#check @Zeta23.OPICARound4.groupedSpectralProjector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSpectralProjector"
#print axioms Zeta23.OPICARound4.groupedSpectralProjector
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization"
#check @Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization"
#print axioms Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.groupedSpectralProjector_eq_starProjection"
#check @Zeta23.OPICARound4.groupedSpectralProjector_eq_starProjection
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.groupedSpectralProjector_eq_starProjection"
#print axioms Zeta23.OPICARound4.groupedSpectralProjector_eq_starProjection
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_input_invisible_coefficient_zero"
#check @Zeta23.OPICARound4.grouped_input_invisible_coefficient_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_input_invisible_coefficient_zero"
#print axioms Zeta23.OPICARound4.grouped_input_invisible_coefficient_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_invisible_residue_zero"
#check @Zeta23.OPICARound4.grouped_invisible_residue_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_invisible_residue_zero"
#print axioms Zeta23.OPICARound4.grouped_invisible_residue_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_output_invisible_coefficient_zero"
#check @Zeta23.OPICARound4.grouped_output_invisible_coefficient_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_output_invisible_coefficient_zero"
#print axioms Zeta23.OPICARound4.grouped_output_invisible_coefficient_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_real_response"
#check @Zeta23.OPICARound4.grouped_real_response
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_real_response"
#print axioms Zeta23.OPICARound4.grouped_real_response
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible"
#check @Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible"
#print axioms Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_residue_zero_iff_pairing_zero"
#check @Zeta23.OPICARound4.grouped_residue_zero_iff_pairing_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_residue_zero_iff_pairing_zero"
#print axioms Zeta23.OPICARound4.grouped_residue_zero_iff_pairing_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_resolvent_expansion"
#check @Zeta23.OPICARound4.grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_resolvent_expansion"
#print axioms Zeta23.OPICARound4.grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_shift_away_of_equiv"
#check @Zeta23.OPICARound4.grouped_shift_away_of_equiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_shift_away_of_equiv"
#print axioms Zeta23.OPICARound4.grouped_shift_away_of_equiv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_shift_injective"
#check @Zeta23.OPICARound4.grouped_shift_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_shift_injective"
#print axioms Zeta23.OPICARound4.grouped_shift_injective
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_signed_resolvent_expansion"
#check @Zeta23.OPICARound4.grouped_signed_resolvent_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_signed_resolvent_expansion"
#print axioms Zeta23.OPICARound4.grouped_signed_resolvent_expansion
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.grouped_zero_coefficient_rigidity"
#check @Zeta23.OPICARound4.grouped_zero_coefficient_rigidity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.grouped_zero_coefficient_rigidity"
#print axioms Zeta23.OPICARound4.grouped_zero_coefficient_rigidity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hermitian_det_star"
#check @Zeta23.OPICARound4.hermitian_det_star
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hermitian_det_star"
#print axioms Zeta23.OPICARound4.hermitian_det_star
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.integerNodePerturb"
#check @Zeta23.OPICARound4.integerNodePerturb
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.integerNodePerturb"
#print axioms Zeta23.OPICARound4.integerNodePerturb
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.integerNodePerturb_deriv"
#check @Zeta23.OPICARound4.integerNodePerturb_deriv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.integerNodePerturb_deriv"
#print axioms Zeta23.OPICARound4.integerNodePerturb_deriv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.integerNodePerturb_hasDerivAt"
#check @Zeta23.OPICARound4.integerNodePerturb_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.integerNodePerturb_hasDerivAt"
#print axioms Zeta23.OPICARound4.integerNodePerturb_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.integerNodePerturb_value"
#check @Zeta23.OPICARound4.integerNodePerturb_value
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.integerNodePerturb_value"
#print axioms Zeta23.OPICARound4.integerNodePerturb_value
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.integer_node_values_same_matrix_ne"
#check @Zeta23.OPICARound4.integer_node_values_same_matrix_ne
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.integer_node_values_same_matrix_ne"
#print axioms Zeta23.OPICARound4.integer_node_values_same_matrix_ne
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul"
#check @Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul"
#print axioms Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt"
#check @Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt"
#print axioms Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeAdaptiveTestClass"
#check @Zeta23.OPICARound4.nativeAdaptiveTestClass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeAdaptiveTestClass"
#print axioms Zeta23.OPICARound4.nativeAdaptiveTestClass
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeArchContinuumRow"
#check @Zeta23.OPICARound4.nativeArchContinuumRow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeArchContinuumRow"
#print axioms Zeta23.OPICARound4.nativeArchContinuumRow
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCompleteRowBudget"
#check @Zeta23.OPICARound4.nativeCompleteRowBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCompleteRowBudget"
#print axioms Zeta23.OPICARound4.nativeCompleteRowBudget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg"
#check @Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg"
#print axioms Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCorrectedVariation"
#check @Zeta23.OPICARound4.nativeCorrectedVariation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCorrectedVariation"
#print axioms Zeta23.OPICARound4.nativeCorrectedVariation
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCorrectedVariation_nonneg"
#check @Zeta23.OPICARound4.nativeCorrectedVariation_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCorrectedVariation_nonneg"
#print axioms Zeta23.OPICARound4.nativeCorrectedVariation_nonneg
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeEvenGroupedEigenvalue"
#check @Zeta23.OPICARound4.nativeEvenGroupedEigenvalue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeEvenGroupedEigenvalue"
#print axioms Zeta23.OPICARound4.nativeEvenGroupedEigenvalue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeEvenGroupedProjector"
#check @Zeta23.OPICARound4.nativeEvenGroupedProjector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeEvenGroupedProjector"
#print axioms Zeta23.OPICARound4.nativeEvenGroupedProjector
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeEvenGroupedResidue"
#check @Zeta23.OPICARound4.nativeEvenGroupedResidue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeEvenGroupedResidue"
#print axioms Zeta23.OPICARound4.nativeEvenGroupedResidue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeEvenObservation"
#check @Zeta23.OPICARound4.nativeEvenObservation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeEvenObservation"
#print axioms Zeta23.OPICARound4.nativeEvenObservation
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeLatePrimePowers"
#check @Zeta23.OPICARound4.nativeLatePrimePowers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeLatePrimePowers"
#print axioms Zeta23.OPICARound4.nativeLatePrimePowers
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddGroupedEigenvalue"
#check @Zeta23.OPICARound4.nativeOddGroupedEigenvalue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddGroupedEigenvalue"
#print axioms Zeta23.OPICARound4.nativeOddGroupedEigenvalue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddGroupedProjector"
#check @Zeta23.OPICARound4.nativeOddGroupedProjector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddGroupedProjector"
#print axioms Zeta23.OPICARound4.nativeOddGroupedProjector
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddGroupedResidue"
#check @Zeta23.OPICARound4.nativeOddGroupedResidue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddGroupedResidue"
#print axioms Zeta23.OPICARound4.nativeOddGroupedResidue
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddObservation"
#check @Zeta23.OPICARound4.nativeOddObservation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddObservation"
#print axioms Zeta23.OPICARound4.nativeOddObservation
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddReciprocalInput"
#check @Zeta23.OPICARound4.nativeOddReciprocalInput
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddReciprocalInput"
#print axioms Zeta23.OPICARound4.nativeOddReciprocalInput
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOldPrimePowers"
#check @Zeta23.OPICARound4.nativeOldPrimePowers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOldPrimePowers"
#print axioms Zeta23.OPICARound4.nativeOldPrimePowers
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativePrimeConcentrationBudget"
#check @Zeta23.OPICARound4.nativePrimeConcentrationBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativePrimeConcentrationBudget"
#print axioms Zeta23.OPICARound4.nativePrimeConcentrationBudget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativePrimeMass"
#check @Zeta23.OPICARound4.nativePrimeMass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativePrimeMass"
#print axioms Zeta23.OPICARound4.nativePrimeMass
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSinePotential"
#check @Zeta23.OPICARound4.nativeSinePotential
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSinePotential"
#print axioms Zeta23.OPICARound4.nativeSinePotential
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSinePotential_deriv"
#check @Zeta23.OPICARound4.nativeSinePotential_deriv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSinePotential_deriv"
#print axioms Zeta23.OPICARound4.nativeSinePotential_deriv
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSinePotential_hasDerivAt"
#check @Zeta23.OPICARound4.nativeSinePotential_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSinePotential_hasDerivAt"
#print axioms Zeta23.OPICARound4.nativeSinePotential_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom"
#check @Zeta23.OPICARound4.nativeSourceAtom
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom"
#print axioms Zeta23.OPICARound4.nativeSourceAtom
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_apply_norm"
#check @Zeta23.OPICARound4.nativeSourceAtom_apply_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_apply_norm"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_apply_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_norm_le_two"
#check @Zeta23.OPICARound4.nativeSourceAtom_norm_le_two
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_norm_le_two"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_norm_le_two
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_symmetric"
#check @Zeta23.OPICARound4.nativeSourceAtom_symmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_symmetric"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_symmetric
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_adaptive_complete_budget"
#check @Zeta23.OPICARound4.native_adaptive_complete_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_adaptive_complete_budget"
#print axioms Zeta23.OPICARound4.native_adaptive_complete_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_complete_concentration_budget"
#check @Zeta23.OPICARound4.native_complete_concentration_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_complete_concentration_budget"
#print axioms Zeta23.OPICARound4.native_complete_concentration_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_complete_row_budget"
#check @Zeta23.OPICARound4.native_complete_row_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_complete_row_budget"
#print axioms Zeta23.OPICARound4.native_complete_row_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_corrected_riesz_budget"
#check @Zeta23.OPICARound4.native_corrected_riesz_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_corrected_riesz_budget"
#print axioms Zeta23.OPICARound4.native_corrected_riesz_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_corrected_source_concentration_real_interval"
#check @Zeta23.OPICARound4.native_corrected_source_concentration_real_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_corrected_source_concentration_real_interval"
#print axioms Zeta23.OPICARound4.native_corrected_source_concentration_real_interval
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_complete_signed_budget"
#check @Zeta23.OPICARound4.native_even_complete_signed_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_complete_signed_budget"
#print axioms Zeta23.OPICARound4.native_even_complete_signed_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_grouped_residue_cast"
#check @Zeta23.OPICARound4.native_even_grouped_residue_cast
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_grouped_residue_cast"
#print axioms Zeta23.OPICARound4.native_even_grouped_residue_cast
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_grouped_resolvent_expansion"
#check @Zeta23.OPICARound4.native_even_grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_grouped_resolvent_expansion"
#print axioms Zeta23.OPICARound4.native_even_grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_invisible_gram"
#check @Zeta23.OPICARound4.native_even_invisible_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_invisible_gram"
#print axioms Zeta23.OPICARound4.native_even_invisible_gram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_visible_or_shared_mode"
#check @Zeta23.OPICARound4.native_even_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_visible_or_shared_mode"
#print axioms Zeta23.OPICARound4.native_even_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt"
#check @Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt"
#print axioms Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_frame_negative_physical_plane"
#check @Zeta23.OPICARound4.native_frame_negative_physical_plane
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_frame_negative_physical_plane"
#print axioms Zeta23.OPICARound4.native_frame_negative_physical_plane
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_inverse_adjoint_cost"
#check @Zeta23.OPICARound4.native_inverse_adjoint_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_inverse_adjoint_cost"
#print axioms Zeta23.OPICARound4.native_inverse_adjoint_cost
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_inverse_gap_norm"
#check @Zeta23.OPICARound4.native_inverse_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_inverse_gap_norm"
#print axioms Zeta23.OPICARound4.native_inverse_gap_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_late_mixed_concentration_cost"
#check @Zeta23.OPICARound4.native_late_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_late_mixed_concentration_cost"
#print axioms Zeta23.OPICARound4.native_late_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_late_prime_concentration"
#check @Zeta23.OPICARound4.native_late_prime_concentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_late_prime_concentration"
#print axioms Zeta23.OPICARound4.native_late_prime_concentration
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_observation_bound_excludes_invisible_even"
#check @Zeta23.OPICARound4.native_observation_bound_excludes_invisible_even
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_observation_bound_excludes_invisible_even"
#print axioms Zeta23.OPICARound4.native_observation_bound_excludes_invisible_even
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_adaptive_response_budget"
#check @Zeta23.OPICARound4.native_odd_adaptive_response_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_adaptive_response_budget"
#print axioms Zeta23.OPICARound4.native_odd_adaptive_response_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_complete_signed_budget"
#check @Zeta23.OPICARound4.native_odd_complete_signed_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_complete_signed_budget"
#print axioms Zeta23.OPICARound4.native_odd_complete_signed_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_concentration_real_interval"
#check @Zeta23.OPICARound4.native_odd_concentration_real_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_concentration_real_interval"
#print axioms Zeta23.OPICARound4.native_odd_concentration_real_interval
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_grouped_residue_cast"
#check @Zeta23.OPICARound4.native_odd_grouped_residue_cast
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_grouped_residue_cast"
#print axioms Zeta23.OPICARound4.native_odd_grouped_residue_cast
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion"
#check @Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion"
#print axioms Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_invisible_gram"
#check @Zeta23.OPICARound4.native_odd_invisible_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_invisible_gram"
#print axioms Zeta23.OPICARound4.native_odd_invisible_gram
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_rank_one_unshifted"
#check @Zeta23.OPICARound4.native_odd_rank_one_unshifted
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_rank_one_unshifted"
#print axioms Zeta23.OPICARound4.native_odd_rank_one_unshifted
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_complete_arithmetic"
#check @Zeta23.OPICARound4.native_odd_response_complete_arithmetic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_complete_arithmetic"
#print axioms Zeta23.OPICARound4.native_odd_response_complete_arithmetic
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source"
#check @Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source"
#print axioms Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget"
#check @Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget"
#print axioms Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor"
#check @Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor"
#print axioms Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_visible_or_shared_mode"
#check @Zeta23.OPICARound4.native_odd_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_visible_or_shared_mode"
#print axioms Zeta23.OPICARound4.native_odd_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_old_mixed_concentration_cost"
#check @Zeta23.OPICARound4.native_old_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_old_mixed_concentration_cost"
#print axioms Zeta23.OPICARound4.native_old_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_old_prime_concentration"
#check @Zeta23.OPICARound4.native_old_prime_concentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_old_prime_concentration"
#print axioms Zeta23.OPICARound4.native_old_prime_concentration
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_concentration_budget"
#check @Zeta23.OPICARound4.native_prime_concentration_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_concentration_budget"
#print axioms Zeta23.OPICARound4.native_prime_concentration_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback"
#check @Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback"
#print axioms Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_discrepancy_integral"
#check @Zeta23.OPICARound4.native_prime_discrepancy_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_discrepancy_integral"
#print axioms Zeta23.OPICARound4.native_prime_discrepancy_integral
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_half_coordinate_iff"
#check @Zeta23.OPICARound4.native_prime_half_coordinate_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_half_coordinate_iff"
#print axioms Zeta23.OPICARound4.native_prime_half_coordinate_iff
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_power_regime_partition"
#check @Zeta23.OPICARound4.native_prime_power_regime_partition
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_power_regime_partition"
#print axioms Zeta23.OPICARound4.native_prime_power_regime_partition
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_row_budget"
#check @Zeta23.OPICARound4.native_prime_row_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_row_budget"
#print axioms Zeta23.OPICARound4.native_prime_row_budget
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_real_shift_inverse_symmetric"
#check @Zeta23.OPICARound4.native_real_shift_inverse_symmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_real_shift_inverse_symmetric"
#print axioms Zeta23.OPICARound4.native_real_shift_inverse_symmetric
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_sine_nodeJet_eq_sourceEntryReal"
#check @Zeta23.OPICARound4.native_sine_nodeJet_eq_sourceEntryReal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_sine_nodeJet_eq_sourceEntryReal"
#print axioms Zeta23.OPICARound4.native_sine_nodeJet_eq_sourceEntryReal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_energy_eq_exchange_difference"
#check @Zeta23.OPICARound4.native_source_energy_eq_exchange_difference
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_energy_eq_exchange_difference"
#print axioms Zeta23.OPICARound4.native_source_energy_eq_exchange_difference
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_mixed_concentration_bound"
#check @Zeta23.OPICARound4.native_source_mixed_concentration_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_mixed_concentration_bound"
#print axioms Zeta23.OPICARound4.native_source_mixed_concentration_bound
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_mixed_norm"
#check @Zeta23.OPICARound4.native_source_mixed_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_mixed_norm"
#print axioms Zeta23.OPICARound4.native_source_mixed_norm
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_selected_membership"
#check @Zeta23.OPICARound4.native_source_selected_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_selected_membership"
#print axioms Zeta23.OPICARound4.native_source_selected_membership
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_square_concentration_full"
#check @Zeta23.OPICARound4.native_source_square_concentration_full
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_square_concentration_full"
#print axioms Zeta23.OPICARound4.native_source_square_concentration_full
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_square_concentration_half"
#check @Zeta23.OPICARound4.native_source_square_concentration_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_square_concentration_half"
#print axioms Zeta23.OPICARound4.native_source_square_concentration_half
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.negativeAtomEmbedding"
#check @Zeta23.OPICARound4.negativeAtomEmbedding
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.negativeAtomEmbedding"
#print axioms Zeta23.OPICARound4.negativeAtomEmbedding
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.negativeAtomEmbedding_injective"
#check @Zeta23.OPICARound4.negativeAtomEmbedding_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.negativeAtomEmbedding_injective"
#print axioms Zeta23.OPICARound4.negativeAtomEmbedding_injective
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt"
#check @Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt"
#print axioms Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.noBothNeg_of_actual_ground_comparisons"
#check @Zeta23.OPICARound4.noBothNeg_of_actual_ground_comparisons
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.noBothNeg_of_actual_ground_comparisons"
#print axioms Zeta23.OPICARound4.noBothNeg_of_actual_ground_comparisons
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons"
#check @Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons"
#print axioms Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.noBothNeg_of_ground_restrictions"
#check @Zeta23.OPICARound4.noBothNeg_of_ground_restrictions
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.noBothNeg_of_ground_restrictions"
#print axioms Zeta23.OPICARound4.noBothNeg_of_ground_restrictions
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.noBothNeg_of_research_targets"
#check @Zeta23.OPICARound4.noBothNeg_of_research_targets
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.noBothNeg_of_research_targets"
#print axioms Zeta23.OPICARound4.noBothNeg_of_research_targets
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure"
#check @Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure"
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_off_line_zero_of_eventual_ground_closure"
#check @Zeta23.OPICARound4.no_off_line_zero_of_eventual_ground_closure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_off_line_zero_of_eventual_ground_closure"
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_ground_closure
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index"
#check @Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index"
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.no_off_line_zero_of_eventual_noBothNeg"
#check @Zeta23.OPICARound4.no_off_line_zero_of_eventual_noBothNeg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.no_off_line_zero_of_eventual_noBothNeg"
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_noBothNeg
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nodeJetMatrix"
#check @Zeta23.OPICARound4.nodeJetMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nodeJetMatrix"
#print axioms Zeta23.OPICARound4.nodeJetMatrix
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nodeJetMatrix_diagonal"
#check @Zeta23.OPICARound4.nodeJetMatrix_diagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nodeJetMatrix_diagonal"
#print axioms Zeta23.OPICARound4.nodeJetMatrix_diagonal
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets"
#check @Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets"
#print axioms Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.observationBlindSubspace"
#check @Zeta23.OPICARound4.observationBlindSubspace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.observationBlindSubspace"
#print axioms Zeta23.OPICARound4.observationBlindSubspace
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.observationBlindSubspace_invariant"
#check @Zeta23.OPICARound4.observationBlindSubspace_invariant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.observationBlindSubspace_invariant"
#print axioms Zeta23.OPICARound4.observationBlindSubspace_invariant
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.observationBlindSubspace_mem"
#check @Zeta23.OPICARound4.observationBlindSubspace_mem
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.observationBlindSubspace_mem"
#print axioms Zeta23.OPICARound4.observationBlindSubspace_mem
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.odd_negative_ground_restriction_of_all_ray"
#check @Zeta23.OPICARound4.odd_negative_ground_restriction_of_all_ray
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.odd_negative_ground_restriction_of_all_ray"
#print axioms Zeta23.OPICARound4.odd_negative_ground_restriction_of_all_ray
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.primeSourceCoordinate_mem_unit"
#check @Zeta23.OPICARound4.primeSourceCoordinate_mem_unit
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.primeSourceCoordinate_mem_unit"
#print axioms Zeta23.OPICARound4.primeSourceCoordinate_mem_unit
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_discrepancy_log_integral"
#check @Zeta23.OPICARound4.prime_discrepancy_log_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_discrepancy_log_integral"
#print axioms Zeta23.OPICARound4.prime_discrepancy_log_integral
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_log_abel"
#check @Zeta23.OPICARound4.prime_log_abel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_log_abel"
#print axioms Zeta23.OPICARound4.prime_log_abel
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_log_mem_interval"
#check @Zeta23.OPICARound4.prime_log_mem_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_log_mem_interval"
#print axioms Zeta23.OPICARound4.prime_log_mem_interval
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.psi_eq_sum_Icc_two"
#check @Zeta23.OPICARound4.psi_eq_sum_Icc_two
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.psi_eq_sum_Icc_two"
#print axioms Zeta23.OPICARound4.psi_eq_sum_Icc_two
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.psi_exp_eq_sum_steps"
#check @Zeta23.OPICARound4.psi_exp_eq_sum_steps
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.psi_exp_eq_sum_steps"
#print axioms Zeta23.OPICARound4.psi_exp_eq_sum_steps
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity"
#check @Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity"
#print axioms Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.rank_one_visible_or_shared_mode"
#check @Zeta23.OPICARound4.rank_one_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.rank_one_visible_or_shared_mode"
#print axioms Zeta23.OPICARound4.rank_one_visible_or_shared_mode
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.reachable_subspace_in_output_kernel"
#check @Zeta23.OPICARound4.reachable_subspace_in_output_kernel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.reachable_subspace_in_output_kernel"
#print axioms Zeta23.OPICARound4.reachable_subspace_in_output_kernel
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.real_sub_upper_ne_zero"
#check @Zeta23.OPICARound4.real_sub_upper_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.real_sub_upper_ne_zero"
#print axioms Zeta23.OPICARound4.real_sub_upper_ne_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signedCauchyEvaluation"
#check @Zeta23.OPICARound4.signedCauchyEvaluation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signedCauchyEvaluation"
#print axioms Zeta23.OPICARound4.signedCauchyEvaluation
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signedCauchyLinearMap"
#check @Zeta23.OPICARound4.signedCauchyLinearMap
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signedCauchyLinearMap"
#print axioms Zeta23.OPICARound4.signedCauchyLinearMap
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.signedPickKernel"
#check @Zeta23.OPICARound4.signedPickKernel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.signedPickKernel"
#print axioms Zeta23.OPICARound4.signedPickKernel
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration"
#check @Zeta23.OPICARound4.sourceConcentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration"
#print axioms Zeta23.OPICARound4.sourceConcentration
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus"
#check @Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus"
#print axioms Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half"
#check @Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half"
#print axioms Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq"
#check @Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq"
#print axioms Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_nonneg"
#check @Zeta23.OPICARound4.sourceConcentration_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_nonneg"
#print axioms Zeta23.OPICARound4.sourceConcentration_nonneg
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMinus"
#check @Zeta23.OPICARound4.sourceExchangeMinus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMinus"
#print axioms Zeta23.OPICARound4.sourceExchangeMinus
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed"
#check @Zeta23.OPICARound4.sourceExchangeMixed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_eq_native"
#check @Zeta23.OPICARound4.sourceExchangeMixed_eq_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_eq_native"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_eq_native
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le"
#check @Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native"
#check @Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangePlus"
#check @Zeta23.OPICARound4.sourceExchangePlus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangePlus"
#print axioms Zeta23.OPICARound4.sourceExchangePlus
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchange_nonneg"
#check @Zeta23.OPICARound4.sourceExchange_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchange_nonneg"
#print axioms Zeta23.OPICARound4.sourceExchange_nonneg
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier"
#check @Zeta23.OPICARound4.sourceFiniteFourier
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier_continuous"
#check @Zeta23.OPICARound4.sourceFiniteFourier_continuous
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier_continuous"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier_continuous
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp"
#check @Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sum_groupedSpectralProjector"
#check @Zeta23.OPICARound4.sum_groupedSpectralProjector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sum_groupedSpectralProjector"
#print axioms Zeta23.OPICARound4.sum_groupedSpectralProjector
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.upper_sub_conj_ne_zero"
#check @Zeta23.OPICARound4.upper_sub_conj_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.upper_sub_conj_ne_zero"
#print axioms Zeta23.OPICARound4.upper_sub_conj_ne_zero
#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.zero_residue_does_not_remove_eigenspace"
#check @Zeta23.OPICARound4.zero_residue_does_not_remove_eigenspace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.zero_residue_does_not_remove_eigenspace"
#print axioms Zeta23.OPICARound4.zero_residue_does_not_remove_eigenspace

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSignedPrimeDiscrepancy"
#check @Zeta23.OPICARound4.nativeSignedPrimeDiscrepancy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSignedPrimeDiscrepancy"
#print axioms Zeta23.OPICARound4.nativeSignedPrimeDiscrepancy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeGroundArchPairing"
#check @Zeta23.OPICARound4.nativeGroundArchPairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeGroundArchPairing"
#print axioms Zeta23.OPICARound4.nativeGroundArchPairing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeGroundPrimePairing"
#check @Zeta23.OPICARound4.nativeGroundPrimePairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeGroundPrimePairing"
#print axioms Zeta23.OPICARound4.nativeGroundPrimePairing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_signed_source_decomposition"
#check @Zeta23.OPICARound4.native_signed_source_decomposition
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_signed_source_decomposition"
#print axioms Zeta23.OPICARound4.native_signed_source_decomposition

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_signed_discrepancy_integral"
#check @Zeta23.OPICARound4.native_signed_discrepancy_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_signed_discrepancy_integral"
#print axioms Zeta23.OPICARound4.native_signed_discrepancy_integral

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ground_ray_facts"
#check @Zeta23.OPICARound4.actual_even_ground_ray_facts
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ground_ray_facts"
#print axioms Zeta23.OPICARound4.actual_even_ground_ray_facts

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_ground_ray_facts"
#check @Zeta23.OPICARound4.actual_odd_ground_ray_facts
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_ground_ray_facts"
#print axioms Zeta23.OPICARound4.actual_odd_ground_ray_facts

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ground_signed_discrepancy"
#check @Zeta23.OPICARound4.actual_even_ground_signed_discrepancy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ground_signed_discrepancy"
#print axioms Zeta23.OPICARound4.actual_even_ground_signed_discrepancy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_ground_reciprocal_discrepancy"
#check @Zeta23.OPICARound4.actual_odd_ground_reciprocal_discrepancy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_ground_reciprocal_discrepancy"
#print axioms Zeta23.OPICARound4.actual_odd_ground_reciprocal_discrepancy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ground_signed_budget_feasibility"
#check @Zeta23.OPICARound4.actual_even_ground_signed_budget_feasibility
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ground_signed_budget_feasibility"
#print axioms Zeta23.OPICARound4.actual_even_ground_signed_budget_feasibility

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_ground_signed_budget_feasibility"
#check @Zeta23.OPICARound4.actual_odd_ground_signed_budget_feasibility
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_ground_signed_budget_feasibility"
#print axioms Zeta23.OPICARound4.actual_odd_ground_signed_budget_feasibility

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ground_ray_moment_feasibility"
#check @Zeta23.OPICARound4.actual_even_ground_ray_moment_feasibility
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ground_ray_moment_feasibility"
#print axioms Zeta23.OPICARound4.actual_even_ground_ray_moment_feasibility

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_eigen_absolute_energy"
#check @Zeta23.OPICARound4.native_even_eigen_absolute_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_eigen_absolute_energy"
#print axioms Zeta23.OPICARound4.native_even_eigen_absolute_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_eigen_absolute_energy"
#check @Zeta23.OPICARound4.native_odd_eigen_absolute_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_eigen_absolute_energy"
#print axioms Zeta23.OPICARound4.native_odd_eigen_absolute_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeStrictEvenGroundConstraints"
#check @Zeta23.OPICARound4.NativeStrictEvenGroundConstraints
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeStrictEvenGroundConstraints"
#print axioms Zeta23.OPICARound4.NativeStrictEvenGroundConstraints

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeStrictEvenGroundConstraints.mk"
#check @Zeta23.OPICARound4.NativeStrictEvenGroundConstraints.mk
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeStrictEvenGroundConstraints.mk"
#print axioms Zeta23.OPICARound4.NativeStrictEvenGroundConstraints.mk

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeStrictOddGroundConstraints"
#check @Zeta23.OPICARound4.NativeStrictOddGroundConstraints
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeStrictOddGroundConstraints"
#print axioms Zeta23.OPICARound4.NativeStrictOddGroundConstraints

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeStrictOddGroundConstraints.mk"
#check @Zeta23.OPICARound4.NativeStrictOddGroundConstraints.mk
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeStrictOddGroundConstraints.mk"
#print axioms Zeta23.OPICARound4.NativeStrictOddGroundConstraints.mk

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeTiedGroundConstraints"
#check @Zeta23.OPICARound4.NativeTiedGroundConstraints
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeTiedGroundConstraints"
#print axioms Zeta23.OPICARound4.NativeTiedGroundConstraints

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeTiedGroundConstraints.mk"
#check @Zeta23.OPICARound4.NativeTiedGroundConstraints.mk
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeTiedGroundConstraints.mk"
#print axioms Zeta23.OPICARound4.NativeTiedGroundConstraints.mk

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeJointGroundConstraints"
#check @Zeta23.OPICARound4.NativeJointGroundConstraints
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeJointGroundConstraints"
#print axioms Zeta23.OPICARound4.NativeJointGroundConstraints

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_tied_ground_constraints"
#check @Zeta23.OPICARound4.native_tied_ground_constraints
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_tied_ground_constraints"
#print axioms Zeta23.OPICARound4.native_tied_ground_constraints

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.joint_ground_constraints_of_both_negative"
#check @Zeta23.OPICARound4.joint_ground_constraints_of_both_negative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.joint_ground_constraints_of_both_negative"
#print axioms Zeta23.OPICARound4.joint_ground_constraints_of_both_negative

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.cofinally_joint_ground_constraints_of_off_line_zero"
#check @Zeta23.OPICARound4.cofinally_joint_ground_constraints_of_off_line_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.cofinally_joint_ground_constraints_of_off_line_zero"
#print axioms Zeta23.OPICARound4.cofinally_joint_ground_constraints_of_off_line_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceImageErrorBudget"
#check @Zeta23.OPICARound4.sourceImageErrorBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceImageErrorBudget"
#print axioms Zeta23.OPICARound4.sourceImageErrorBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteModeCost"
#check @Zeta23.OPICARound4.sourceFiniteModeCost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteModeCost"
#print axioms Zeta23.OPICARound4.sourceFiniteModeCost

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingErrorBudget"
#check @Zeta23.OPICARound4.sourceForcingErrorBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingErrorBudget"
#print axioms Zeta23.OPICARound4.sourceForcingErrorBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceWeilBoundConstant"
#check @Zeta23.OPICARound4.sourceWeilBoundConstant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceWeilBoundConstant"
#print axioms Zeta23.OPICARound4.sourceWeilBoundConstant

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceWeilBoundConstant_pos"
#check @Zeta23.OPICARound4.sourceWeilBoundConstant_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceWeilBoundConstant_pos"
#print axioms Zeta23.OPICARound4.sourceWeilBoundConstant_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteForcingBudget"
#check @Zeta23.OPICARound4.finiteForcingBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteForcingBudget"
#print axioms Zeta23.OPICARound4.finiteForcingBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceImageErrorBudget_nonneg"
#check @Zeta23.OPICARound4.sourceImageErrorBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceImageErrorBudget_nonneg"
#print axioms Zeta23.OPICARound4.sourceImageErrorBudget_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.source_eta_nonneg"
#check @Zeta23.OPICARound4.source_eta_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.source_eta_nonneg"
#print axioms Zeta23.OPICARound4.source_eta_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingErrorBudget_nonneg"
#check @Zeta23.OPICARound4.sourceForcingErrorBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingErrorBudget_nonneg"
#print axioms Zeta23.OPICARound4.sourceForcingErrorBudget_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteForcingBudget_nonneg"
#check @Zeta23.OPICARound4.finiteForcingBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteForcingBudget_nonneg"
#print axioms Zeta23.OPICARound4.finiteForcingBudget_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceL2"
#check @Zeta23.OPICARound4.smoothSourceL2
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceL2"
#print axioms Zeta23.OPICARound4.smoothSourceL2

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceL2_ae"
#check @Zeta23.OPICARound4.smoothSourceL2_ae
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceL2_ae"
#print axioms Zeta23.OPICARound4.smoothSourceL2_ae

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceResponseL2"
#check @Zeta23.OPICARound4.smoothSourceResponseL2
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceResponseL2"
#print axioms Zeta23.OPICARound4.smoothSourceResponseL2

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceResponseL2_ae"
#check @Zeta23.OPICARound4.smoothSourceResponseL2_ae
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceResponseL2_ae"
#print axioms Zeta23.OPICARound4.smoothSourceResponseL2_ae

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing"
#check @Zeta23.OPICARound4.smoothSourceForcing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing"
#print axioms Zeta23.OPICARound4.smoothSourceForcing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing_pairing"
#check @Zeta23.OPICARound4.smoothSourceForcing_pairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing_pairing"
#print axioms Zeta23.OPICARound4.smoothSourceForcing_pairing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing_error_pairing"
#check @Zeta23.OPICARound4.smoothSourceForcing_error_pairing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing_error_pairing"
#print axioms Zeta23.OPICARound4.smoothSourceForcing_error_pairing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing_channels"
#check @Zeta23.OPICARound4.smoothSourceForcing_channels
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing_channels"
#print axioms Zeta23.OPICARound4.smoothSourceForcing_channels

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.norm_le_of_all_inner_bound"
#check @Zeta23.OPICARound4.norm_le_of_all_inner_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.norm_le_of_all_inner_bound"
#print axioms Zeta23.OPICARound4.norm_le_of_all_inner_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing_error_bound"
#check @Zeta23.OPICARound4.smoothSourceForcing_error_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing_error_bound"
#print axioms Zeta23.OPICARound4.smoothSourceForcing_error_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteForcing_norm_bound"
#check @Zeta23.OPICARound4.finiteForcing_norm_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteForcing_norm_bound"
#print axioms Zeta23.OPICARound4.finiteForcing_norm_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceForcing_norm_bound"
#check @Zeta23.OPICARound4.smoothSourceForcing_norm_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceForcing_norm_bound"
#print axioms Zeta23.OPICARound4.smoothSourceForcing_norm_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourcePhysicalL2_norm_eq"
#check @Zeta23.OPICARound4.sourcePhysicalL2_norm_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourcePhysicalL2_norm_eq"
#print axioms Zeta23.OPICARound4.sourcePhysicalL2_norm_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceL2_error_bound"
#check @Zeta23.OPICARound4.smoothSourceL2_error_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceL2_error_bound"
#print axioms Zeta23.OPICARound4.smoothSourceL2_error_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceL2_norm_bound"
#check @Zeta23.OPICARound4.smoothSourceL2_norm_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceL2_norm_bound"
#print axioms Zeta23.OPICARound4.smoothSourceL2_norm_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorInverse"
#check @Zeta23.OPICARound4.detectorInverse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorInverse"
#print axioms Zeta23.OPICARound4.detectorInverse

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceInverseBudget"
#check @Zeta23.OPICARound4.sourceInverseBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceInverseBudget"
#print axioms Zeta23.OPICARound4.sourceInverseBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorSchurLoss"
#check @Zeta23.OPICARound4.detectorSchurLoss
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorSchurLoss"
#print axioms Zeta23.OPICARound4.detectorSchurLoss

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteSourceEnergy"
#check @Zeta23.OPICARound4.finiteSourceEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteSourceEnergy"
#print axioms Zeta23.OPICARound4.finiteSourceEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceMain"
#check @Zeta23.OPICARound4.smoothSourceMain
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceMain"
#print axioms Zeta23.OPICARound4.smoothSourceMain

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceEnergyErrorBudget"
#check @Zeta23.OPICARound4.sourceEnergyErrorBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceEnergyErrorBudget"
#print axioms Zeta23.OPICARound4.sourceEnergyErrorBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceSchurErrorBudget"
#check @Zeta23.OPICARound4.sourceSchurErrorBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceSchurErrorBudget"
#print axioms Zeta23.OPICARound4.sourceSchurErrorBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorInverse_norm_bound"
#check @Zeta23.OPICARound4.detectorInverse_norm_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorInverse_norm_bound"
#print axioms Zeta23.OPICARound4.detectorInverse_norm_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceInverseBudget_nonneg"
#check @Zeta23.OPICARound4.sourceInverseBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceInverseBudget_nonneg"
#print axioms Zeta23.OPICARound4.sourceInverseBudget_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorSchurLoss_lower"
#check @Zeta23.OPICARound4.detectorSchurLoss_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorSchurLoss_lower"
#print axioms Zeta23.OPICARound4.detectorSchurLoss_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorSchurLoss_eq_forcing_energy"
#check @Zeta23.OPICARound4.detectorSchurLoss_eq_forcing_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorSchurLoss_eq_forcing_energy"
#print axioms Zeta23.OPICARound4.detectorSchurLoss_eq_forcing_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceQuadratic_perturbation_bound"
#check @Zeta23.OPICARound4.sourceQuadratic_perturbation_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceQuadratic_perturbation_bound"
#print axioms Zeta23.OPICARound4.sourceQuadratic_perturbation_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.smoothSourceL2_mass_error_bound"
#check @Zeta23.OPICARound4.smoothSourceL2_mass_error_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.smoothSourceL2_mass_error_bound"
#print axioms Zeta23.OPICARound4.smoothSourceL2_mass_error_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorSchurLoss_sub_smoothSourceMain_bound"
#check @Zeta23.OPICARound4.detectorSchurLoss_sub_smoothSourceMain_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorSchurLoss_sub_smoothSourceMain_bound"
#print axioms Zeta23.OPICARound4.detectorSchurLoss_sub_smoothSourceMain_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorForcing_zero_at_first"
#check @Zeta23.OPICARound4.detectorForcing_zero_at_first
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorForcing_zero_at_first"
#print axioms Zeta23.OPICARound4.detectorForcing_zero_at_first

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detectorSchurLoss_at_first"
#check @Zeta23.OPICARound4.detectorSchurLoss_at_first
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detectorSchurLoss_at_first"
#print axioms Zeta23.OPICARound4.detectorSchurLoss_at_first

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quartic_polynomial_exp_tendsto_zero"
#check @Zeta23.OPICARound4.quartic_polynomial_exp_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quartic_polynomial_exp_tendsto_zero"
#print axioms Zeta23.OPICARound4.quartic_polynomial_exp_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticImageError"
#check @Zeta23.OPICARound4.quarticImageError
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticImageError"
#print axioms Zeta23.OPICARound4.quarticImageError

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticImageError_nonneg"
#check @Zeta23.OPICARound4.quarticImageError_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticImageError_nonneg"
#print axioms Zeta23.OPICARound4.quarticImageError_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticImageError_mul_exp_tendsto_zero"
#check @Zeta23.OPICARound4.quarticImageError_mul_exp_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticImageError_mul_exp_tendsto_zero"
#print axioms Zeta23.OPICARound4.quarticImageError_mul_exp_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.pow_mul_exp_mul_quarticImageError_tendsto_zero"
#check @Zeta23.OPICARound4.pow_mul_exp_mul_quarticImageError_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.pow_mul_exp_mul_quarticImageError_tendsto_zero"
#print axioms Zeta23.OPICARound4.pow_mul_exp_mul_quarticImageError_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticCutoff_le_two_pow_four"
#check @Zeta23.OPICARound4.quarticCutoff_le_two_pow_four
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticCutoff_le_two_pow_four"
#print axioms Zeta23.OPICARound4.quarticCutoff_le_two_pow_four

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quartic_mode_cost_le"
#check @Zeta23.OPICARound4.quartic_mode_cost_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quartic_mode_cost_le"
#print axioms Zeta23.OPICARound4.quartic_mode_cost_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticErrorEnvelope"
#check @Zeta23.OPICARound4.quarticErrorEnvelope
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticErrorEnvelope"
#print axioms Zeta23.OPICARound4.quarticErrorEnvelope

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticErrorEnvelope_nonneg"
#check @Zeta23.OPICARound4.quarticErrorEnvelope_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticErrorEnvelope_nonneg"
#print axioms Zeta23.OPICARound4.quarticErrorEnvelope_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticErrorEnvelope_mul_exp_tendsto_zero"
#check @Zeta23.OPICARound4.quarticErrorEnvelope_mul_exp_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticErrorEnvelope_mul_exp_tendsto_zero"
#print axioms Zeta23.OPICARound4.quarticErrorEnvelope_mul_exp_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.quarticErrorEnvelope_eventually_lt_exp"
#check @Zeta23.OPICARound4.quarticErrorEnvelope_eventually_lt_exp
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.quarticErrorEnvelope_eventually_lt_exp"
#print axioms Zeta23.OPICARound4.quarticErrorEnvelope_eventually_lt_exp

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceEtaGrowthConstant"
#check @Zeta23.OPICARound4.sourceEtaGrowthConstant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceEtaGrowthConstant"
#print axioms Zeta23.OPICARound4.sourceEtaGrowthConstant

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceEtaGrowthConstant_pos"
#check @Zeta23.OPICARound4.sourceEtaGrowthConstant_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceEtaGrowthConstant_pos"
#print axioms Zeta23.OPICARound4.sourceEtaGrowthConstant_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.source_eta_polynomial_bound"
#check @Zeta23.OPICARound4.source_eta_polynomial_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.source_eta_polynomial_bound"
#print axioms Zeta23.OPICARound4.source_eta_polynomial_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.detector_inverse_polynomial_bound"
#check @Zeta23.OPICARound4.detector_inverse_polynomial_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.detector_inverse_polynomial_bound"
#print axioms Zeta23.OPICARound4.detector_inverse_polynomial_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingGrowthConstant"
#check @Zeta23.OPICARound4.sourceForcingGrowthConstant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingGrowthConstant"
#print axioms Zeta23.OPICARound4.sourceForcingGrowthConstant

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingErrorGrowthConstant"
#check @Zeta23.OPICARound4.sourceForcingErrorGrowthConstant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingErrorGrowthConstant"
#print axioms Zeta23.OPICARound4.sourceForcingErrorGrowthConstant

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingGrowthConstant_pos"
#check @Zeta23.OPICARound4.sourceForcingGrowthConstant_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingGrowthConstant_pos"
#print axioms Zeta23.OPICARound4.sourceForcingGrowthConstant_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingErrorGrowthConstant_pos"
#check @Zeta23.OPICARound4.sourceForcingErrorGrowthConstant_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingErrorGrowthConstant_pos"
#print axioms Zeta23.OPICARound4.sourceForcingErrorGrowthConstant_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteForcingBudget_polynomial_bound"
#check @Zeta23.OPICARound4.finiteForcingBudget_polynomial_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteForcingBudget_polynomial_bound"
#print axioms Zeta23.OPICARound4.finiteForcingBudget_polynomial_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceForcingErrorBudget_polynomial_bound"
#check @Zeta23.OPICARound4.sourceForcingErrorBudget_polynomial_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceForcingErrorBudget_polynomial_bound"
#print axioms Zeta23.OPICARound4.sourceForcingErrorBudget_polynomial_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceSchurUniformEnvelope"
#check @Zeta23.OPICARound4.sourceSchurUniformEnvelope
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceSchurUniformEnvelope"
#print axioms Zeta23.OPICARound4.sourceSchurUniformEnvelope

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceSchurErrorBudget_le_uniformEnvelope"
#check @Zeta23.OPICARound4.sourceSchurErrorBudget_le_uniformEnvelope
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceSchurErrorBudget_le_uniformEnvelope"
#print axioms Zeta23.OPICARound4.sourceSchurErrorBudget_le_uniformEnvelope

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceSchurUniformEnvelope_mul_exp_tendsto_zero"
#check @Zeta23.OPICARound4.sourceSchurUniformEnvelope_mul_exp_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceSchurUniformEnvelope_mul_exp_tendsto_zero"
#print axioms Zeta23.OPICARound4.sourceSchurUniformEnvelope_mul_exp_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_uniform_source_schur_error_threshold"
#check @Zeta23.OPICARound4.exists_uniform_source_schur_error_threshold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_uniform_source_schur_error_threshold"
#print axioms Zeta23.OPICARound4.exists_uniform_source_schur_error_threshold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_uniform_smooth_source_main_lower_threshold"
#check @Zeta23.OPICARound4.exists_uniform_smooth_source_main_lower_threshold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_uniform_smooth_source_main_lower_threshold"
#print axioms Zeta23.OPICARound4.exists_uniform_smooth_source_main_lower_threshold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_generated_smooth_source_main_lower_threshold"
#check @Zeta23.OPICARound4.exists_generated_smooth_source_main_lower_threshold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_generated_smooth_source_main_lower_threshold"
#print axioms Zeta23.OPICARound4.exists_generated_smooth_source_main_lower_threshold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_smooth_source_forcing"
#check @Zeta23.OPICARound4.validation_smooth_source_forcing
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_smooth_source_forcing"
#print axioms Zeta23.OPICARound4.validation_smooth_source_forcing

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_detector_schur_error"
#check @Zeta23.OPICARound4.validation_detector_schur_error
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_detector_schur_error"
#print axioms Zeta23.OPICARound4.validation_detector_schur_error

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_detector_first_cutoff"
#check @Zeta23.OPICARound4.validation_detector_first_cutoff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_detector_first_cutoff"
#print axioms Zeta23.OPICARound4.validation_detector_first_cutoff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.quartic_rate_consumer"
#check @Zeta23.OPICARound4.Validation.quartic_rate_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.quartic_rate_consumer"
#print axioms Zeta23.OPICARound4.Validation.quartic_rate_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.source_shift_consumer"
#check @Zeta23.OPICARound4.Validation.source_shift_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.source_shift_consumer"
#print axioms Zeta23.OPICARound4.Validation.source_shift_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.same_detector_inverse_consumer"
#check @Zeta23.OPICARound4.Validation.same_detector_inverse_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.same_detector_inverse_consumer"
#print axioms Zeta23.OPICARound4.Validation.same_detector_inverse_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.complete_error_envelope_consumer"
#check @Zeta23.OPICARound4.Validation.complete_error_envelope_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.complete_error_envelope_consumer"
#print axioms Zeta23.OPICARound4.Validation.complete_error_envelope_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.all_exponential_rates_consumer"
#check @Zeta23.OPICARound4.Validation.all_exponential_rates_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.all_exponential_rates_consumer"
#print axioms Zeta23.OPICARound4.Validation.all_exponential_rates_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.threshold_before_packet_consumer"
#check @Zeta23.OPICARound4.Validation.threshold_before_packet_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.threshold_before_packet_consumer"
#print axioms Zeta23.OPICARound4.Validation.threshold_before_packet_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_packet_lower_consumer"
#check @Zeta23.OPICARound4.Validation.native_packet_lower_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_packet_lower_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_packet_lower_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.generated_packet_lower_consumer"
#check @Zeta23.OPICARound4.Validation.generated_packet_lower_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.generated_packet_lower_consumer"
#print axioms Zeta23.OPICARound4.Validation.generated_packet_lower_consumer
