import Zeta23.OPICARound4.ArithmeticFrontier.Validation.Carriers
import Zeta23.OPICARound4.Validation.NativeNoncollision
import Zeta23.OPICARound4.Validation.NativeGroundRegularity
import Zeta23.OPICARound4.Validation.JointGround
import Zeta23.OPICARound4.Validation.Hyperbola
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

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusR"
#check @Zeta23.OPICARound4.mobiusR
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusR"
#print axioms Zeta23.OPICARound4.mobiusR

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.arithmetic_sub_apply"
#check @Zeta23.OPICARound4.arithmetic_sub_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.arithmetic_sub_apply"
#print axioms Zeta23.OPICARound4.arithmetic_sub_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.weighted_convolution"
#check @Zeta23.OPICARound4.weighted_convolution
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.weighted_convolution"
#print axioms Zeta23.OPICARound4.weighted_convolution

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.weighted_mobius_inverse"
#check @Zeta23.OPICARound4.weighted_mobius_inverse
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.weighted_mobius_inverse"
#print axioms Zeta23.OPICARound4.weighted_mobius_inverse

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.arithmeticTruncation"
#check @Zeta23.OPICARound4.arithmeticTruncation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.arithmeticTruncation"
#print axioms Zeta23.OPICARound4.arithmeticTruncation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.arithmeticTruncation_apply"
#check @Zeta23.OPICARound4.arithmeticTruncation_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.arithmeticTruncation_apply"
#print axioms Zeta23.OPICARound4.arithmeticTruncation_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.arithmeticTruncation_sum"
#check @Zeta23.OPICARound4.arithmeticTruncation_sum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.arithmeticTruncation_sum"
#print axioms Zeta23.OPICARound4.arithmeticTruncation_sum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.tail_square_vanishes"
#check @Zeta23.OPICARound4.tail_square_vanishes
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.tail_square_vanishes"
#print axioms Zeta23.OPICARound4.tail_square_vanishes

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.tail_square_convolution_vanishes"
#check @Zeta23.OPICARound4.tail_square_convolution_vanishes
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.tail_square_convolution_vanishes"
#print axioms Zeta23.OPICARound4.tail_square_convolution_vanishes

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobius_hyperbola_coefficient"
#check @Zeta23.OPICARound4.mobius_hyperbola_coefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobius_hyperbola_coefficient"
#print axioms Zeta23.OPICARound4.mobius_hyperbola_coefficient

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.weighted_triple_convolution"
#check @Zeta23.OPICARound4.weighted_triple_convolution
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.weighted_triple_convolution"
#print axioms Zeta23.OPICARound4.weighted_triple_convolution

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaU"
#check @Zeta23.OPICARound4.hyperbolaU
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaU"
#print axioms Zeta23.OPICARound4.hyperbolaU

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaE"
#check @Zeta23.OPICARound4.hyperbolaE
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaE"
#print axioms Zeta23.OPICARound4.hyperbolaE

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaT"
#check @Zeta23.OPICARound4.hyperbolaT
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaT"
#print axioms Zeta23.OPICARound4.hyperbolaT

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.truncated_convolution_is_hyperbolaT"
#check @Zeta23.OPICARound4.truncated_convolution_is_hyperbolaT
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.truncated_convolution_is_hyperbolaT"
#print axioms Zeta23.OPICARound4.truncated_convolution_is_hyperbolaT

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_mobius_hyperbola"
#check @Zeta23.OPICARound4.finite_mobius_hyperbola
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_mobius_hyperbola"
#print axioms Zeta23.OPICARound4.finite_mobius_hyperbola

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteLogarithmicTest"
#check @Zeta23.OPICARound4.finiteLogarithmicTest
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteLogarithmicTest"
#print axioms Zeta23.OPICARound4.finiteLogarithmicTest

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteLogarithmicTest_support"
#check @Zeta23.OPICARound4.finiteLogarithmicTest_support
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteLogarithmicTest_support"
#print axioms Zeta23.OPICARound4.finiteLogarithmicTest_support

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU"
#check @Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU"
#print axioms Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_vonMangoldt_hyperbola"
#check @Zeta23.OPICARound4.finite_vonMangoldt_hyperbola
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_vonMangoldt_hyperbola"
#print axioms Zeta23.OPICARound4.finite_vonMangoldt_hyperbola

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaT_one"
#check @Zeta23.OPICARound4.hyperbolaT_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaT_one"
#print axioms Zeta23.OPICARound4.hyperbolaT_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaT_negative_test"
#check @Zeta23.OPICARound4.hyperbolaT_negative_test
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaT_negative_test"
#print axioms Zeta23.OPICARound4.hyperbolaT_negative_test

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finiteLogarithmicTest_half_support"
#check @Zeta23.OPICARound4.finiteLogarithmicTest_half_support
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finiteLogarithmicTest_half_support"
#print axioms Zeta23.OPICARound4.finiteLogarithmicTest_half_support

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.hyperbolaU_shrink"
#check @Zeta23.OPICARound4.hyperbolaU_shrink
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.hyperbolaU_shrink"
#print axioms Zeta23.OPICARound4.hyperbolaU_shrink

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half"
#check @Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half"
#print axioms Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationKernel"
#check @Zeta23.OPICARound4.actualCorrelationKernel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationKernel"
#print axioms Zeta23.OPICARound4.actualCorrelationKernel

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationSource"
#check @Zeta23.OPICARound4.actualCorrelationSource
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationSource"
#print axioms Zeta23.OPICARound4.actualCorrelationSource

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationCutoff"
#check @Zeta23.OPICARound4.actualCorrelationCutoff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationCutoff"
#print axioms Zeta23.OPICARound4.actualCorrelationCutoff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationWeight"
#check @Zeta23.OPICARound4.actualCorrelationWeight
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationWeight"
#print axioms Zeta23.OPICARound4.actualCorrelationWeight

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_eq_sourceConvolution"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_eq_sourceConvolution
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_eq_sourceConvolution"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_eq_sourceConvolution

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_bound_of_native_bound"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_bound_of_native_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_bound_of_native_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_bound_of_native_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_rapid_bound"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_rapid_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_rapid_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_rapid_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationKernel_supported"
#check @Zeta23.OPICARound4.actualCorrelationKernel_supported
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationKernel_supported"
#print axioms Zeta23.OPICARound4.actualCorrelationKernel_supported

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationCutoff_exact"
#check @Zeta23.OPICARound4.actualCorrelationCutoff_exact
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationCutoff_exact"
#print axioms Zeta23.OPICARound4.actualCorrelationCutoff_exact

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationWeight_zero_above"
#check @Zeta23.OPICARound4.actualCorrelationWeight_zero_above
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationWeight_zero_above"
#print axioms Zeta23.OPICARound4.actualCorrelationWeight_zero_above

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_eq_weighted_vonMangoldt"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_eq_weighted_vonMangoldt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_eq_weighted_vonMangoldt"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_eq_weighted_vonMangoldt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_eq_nativeSourceConvolution"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_eq_nativeSourceConvolution
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_eq_nativeSourceConvolution"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_eq_nativeSourceConvolution

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLogarithmicTest"
#check @Zeta23.OPICARound4.actualCorrelationLogarithmicTest
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLogarithmicTest"
#print axioms Zeta23.OPICARound4.actualCorrelationLogarithmicTest

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLogarithmicTest_eq_integerDrive"
#check @Zeta23.OPICARound4.actualCorrelationLogarithmicTest_eq_integerDrive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLogarithmicTest_eq_integerDrive"
#print axioms Zeta23.OPICARound4.actualCorrelationLogarithmicTest_eq_integerDrive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest"
#check @Zeta23.OPICARound4.actualFlatMobiusTest
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_normalization"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_normalization
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_normalization"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_normalization

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_eq_mobius"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_eq_mobius
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_eq_mobius"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_eq_mobius

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLogarithmicTest_half_support"
#check @Zeta23.OPICARound4.actualCorrelationLogarithmicTest_half_support
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLogarithmicTest_half_support"
#print axioms Zeta23.OPICARound4.actualCorrelationLogarithmicTest_half_support

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualNativeSourceConvolution_hyperbola_half"
#check @Zeta23.OPICARound4.actualNativeSourceConvolution_hyperbola_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualNativeSourceConvolution_hyperbola_half"
#print axioms Zeta23.OPICARound4.actualNativeSourceConvolution_hyperbola_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationShortTerm_rapid_bound"
#check @Zeta23.OPICARound4.actualCorrelationShortTerm_rapid_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationShortTerm_rapid_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationShortTerm_rapid_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.aliasDiagonal"
#check @Zeta23.OPICARound4.aliasDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.aliasDiagonal"
#print axioms Zeta23.OPICARound4.aliasDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.abs_aliasDiagonal_le_count"
#check @Zeta23.OPICARound4.abs_aliasDiagonal_le_count
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.abs_aliasDiagonal_le_count"
#print axioms Zeta23.OPICARound4.abs_aliasDiagonal_le_count

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.abs_aliasDiagonal_le_sqrt"
#check @Zeta23.OPICARound4.abs_aliasDiagonal_le_sqrt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.abs_aliasDiagonal_le_sqrt"
#print axioms Zeta23.OPICARound4.abs_aliasDiagonal_le_sqrt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.lower_bound_remove_bounded_diagonal"
#check @Zeta23.OPICARound4.lower_bound_remove_bounded_diagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.lower_bound_remove_bounded_diagonal"
#print axioms Zeta23.OPICARound4.lower_bound_remove_bounded_diagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.lower_bound_restore_bounded_diagonal"
#check @Zeta23.OPICARound4.lower_bound_restore_bounded_diagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.lower_bound_restore_bounded_diagonal"
#print axioms Zeta23.OPICARound4.lower_bound_restore_bounded_diagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonRemainder"
#check @Zeta23.OPICARound4.mobiusPoissonRemainder
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonRemainder"
#print axioms Zeta23.OPICARound4.mobiusPoissonRemainder

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonOffDiagonal"
#check @Zeta23.OPICARound4.mobiusPoissonOffDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonOffDiagonal"
#print axioms Zeta23.OPICARound4.mobiusPoissonOffDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusReciprocalSum"
#check @Zeta23.OPICARound4.mobiusReciprocalSum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusReciprocalSum"
#print axioms Zeta23.OPICARound4.mobiusReciprocalSum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonRankOne"
#check @Zeta23.OPICARound4.mobiusPoissonRankOne
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonRankOne"
#print axioms Zeta23.OPICARound4.mobiusPoissonRankOne

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonQuadratic"
#check @Zeta23.OPICARound4.mobiusPoissonQuadratic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonQuadratic"
#print axioms Zeta23.OPICARound4.mobiusPoissonQuadratic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonRemainder_eq_diagonal_add_offDiagonal"
#check @Zeta23.OPICARound4.mobiusPoissonRemainder_eq_diagonal_add_offDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonRemainder_eq_diagonal_add_offDiagonal"
#print axioms Zeta23.OPICARound4.mobiusPoissonRemainder_eq_diagonal_add_offDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonRankOne_nonneg"
#check @Zeta23.OPICARound4.mobiusPoissonRankOne_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonRankOne_nonneg"
#print axioms Zeta23.OPICARound4.mobiusPoissonRankOne_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_add_remainder"
#check @Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_add_remainder
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_add_remainder"
#print axioms Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_add_remainder

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal"
#check @Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal"
#print axioms Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.HasEventualSqrtLower"
#check @Zeta23.OPICARound4.HasEventualSqrtLower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.HasEventualSqrtLower"
#print axioms Zeta23.OPICARound4.HasEventualSqrtLower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal"
#check @Zeta23.OPICARound4.eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal"
#print axioms Zeta23.OPICARound4.eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_hyperbola"
#check @Zeta23.OPICARound4.validation_madness_actual_hyperbola
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_hyperbola"
#print axioms Zeta23.OPICARound4.validation_madness_actual_hyperbola

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_drive"
#check @Zeta23.OPICARound4.validation_madness_actual_drive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_drive"
#print axioms Zeta23.OPICARound4.validation_madness_actual_drive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_normalization"
#check @Zeta23.OPICARound4.validation_madness_actual_normalization
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_normalization"
#print axioms Zeta23.OPICARound4.validation_madness_actual_normalization

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_drive_rapid_decay"
#check @Zeta23.OPICARound4.validation_madness_drive_rapid_decay
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_drive_rapid_decay"
#print axioms Zeta23.OPICARound4.validation_madness_drive_rapid_decay

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_short_term_rapid_decay"
#check @Zeta23.OPICARound4.validation_madness_short_term_rapid_decay
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_short_term_rapid_decay"
#print axioms Zeta23.OPICARound4.validation_madness_short_term_rapid_decay

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_observable_remainder"
#check @Zeta23.OPICARound4.validation_madness_observable_remainder
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_observable_remainder"
#print axioms Zeta23.OPICARound4.validation_madness_observable_remainder

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_complete_split"
#check @Zeta23.OPICARound4.validation_madness_complete_split
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_complete_split"
#print axioms Zeta23.OPICARound4.validation_madness_complete_split

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_diagonal_budget"
#check @Zeta23.OPICARound4.validation_madness_diagonal_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_diagonal_budget"
#print axioms Zeta23.OPICARound4.validation_madness_diagonal_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_lower_equivalence"
#check @Zeta23.OPICARound4.validation_madness_lower_equivalence
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_lower_equivalence"
#print axioms Zeta23.OPICARound4.validation_madness_lower_equivalence

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_signed_test"
#check @Zeta23.OPICARound4.validation_madness_signed_test
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_signed_test"
#print axioms Zeta23.OPICARound4.validation_madness_signed_test

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.higherPrimePowerCoefficient"
#check @Zeta23.OPICARound4.higherPrimePowerCoefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.higherPrimePowerCoefficient"
#print axioms Zeta23.OPICARound4.higherPrimePowerCoefficient

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.higherPrimePowerCoefficient_nonneg"
#check @Zeta23.OPICARound4.higherPrimePowerCoefficient_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.higherPrimePowerCoefficient_nonneg"
#print axioms Zeta23.OPICARound4.higherPrimePowerCoefficient_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.higherPrimePowerCoefficient_sum"
#check @Zeta23.OPICARound4.higherPrimePowerCoefficient_sum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.higherPrimePowerCoefficient_sum"
#print axioms Zeta23.OPICARound4.higherPrimePowerCoefficient_sum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationKernel_continuous"
#check @Zeta23.OPICARound4.actualCorrelationKernel_continuous
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationKernel_continuous"
#print axioms Zeta23.OPICARound4.actualCorrelationKernel_continuous

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationSource_bounded"
#check @Zeta23.OPICARound4.actualCorrelationSource_bounded
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationSource_bounded"
#print axioms Zeta23.OPICARound4.actualCorrelationSource_bounded

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationWeight_uniform_bound"
#check @Zeta23.OPICARound4.actualCorrelationWeight_uniform_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationWeight_uniform_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationWeight_uniform_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationHigherPrimePowers"
#check @Zeta23.OPICARound4.actualCorrelationHigherPrimePowers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationHigherPrimePowers"
#print axioms Zeta23.OPICARound4.actualCorrelationHigherPrimePowers

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationHigherPrimePowers_uniform_bound"
#check @Zeta23.OPICARound4.actualCorrelationHigherPrimePowers_uniform_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationHigherPrimePowers_uniform_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationHigherPrimePowers_uniform_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_split_prime_powers"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_split_prime_powers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_split_prime_powers"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_split_prime_powers

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_hasDerivAt"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_hasDerivAt"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_hasDerivAt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv_rapid_bound"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv_rapid_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv_rapid_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv_rapid_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_zero_of_nonpos"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_zero_of_nonpos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_zero_of_nonpos"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_zero_of_nonpos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_higher_prime_powers_bounded"
#check @Zeta23.OPICARound4.validation_madness_higher_prime_powers_bounded
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_higher_prime_powers_bounded"
#print axioms Zeta23.OPICARound4.validation_madness_higher_prime_powers_bounded

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_prime_power_split"
#check @Zeta23.OPICARound4.validation_madness_prime_power_split
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_prime_power_split"
#print axioms Zeta23.OPICARound4.validation_madness_prime_power_split

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_drive_derivative_rapid"
#check @Zeta23.OPICARound4.validation_madness_drive_derivative_rapid
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_drive_derivative_rapid"
#print axioms Zeta23.OPICARound4.validation_madness_drive_derivative_rapid

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_flat_test_derivative"
#check @Zeta23.OPICARound4.validation_madness_flat_test_derivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_flat_test_derivative"
#print axioms Zeta23.OPICARound4.validation_madness_flat_test_derivative

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_contDiff_one"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_contDiff_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_contDiff_one"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_contDiff_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_origin_bounds"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_origin_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_origin_bounds"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_origin_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt_zero"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt_zero"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_contDiff_one"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_contDiff_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_contDiff_one"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_contDiff_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_zero_above"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_zero_above
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_zero_above"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_zero_above

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_at_upper_collar"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_at_upper_collar
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_at_upper_collar"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_at_upper_collar

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatMobiusTest_hasCompactSupport"
#check @Zeta23.OPICARound4.actualFlatMobiusTest_hasCompactSupport
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatMobiusTest_hasCompactSupport"
#print axioms Zeta23.OPICARound4.actualFlatMobiusTest_hasCompactSupport

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingMass"
#check @Zeta23.OPICARound4.actualFlatSamplingMass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingMass"
#print axioms Zeta23.OPICARound4.actualFlatSamplingMass

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingSum"
#check @Zeta23.OPICARound4.actualFlatSamplingSum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingSum"
#print axioms Zeta23.OPICARound4.actualFlatSamplingSum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingRemainder"
#check @Zeta23.OPICARound4.actualFlatSamplingRemainder
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingRemainder"
#print axioms Zeta23.OPICARound4.actualFlatSamplingRemainder

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingRemainder_bounded"
#check @Zeta23.OPICARound4.actualFlatSamplingRemainder_bounded
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingRemainder_bounded"
#print axioms Zeta23.OPICARound4.actualFlatSamplingRemainder_bounded

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingSum_eq_mass_add_remainder"
#check @Zeta23.OPICARound4.actualFlatSamplingSum_eq_mass_add_remainder
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingSum_eq_mass_add_remainder"
#print axioms Zeta23.OPICARound4.actualFlatSamplingSum_eq_mass_add_remainder

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingDiagonal_sqrt_bound"
#check @Zeta23.OPICARound4.actualFlatSamplingDiagonal_sqrt_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingDiagonal_sqrt_bound"
#print axioms Zeta23.OPICARound4.actualFlatSamplingDiagonal_sqrt_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingSum_eq_tsum"
#check @Zeta23.OPICARound4.actualFlatSamplingSum_eq_tsum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingSum_eq_tsum"
#print axioms Zeta23.OPICARound4.actualFlatSamplingSum_eq_tsum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSampling_eventual_lower_iff"
#check @Zeta23.OPICARound4.actualFlatSampling_eventual_lower_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSampling_eventual_lower_iff"
#print axioms Zeta23.OPICARound4.actualFlatSampling_eventual_lower_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_flat_test_c1"
#check @Zeta23.OPICARound4.validation_madness_flat_test_c1
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_flat_test_c1"
#print axioms Zeta23.OPICARound4.validation_madness_flat_test_c1

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_flat_test_compact"
#check @Zeta23.OPICARound4.validation_madness_flat_test_compact
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_flat_test_compact"
#print axioms Zeta23.OPICARound4.validation_madness_flat_test_compact

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_remainder_bounded"
#check @Zeta23.OPICARound4.validation_madness_actual_remainder_bounded
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_remainder_bounded"
#print axioms Zeta23.OPICARound4.validation_madness_actual_remainder_bounded

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_diagonal"
#check @Zeta23.OPICARound4.validation_madness_actual_diagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_diagonal"
#print axioms Zeta23.OPICARound4.validation_madness_actual_diagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_all_sampling_terms"
#check @Zeta23.OPICARound4.validation_madness_all_sampling_terms
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_all_sampling_terms"
#print axioms Zeta23.OPICARound4.validation_madness_all_sampling_terms

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_lower_equivalence"
#check @Zeta23.OPICARound4.validation_madness_actual_lower_equivalence
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_lower_equivalence"
#print axioms Zeta23.OPICARound4.validation_madness_actual_lower_equivalence

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingSum_eq_hyperbola_history"
#check @Zeta23.OPICARound4.actualFlatSamplingSum_eq_hyperbola_history
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingSum_eq_hyperbola_history"
#print axioms Zeta23.OPICARound4.actualFlatSamplingSum_eq_hyperbola_history

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLongTerm_eq_sampling_quadratic"
#check @Zeta23.OPICARound4.actualCorrelationLongTerm_eq_sampling_quadratic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLongTerm_eq_sampling_quadratic"
#print axioms Zeta23.OPICARound4.actualCorrelationLongTerm_eq_sampling_quadratic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationNativeCutoff_sqrt_bound"
#check @Zeta23.OPICARound4.actualCorrelationNativeCutoff_sqrt_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationNativeCutoff_sqrt_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationNativeCutoff_sqrt_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound"
#check @Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined"
#check @Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined"
#print axioms Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined"
#check @Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined"
#print axioms Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actualCorrelationNativeDiagonal_bound"
#check @Zeta23.OPICARound4.validation_madness_actualCorrelationNativeDiagonal_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actualCorrelationNativeDiagonal_bound"
#print axioms Zeta23.OPICARound4.validation_madness_actualCorrelationNativeDiagonal_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined"
#check @Zeta23.OPICARound4.validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined"
#print axioms Zeta23.OPICARound4.validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_exact_sampling_bridge"
#check @Zeta23.OPICARound4.validation_madness_exact_sampling_bridge
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_exact_sampling_bridge"
#print axioms Zeta23.OPICARound4.validation_madness_exact_sampling_bridge

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOriginalIntegerDriveLaplace_half"
#check @Zeta23.OPICARound4.nativeOriginalIntegerDriveLaplace_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOriginalIntegerDriveLaplace_half"
#print axioms Zeta23.OPICARound4.nativeOriginalIntegerDriveLaplace_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualSourceHalfMass"
#check @Zeta23.OPICARound4.actualSourceHalfMass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualSourceHalfMass"
#print axioms Zeta23.OPICARound4.actualSourceHalfMass

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualSourceHalfMass_integrable"
#check @Zeta23.OPICARound4.actualSourceHalfMass_integrable
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualSourceHalfMass_integrable"
#print axioms Zeta23.OPICARound4.actualSourceHalfMass_integrable

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualSourceHalfMass_eq_product"
#check @Zeta23.OPICARound4.actualSourceHalfMass_eq_product
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualSourceHalfMass_eq_product"
#print axioms Zeta23.OPICARound4.actualSourceHalfMass_eq_product

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualSourceHalfMass_pos"
#check @Zeta23.OPICARound4.actualSourceHalfMass_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualSourceHalfMass_pos"
#print axioms Zeta23.OPICARound4.actualSourceHalfMass_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOriginalIntegerDrive_half_integral"
#check @Zeta23.OPICARound4.nativeOriginalIntegerDrive_half_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOriginalIntegerDrive_half_integral"
#print axioms Zeta23.OPICARound4.nativeOriginalIntegerDrive_half_integral

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingMass_eq_dampedDrive"
#check @Zeta23.OPICARound4.actualFlatSamplingMass_eq_dampedDrive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingMass_eq_dampedDrive"
#print axioms Zeta23.OPICARound4.actualFlatSamplingMass_eq_dampedDrive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationIntegerDrive_half_integral"
#check @Zeta23.OPICARound4.actualCorrelationIntegerDrive_half_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationIntegerDrive_half_integral"
#print axioms Zeta23.OPICARound4.actualCorrelationIntegerDrive_half_integral

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingMass_eq_sourceHalfMass_sq"
#check @Zeta23.OPICARound4.actualFlatSamplingMass_eq_sourceHalfMass_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingMass_eq_sourceHalfMass_sq"
#print axioms Zeta23.OPICARound4.actualFlatSamplingMass_eq_sourceHalfMass_sq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualFlatSamplingMass_pos"
#check @Zeta23.OPICARound4.actualFlatSamplingMass_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualFlatSamplingMass_pos"
#print axioms Zeta23.OPICARound4.actualFlatSamplingMass_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_mass_positive"
#check @Zeta23.OPICARound4.validation_madness_actual_mass_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_mass_positive"
#print axioms Zeta23.OPICARound4.validation_madness_actual_mass_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_rank_one_nonnegative"
#check @Zeta23.OPICARound4.validation_madness_actual_rank_one_nonnegative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_rank_one_nonnegative"
#print axioms Zeta23.OPICARound4.validation_madness_actual_rank_one_nonnegative

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationKernel_weilTest_translate"
#check @Zeta23.OPICARound4.actualCorrelationKernel_weilTest_translate
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationKernel_weilTest_translate"
#print axioms Zeta23.OPICARound4.actualCorrelationKernel_weilTest_translate

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationArch"
#check @Zeta23.OPICARound4.actualCorrelationArch
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationArch"
#print axioms Zeta23.OPICARound4.actualCorrelationArch

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelation_explicit_formula"
#check @Zeta23.OPICARound4.actualCorrelation_explicit_formula
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelation_explicit_formula"
#print axioms Zeta23.OPICARound4.actualCorrelation_explicit_formula

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationArch_uniform_bound"
#check @Zeta23.OPICARound4.actualCorrelationArch_uniform_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationArch_uniform_bound"
#print axioms Zeta23.OPICARound4.actualCorrelationArch_uniform_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actualCorrelationPrimeField_reflected_zero"
#check @Zeta23.OPICARound4.actualCorrelationPrimeField_reflected_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actualCorrelationPrimeField_reflected_zero"
#print axioms Zeta23.OPICARound4.actualCorrelationPrimeField_reflected_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower"
#check @Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower"
#print axioms Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_weil_translation"
#check @Zeta23.OPICARound4.validation_madness_actual_weil_translation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_weil_translation"
#print axioms Zeta23.OPICARound4.validation_madness_actual_weil_translation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_explicit_formula"
#check @Zeta23.OPICARound4.validation_madness_actual_explicit_formula
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_explicit_formula"
#print axioms Zeta23.OPICARound4.validation_madness_actual_explicit_formula

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_arch_bound"
#check @Zeta23.OPICARound4.validation_madness_actual_arch_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_arch_bound"
#print axioms Zeta23.OPICARound4.validation_madness_actual_arch_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_actual_reflected_history"
#check @Zeta23.OPICARound4.validation_madness_actual_reflected_history
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_actual_reflected_history"
#print axioms Zeta23.OPICARound4.validation_madness_actual_reflected_history

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.validation_madness_rh_of_actual_lower"
#check @Zeta23.OPICARound4.validation_madness_rh_of_actual_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.validation_madness_rh_of_actual_lower"
#print axioms Zeta23.OPICARound4.validation_madness_rh_of_actual_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase"
#check @Zeta23.OPICARound4.recenteredSmoothPhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteApprox"
#check @Zeta23.OPICARound4.recenteredFiniteApprox
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteApprox"
#print axioms Zeta23.OPICARound4.recenteredFiniteApprox

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteHard"
#check @Zeta23.OPICARound4.recenteredFiniteHard
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteHard"
#print axioms Zeta23.OPICARound4.recenteredFiniteHard

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_eq_translate"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_eq_translate
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_eq_translate"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_eq_translate

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_contDiff"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_contDiff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_contDiff"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_contDiff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_L1_bound"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_L1_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_L1_bound"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_L1_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_zero_outside"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_zero_outside
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_zero_outside"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_zero_outside

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteHard_contDiff"
#check @Zeta23.OPICARound4.recenteredFiniteHard_contDiff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteHard_contDiff"
#print axioms Zeta23.OPICARound4.recenteredFiniteHard_contDiff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteApprox_jet_error"
#check @Zeta23.OPICARound4.recenteredFiniteApprox_jet_error
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteApprox_jet_error"
#print axioms Zeta23.OPICARound4.recenteredFiniteApprox_jet_error

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteHard_L1_error"
#check @Zeta23.OPICARound4.recenteredFiniteHard_L1_error
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteHard_L1_error"
#print axioms Zeta23.OPICARound4.recenteredFiniteHard_L1_error

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFinitePhase_Weil_error"
#check @Zeta23.OPICARound4.recenteredFinitePhase_Weil_error
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFinitePhase_Weil_error"
#print axioms Zeta23.OPICARound4.recenteredFinitePhase_Weil_error

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteHard_Weil_eq_native"
#check @Zeta23.OPICARound4.recenteredFiniteHard_Weil_eq_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteHard_Weil_eq_native"
#print axioms Zeta23.OPICARound4.recenteredFiniteHard_Weil_eq_native

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_fixed_energy"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_fixed_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_fixed_energy"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_fixed_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recentered_negative_phase_eventually_quartic"
#check @Zeta23.OPICARound4.recentered_negative_phase_eventually_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recentered_negative_phase_eventually_quartic"
#print axioms Zeta23.OPICARound4.recentered_negative_phase_eventually_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_fixed_negative_original_phase"
#check @Zeta23.OPICARound4.exists_fixed_negative_original_phase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_fixed_negative_original_phase"
#print axioms Zeta23.OPICARound4.exists_fixed_negative_original_phase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventually_both_negative_at_original_quartic"
#check @Zeta23.OPICARound4.eventually_both_negative_at_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventually_both_negative_at_original_quartic"
#print axioms Zeta23.OPICARound4.eventually_both_negative_at_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.cofinally_both_negative_at_original_quartic"
#check @Zeta23.OPICARound4.cofinally_both_negative_at_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.cofinally_both_negative_at_original_quartic"
#print axioms Zeta23.OPICARound4.cofinally_both_negative_at_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.every_late_generated_packet_has_joint_detector_ground"
#check @Zeta23.OPICARound4.every_late_generated_packet_has_joint_detector_ground
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.every_late_generated_packet_has_joint_detector_ground"
#print axioms Zeta23.OPICARound4.every_late_generated_packet_has_joint_detector_ground

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.first_common_cutoff_le_original_quartic"
#check @Zeta23.OPICARound4.first_common_cutoff_le_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.first_common_cutoff_le_original_quartic"
#print axioms Zeta23.OPICARound4.first_common_cutoff_le_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.negative_eigenspace_finrank_le_shell"
#check @Zeta23.OPICARound4.negative_eigenspace_finrank_le_shell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.negative_eigenspace_finrank_le_shell"
#print axioms Zeta23.OPICARound4.negative_eigenspace_finrank_le_shell

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeNewborn_negative_eigenspace_finrank_le_one"
#check @Zeta23.OPICARound4.nativeNewborn_negative_eigenspace_finrank_le_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeNewborn_negative_eigenspace_finrank_le_one"
#print axioms Zeta23.OPICARound4.nativeNewborn_negative_eigenspace_finrank_le_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeNewborn_even_ground_simple"
#check @Zeta23.OPICARound4.nativeNewborn_even_ground_simple
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeNewborn_even_ground_simple"
#print axioms Zeta23.OPICARound4.nativeNewborn_even_ground_simple

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeNewborn_even_tied_ground_momentFour_ne_zero"
#check @Zeta23.OPICARound4.nativeNewborn_even_tied_ground_momentFour_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeNewborn_even_tied_ground_momentFour_ne_zero"
#print axioms Zeta23.OPICARound4.nativeNewborn_even_tied_ground_momentFour_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.simple_native_tied_ground_not_both_silent"
#check @Zeta23.OPICARound4.simple_native_tied_ground_not_both_silent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.simple_native_tied_ground_not_both_silent"
#print axioms Zeta23.OPICARound4.simple_native_tied_ground_not_both_silent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oneShell_negative_eigen_complement_nonnegative"
#check @Zeta23.OPICARound4.oneShell_negative_eigen_complement_nonnegative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oneShell_negative_eigen_complement_nonnegative"
#print axioms Zeta23.OPICARound4.oneShell_negative_eigen_complement_nonnegative

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oneShell_negative_eigen_shifted_complement_coercive"
#check @Zeta23.OPICARound4.oneShell_negative_eigen_shifted_complement_coercive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oneShell_negative_eigen_shifted_complement_coercive"
#print axioms Zeta23.OPICARound4.oneShell_negative_eigen_shifted_complement_coercive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oneShell_negative_eigen_complement_response_norm"
#check @Zeta23.OPICARound4.oneShell_negative_eigen_complement_response_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oneShell_negative_eigen_complement_response_norm"
#print axioms Zeta23.OPICARound4.oneShell_negative_eigen_complement_response_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeNewborn_negative_eigen_complement_bounds"
#check @Zeta23.OPICARound4.nativeNewborn_negative_eigen_complement_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeNewborn_negative_eigen_complement_bounds"
#print axioms Zeta23.OPICARound4.nativeNewborn_negative_eigen_complement_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_active_moment_pos_of_le_odd_bottom"
#check @Zeta23.OPICARound4.native_source_active_moment_pos_of_le_odd_bottom
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_active_moment_pos_of_le_odd_bottom"
#print axioms Zeta23.OPICARound4.native_source_active_moment_pos_of_le_odd_bottom

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_normalized_tied_ground_moment_pos"
#check @Zeta23.OPICARound4.native_source_normalized_tied_ground_moment_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_normalized_tied_ground_moment_pos"
#print axioms Zeta23.OPICARound4.native_source_normalized_tied_ground_moment_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.simple_even_tie_source_silent_odd_kernel_visible"
#check @Zeta23.OPICARound4.simple_even_tie_source_silent_odd_kernel_visible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.simple_even_tie_source_silent_odd_kernel_visible"
#print axioms Zeta23.OPICARound4.simple_even_tie_source_silent_odd_kernel_visible

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.simple_even_tie_whole_kernel_exclusive_visibility"
#check @Zeta23.OPICARound4.simple_even_tie_whole_kernel_exclusive_visibility
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.simple_even_tie_whole_kernel_exclusive_visibility"
#print axioms Zeta23.OPICARound4.simple_even_tie_whole_kernel_exclusive_visibility

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.common_quartic_uniform_threshold_consumer"
#check @Zeta23.OPICARound4.Validation.common_quartic_uniform_threshold_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.common_quartic_uniform_threshold_consumer"
#print axioms Zeta23.OPICARound4.Validation.common_quartic_uniform_threshold_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.generated_packet_joint_consumer"
#check @Zeta23.OPICARound4.Validation.generated_packet_joint_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.generated_packet_joint_consumer"
#print axioms Zeta23.OPICARound4.Validation.generated_packet_joint_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.first_common_quartic_bound_consumer"
#check @Zeta23.OPICARound4.Validation.first_common_quartic_bound_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.first_common_quartic_bound_consumer"
#print axioms Zeta23.OPICARound4.Validation.first_common_quartic_bound_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_newborn_complement_consumer"
#check @Zeta23.OPICARound4.Validation.native_newborn_complement_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_newborn_complement_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_newborn_complement_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.source_active_ground_moment_consumer"
#check @Zeta23.OPICARound4.Validation.source_active_ground_moment_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.source_active_ground_moment_consumer"
#print axioms Zeta23.OPICARound4.Validation.source_active_ground_moment_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_newborn_even_ground_simple_consumer"
#check @Zeta23.OPICARound4.Validation.actual_newborn_even_ground_simple_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_newborn_even_ground_simple_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_newborn_even_ground_simple_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.tied_ground_not_both_silent_consumer"
#check @Zeta23.OPICARound4.Validation.tied_ground_not_both_silent_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.tied_ground_not_both_silent_consumer"
#print axioms Zeta23.OPICARound4.Validation.tied_ground_not_both_silent_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.tied_ground_whole_kernel_visibility_consumer"
#check @Zeta23.OPICARound4.Validation.tied_ground_whole_kernel_visibility_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.tied_ground_whole_kernel_visibility_consumer"
#print axioms Zeta23.OPICARound4.Validation.tied_ground_whole_kernel_visibility_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_indexComplement_norm_le"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_indexComplement_norm_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_indexComplement_norm_le"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_indexComplement_norm_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_active_source_moment_bounds"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_active_source_moment_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_active_source_moment_bounds"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_active_source_moment_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_normalized_moment_bounds"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_normalized_moment_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_normalized_moment_bounds"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_normalized_moment_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeNewborn_negative_eigenvalue_eq_ground"
#check @Zeta23.OPICARound4.nativeNewborn_negative_eigenvalue_eq_ground
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeNewborn_negative_eigenvalue_eq_ground"
#print axioms Zeta23.OPICARound4.nativeNewborn_negative_eigenvalue_eq_ground

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.evenNewborn_odd_negative_eigen_channels_visible"
#check @Zeta23.OPICARound4.evenNewborn_odd_negative_eigen_channels_visible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.evenNewborn_odd_negative_eigen_channels_visible"
#print axioms Zeta23.OPICARound4.evenNewborn_odd_negative_eigen_channels_visible

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oddNewborn_even_negative_eigen_channels_visible"
#check @Zeta23.OPICARound4.oddNewborn_even_negative_eigen_channels_visible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oddNewborn_even_negative_eigen_channels_visible"
#print axioms Zeta23.OPICARound4.oddNewborn_even_negative_eigen_channels_visible

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.evenNewborn_odd_negative_eigenspace_finrank_le_one"
#check @Zeta23.OPICARound4.evenNewborn_odd_negative_eigenspace_finrank_le_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.evenNewborn_odd_negative_eigenspace_finrank_le_one"
#print axioms Zeta23.OPICARound4.evenNewborn_odd_negative_eigenspace_finrank_le_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oddNewborn_even_negative_eigenspace_finrank_le_one"
#check @Zeta23.OPICARound4.oddNewborn_even_negative_eigenspace_finrank_le_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oddNewborn_even_negative_eigenspace_finrank_le_one"
#print axioms Zeta23.OPICARound4.oddNewborn_even_negative_eigenspace_finrank_le_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_energy_nonneg"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_energy_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_energy_nonneg"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_energy_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_channel_nonneg"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_channel_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_channel_nonneg"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_channel_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_normalized_even_moment_cubic_energy_lower"
#check @Zeta23.OPICARound4.actual_normalized_even_moment_cubic_energy_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_normalized_even_moment_cubic_energy_lower"
#print axioms Zeta23.OPICARound4.actual_normalized_even_moment_cubic_energy_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_silent_moment_depth_lower"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_silent_moment_depth_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_silent_moment_depth_lower"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_silent_moment_depth_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple"
#check @Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple"
#print axioms Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_log_nonzero_in_open_positive"
#check @Zeta23.OPICARound4.exists_log_nonzero_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_log_nonzero_in_open_positive"
#print axioms Zeta23.OPICARound4.exists_log_nonzero_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_finite_log_nonzero_in_open_positive"
#check @Zeta23.OPICARound4.exists_finite_log_nonzero_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_finite_log_nonzero_in_open_positive"
#print axioms Zeta23.OPICARound4.exists_finite_log_nonzero_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedEntry"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedEntry"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedEntry

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_ofReal"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_ofReal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_ofReal"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_ofReal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_one"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_one"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_one"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_one"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedFullSource"
#check @Zeta23.OPICARound4.RegularCells.liftedFullSource
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedFullSource"
#print axioms Zeta23.OPICARound4.RegularCells.liftedFullSource

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedFrameSource"
#check @Zeta23.OPICARound4.RegularCells.normalizedFrameSource
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedFrameSource"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedFrameSource

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedFrameSource_apply"
#check @Zeta23.OPICARound4.RegularCells.normalizedFrameSource_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedFrameSource_apply"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedFrameSource_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.analyticOnNhd_normalizedFrameSource_apply"
#check @Zeta23.OPICARound4.RegularCells.analyticOnNhd_normalizedFrameSource_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.analyticOnNhd_normalizedFrameSource_apply"
#print axioms Zeta23.OPICARound4.RegularCells.analyticOnNhd_normalizedFrameSource_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedNativeFrame"
#check @Zeta23.OPICARound4.RegularCells.liftedNativeFrame
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedNativeFrame"
#print axioms Zeta23.OPICARound4.RegularCells.liftedNativeFrame

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrame_coord"
#check @Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrame_coord
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrame_coord"
#print axioms Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrame_coord

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedNativeFrame_deck_base"
#check @Zeta23.OPICARound4.RegularCells.liftedNativeFrame_deck_base
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedNativeFrame_deck_base"
#print axioms Zeta23.OPICARound4.RegularCells.liftedNativeFrame_deck_base

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedNativeFrameDet"
#check @Zeta23.OPICARound4.RegularCells.liftedNativeFrameDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedNativeFrameDet"
#print axioms Zeta23.OPICARound4.RegularCells.liftedNativeFrameDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrameDet"
#check @Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrameDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrameDet"
#print axioms Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrameDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_mem_corridor_liftedNativeFrameDet_ne_zero"
#check @Zeta23.OPICARound4.RegularCells.exists_mem_corridor_liftedNativeFrameDet_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_mem_corridor_liftedNativeFrameDet_ne_zero"
#print axioms Zeta23.OPICARound4.RegularCells.exists_mem_corridor_liftedNativeFrameDet_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry"
#check @Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry"
#print axioms Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.nativeSeedPhysicalTransport"
#check @Zeta23.OPICARound4.RegularCells.nativeSeedPhysicalTransport
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.nativeSeedPhysicalTransport"
#print axioms Zeta23.OPICARound4.RegularCells.nativeSeedPhysicalTransport

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_physical_transport"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_physical_transport
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_physical_transport"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_physical_transport

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry_inner_canonical"
#check @Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry_inner_canonical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry_inner_canonical"
#print axioms Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry_inner_canonical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedFullSource_log_fixedCell"
#check @Zeta23.OPICARound4.RegularCells.liftedFullSource_log_fixedCell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedFullSource_log_fixedCell"
#print axioms Zeta23.OPICARound4.RegularCells.liftedFullSource_log_fixedCell

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_real_isSymmetric"
#check @Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_real_isSymmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_real_isSymmetric"
#print axioms Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_real_isSymmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.liftedNativeFrame_log_fixedCell"
#check @Zeta23.OPICARound4.RegularCells.liftedNativeFrame_log_fixedCell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.liftedNativeFrame_log_fixedCell"
#print axioms Zeta23.OPICARound4.RegularCells.liftedNativeFrame_log_fixedCell

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.nativeCanonical_bijective_of_frameDet_ne_zero"
#check @Zeta23.OPICARound4.RegularCells.nativeCanonical_bijective_of_frameDet_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.nativeCanonical_bijective_of_frameDet_ne_zero"
#print axioms Zeta23.OPICARound4.RegularCells.nativeCanonical_bijective_of_frameDet_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_fixedCell"
#check @Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_fixedCell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_fixedCell"
#print axioms Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_fixedCell

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_open_fixedCell_subset_positive"
#check @Zeta23.OPICARound4.RegularCells.exists_open_fixedCell_subset_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_open_fixedCell_subset_positive"
#print axioms Zeta23.OPICARound4.RegularCells.exists_open_fixedCell_subset_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_positive"
#check @Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_positive"
#print axioms Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_bounded_native_regular_in_open_positive"
#check @Zeta23.OPICARound4.RegularCells.exists_bounded_native_regular_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_bounded_native_regular_in_open_positive"
#print axioms Zeta23.OPICARound4.RegularCells.exists_bounded_native_regular_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.cofinally_both_negative_and_native_regular"
#check @Zeta23.OPICARound4.RegularCells.cofinally_both_negative_and_native_regular
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.cofinally_both_negative_and_native_regular"
#print axioms Zeta23.OPICARound4.RegularCells.cofinally_both_negative_and_native_regular

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.cofinally_regular_first_common_births"
#check @Zeta23.OPICARound4.RegularCells.cofinally_regular_first_common_births
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.cofinally_regular_first_common_births"
#print axioms Zeta23.OPICARound4.RegularCells.cofinally_regular_first_common_births

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.native_newborn_realization_regular_of_bijective"
#check @Zeta23.OPICARound4.RegularCells.native_newborn_realization_regular_of_bijective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.native_newborn_realization_regular_of_bijective"
#print axioms Zeta23.OPICARound4.RegularCells.native_newborn_realization_regular_of_bijective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.tied_newborn_active_response_consumer"
#check @Zeta23.OPICARound4.Validation.tied_newborn_active_response_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.tied_newborn_active_response_consumer"
#print axioms Zeta23.OPICARound4.Validation.tied_newborn_active_response_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.newborn_opposite_source_channels_consumer"
#check @Zeta23.OPICARound4.Validation.newborn_opposite_source_channels_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.newborn_opposite_source_channels_consumer"
#print axioms Zeta23.OPICARound4.Validation.newborn_opposite_source_channels_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.normalized_cubic_energy_lower_consumer"
#check @Zeta23.OPICARound4.Validation.normalized_cubic_energy_lower_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.normalized_cubic_energy_lower_consumer"
#print axioms Zeta23.OPICARound4.Validation.normalized_cubic_energy_lower_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.negative_cubic_energy_ground_simple_consumer"
#check @Zeta23.OPICARound4.Validation.negative_cubic_energy_ground_simple_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.negative_cubic_energy_ground_simple_consumer"
#print axioms Zeta23.OPICARound4.Validation.negative_cubic_energy_ground_simple_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.native_fixed_cell_regular_selection_consumer"
#check @Zeta23.OPICARound4.Validation.native_fixed_cell_regular_selection_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.native_fixed_cell_regular_selection_consumer"
#print axioms Zeta23.OPICARound4.Validation.native_fixed_cell_regular_selection_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.cofinal_native_regular_births_consumer"
#check @Zeta23.OPICARound4.Validation.cofinal_native_regular_births_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.cofinal_native_regular_births_consumer"
#print axioms Zeta23.OPICARound4.Validation.cofinal_native_regular_births_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.same_newborn_regular_realization_consumer"
#check @Zeta23.OPICARound4.Validation.same_newborn_regular_realization_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.same_newborn_regular_realization_consumer"
#print axioms Zeta23.OPICARound4.Validation.same_newborn_regular_realization_consumer

-- Expand proof arguments in the new declarations; retain preceding audit bytes.
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 2000000

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.diagonal_two_moment_compressions_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.diagonal_two_moment_compressions_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.diagonal_two_moment_compressions_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.diagonal_two_moment_compressions_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.native_squared_index_compressions_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.native_squared_index_compressions_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.native_squared_index_compressions_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.native_squared_index_compressions_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeConstantVector"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeConstantVector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeConstantVector"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeConstantVector

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeIndexVector"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeIndexVector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeIndexVector"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeIndexVector

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSquareVector"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSquareVector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSquareVector"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSquareVector

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeReciprocalVector"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeReciprocalVector
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeReciprocalVector"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeReciprocalVector

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingEvenCarrier"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingEvenCarrier
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingEvenCarrier"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingEvenCarrier

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingOddCarrier"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingOddCarrier
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingOddCarrier"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingOddCarrier

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexDiagonal"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexDiagonal"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexCompression"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexCompression
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexCompression"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexCompression

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.native_limiting_compressed_squared_index_no_common_eigenvalue"
#check @Zeta23.OPICARound4.NativeParitySeparation.native_limiting_compressed_squared_index_no_common_eigenvalue
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.native_limiting_compressed_squared_index_no_common_eigenvalue"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.native_limiting_compressed_squared_index_no_common_eigenvalue

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_of_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_of_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_of_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_of_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_not_injective_of_common"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_not_injective_of_common
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_not_injective_of_common"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_not_injective_of_common

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_iff_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_iff_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_iff_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_iff_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_det_ne_zero_iff_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_det_ne_zero_iff_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_det_ne_zero_iff_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_det_ne_zero_iff_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_common_scalar"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_common_scalar
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_common_scalar"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_common_scalar

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_scale"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_scale
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_scale"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_scale

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_identity_gram"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_identity_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_identity_gram"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_identity_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_factor"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_factor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_factor"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_factor

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_injective_of_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_injective_of_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_injective_of_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_injective_of_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_disjoint_of_injective"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_disjoint_of_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_disjoint_of_injective"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_disjoint_of_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_det_ne_zero_iff_disjoint"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_det_ne_zero_iff_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_det_ne_zero_iff_disjoint"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_det_ne_zero_iff_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.imaginaryReciprocal"
#check @Zeta23.OPICARound4.RegularCells.imaginaryReciprocal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.imaginaryReciprocal"
#print axioms Zeta23.OPICARound4.RegularCells.imaginaryReciprocal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto"
#check @Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto"
#print axioms Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto_punctured"
#check @Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto_punctured
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto_punctured"
#print axioms Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto_punctured

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_isBigO_pow"
#check @Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_isBigO_pow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_isBigO_pow"
#print axioms Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_isBigO_pow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_div_exp_tendsto_zero"
#check @Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_div_exp_tendsto_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_div_exp_tendsto_zero"
#print axioms Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_div_exp_tendsto_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.frequencyRayTerm"
#check @Zeta23.OPICARound4.RegularCells.frequencyRayTerm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.frequencyRayTerm"
#print axioms Zeta23.OPICARound4.RegularCells.frequencyRayTerm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.frequencyRayTerm_div"
#check @Zeta23.OPICARound4.RegularCells.frequencyRayTerm_div
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.frequencyRayTerm_div"
#print axioms Zeta23.OPICARound4.RegularCells.frequencyRayTerm_div

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_max_nonzero"
#check @Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_max_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_max_nonzero"
#print axioms Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_max_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_nonzero"
#check @Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_nonzero"
#print axioms Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exp_frequency_imaginaryReciprocal"
#check @Zeta23.OPICARound4.RegularCells.exp_frequency_imaginaryReciprocal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exp_frequency_imaginaryReciprocal"
#print axioms Zeta23.OPICARound4.RegularCells.exp_frequency_imaginaryReciprocal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.meromorphic_frequency_germ_nonzero"
#check @Zeta23.OPICARound4.RegularCells.meromorphic_frequency_germ_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.meromorphic_frequency_germ_nonzero"
#print axioms Zeta23.OPICARound4.RegularCells.meromorphic_frequency_germ_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLogFrequency"
#check @Zeta23.OPICARound4.RegularCells.primeLogFrequency
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLogFrequency"
#print axioms Zeta23.OPICARound4.RegularCells.primeLogFrequency

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.finite_prime_product_factorization"
#check @Zeta23.OPICARound4.RegularCells.finite_prime_product_factorization
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.finite_prime_product_factorization"
#print axioms Zeta23.OPICARound4.RegularCells.finite_prime_product_factorization

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.natural_prime_log_sum_injective"
#check @Zeta23.OPICARound4.RegularCells.natural_prime_log_sum_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.natural_prime_log_sum_injective"
#print axioms Zeta23.OPICARound4.RegularCells.natural_prime_log_sum_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLogFrequency_injective"
#check @Zeta23.OPICARound4.RegularCells.primeLogFrequency_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLogFrequency_injective"
#print axioms Zeta23.OPICARound4.RegularCells.primeLogFrequency_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurentFrequency"
#check @Zeta23.OPICARound4.RegularCells.primeLaurentFrequency
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurentFrequency"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurentFrequency

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurentFrequency_injective"
#check @Zeta23.OPICARound4.RegularCells.primeLaurentFrequency_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurentFrequency_injective"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurentFrequency_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primePhase"
#check @Zeta23.OPICARound4.RegularCells.primePhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primePhase"
#print axioms Zeta23.OPICARound4.RegularCells.primePhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurentMonomial"
#check @Zeta23.OPICARound4.RegularCells.primeLaurentMonomial
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurentMonomial"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurentMonomial

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurentMonomial_eq_exp"
#check @Zeta23.OPICARound4.RegularCells.primeLaurentMonomial_eq_exp
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurentMonomial_eq_exp"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurentMonomial_eq_exp

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient"
#check @Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient"
#print axioms Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurent_sum_grouped"
#check @Zeta23.OPICARound4.RegularCells.primeLaurent_sum_grouped
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurent_sum_grouped"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurent_sum_grouped

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient_meromorphic"
#check @Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient_meromorphic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient_meromorphic"
#print axioms Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient_meromorphic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLaurent_sum_germ_nonzero"
#check @Zeta23.OPICARound4.RegularCells.primeLaurent_sum_germ_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLaurent_sum_germ_nonzero"
#print axioms Zeta23.OPICARound4.RegularCells.primeLaurent_sum_germ_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primeLogFrequency_factorization"
#check @Zeta23.OPICARound4.RegularCells.primeLogFrequency_factorization
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primeLogFrequency_factorization"
#print axioms Zeta23.OPICARound4.RegularCells.primeLogFrequency_factorization

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primePhase_eq_factorization_monomial"
#check @Zeta23.OPICARound4.RegularCells.primePhase_eq_factorization_monomial
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primePhase_eq_factorization_monomial"
#print axioms Zeta23.OPICARound4.RegularCells.primePhase_eq_factorization_monomial

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.formalPrimeMonomial"
#check @Zeta23.OPICARound4.RegularCells.formalPrimeMonomial
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.formalPrimeMonomial"
#print axioms Zeta23.OPICARound4.RegularCells.formalPrimeMonomial

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_zero"
#check @Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_zero"
#print axioms Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_add"
#check @Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_add
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_add"
#print axioms Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_add

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.congr"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.congr
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.congr"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.congr

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.constant"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.constant
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.constant"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.constant

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.monomial"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.monomial
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.monomial"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.monomial

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_single"
#check @Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_single
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_single"
#print axioms Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_single

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.coordinate_zpow"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.coordinate_zpow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.coordinate_zpow"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.coordinate_zpow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.add"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.add
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.add"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.add

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.neg"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.neg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.neg"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.neg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sub"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sub
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sub"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sub

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.mul"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.mul
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.mul"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.mul

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sum"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sum"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.prod"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.prod
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.prod"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.prod

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.det"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.det
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.det"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.det

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.primePhaseUnits"
#check @Zeta23.OPICARound4.RegularCells.primePhaseUnits
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.primePhaseUnits"
#print axioms Zeta23.OPICARound4.RegularCells.primePhaseUnits

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_actual"
#check @Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_actual"
#print axioms Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.exists_nonzero_coefficient"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.exists_nonzero_coefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.exists_nonzero_coefficient"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.exists_nonzero_coefficient

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.actual_germ_nonzero"
#check @Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.actual_germ_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.actual_germ_nonzero"
#print axioms Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.actual_germ_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_ne_zero"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_ne_zero"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.exp_source_angle"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.exp_source_angle
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.exp_source_angle"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.exp_source_angle

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.exp_neg_source_angle"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.exp_neg_source_angle
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.exp_neg_source_angle"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.exp_neg_source_angle

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.potential_laurent"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.potential_laurent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.potential_laurent"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.potential_laurent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.diagonal_laurent"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.diagonal_laurent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.diagonal_laurent"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.diagonal_laurent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_one"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_one"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.frozenPrimeMatrix_laurent"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.frozenPrimeMatrix_laurent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.frozenPrimeMatrix_laurent"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.frozenPrimeMatrix_laurent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_eq"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_eq"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_zero"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_zero"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.tendsto_scaledPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.tendsto_scaledPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.tendsto_scaledPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.tendsto_scaledPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.meromorphicAt_formalPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.meromorphicAt_formalPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.meromorphicAt_formalPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.meromorphicAt_formalPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.primeCommonScalar"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.primeCommonScalar
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.primeCommonScalar"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.primeCommonScalar

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix_eq"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix_eq"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledFrozenPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledFrozenPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledFrozenPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledFrozenPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.center"
#check @Zeta23.OPICARound4.NativeZeroFrame.center
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.center"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.center

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.pos"
#check @Zeta23.OPICARound4.NativeZeroFrame.pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.pos"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.neg"
#check @Zeta23.OPICARound4.NativeZeroFrame.neg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.neg"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.neg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.centered_center"
#check @Zeta23.OPICARound4.NativeZeroFrame.centered_center
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.centered_center"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.centered_center

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.centered_pos"
#check @Zeta23.OPICARound4.NativeZeroFrame.centered_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.centered_pos"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.centered_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.centered_neg"
#check @Zeta23.OPICARound4.NativeZeroFrame.centered_neg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.centered_neg"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.centered_neg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldIndex"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldIndex
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldIndex"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldIndex

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldIndex_bijective"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldIndex_bijective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldIndex_bijective"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldIndex_bijective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldEquiv"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldEquiv"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.sum_fold"
#check @Zeta23.OPICARound4.NativeZeroFrame.sum_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.sum_fold"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.sum_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rev_pos"
#check @Zeta23.OPICARound4.NativeZeroFrame.rev_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rev_pos"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rev_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rev_center"
#check @Zeta23.OPICARound4.NativeZeroFrame.rev_center
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rev_center"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rev_center

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rev_neg"
#check @Zeta23.OPICARound4.NativeZeroFrame.rev_neg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rev_neg"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rev_neg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift_center"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift_center
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift_center"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift_center

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift_pos"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift_pos"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift_neg"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift_neg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift_neg"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift_neg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.fold_ext"
#check @Zeta23.OPICARound4.NativeZeroFrame.fold_ext
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.fold_ext"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.fold_ext

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift_even"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift_even
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift_even"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift_even

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.foldLift_odd"
#check @Zeta23.OPICARound4.NativeZeroFrame.foldLift_odd
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.foldLift_odd"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.foldLift_odd

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.moment_foldLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.moment_foldLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.moment_foldLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.moment_foldLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawOddLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawOddLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawOddLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawOddLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.index_ne_zero"
#check @Zeta23.OPICARound4.NativeZeroFrame.index_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.index_ne_zero"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.index_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawEvenLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawEvenLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawEvenLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawEvenLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawOddLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawOddLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawOddLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawOddLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_zero"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_zero"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_two"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_two
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_two"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_two

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_four"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_four
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_four"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_four

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_one"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_one"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_three"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_three
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_three"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_three

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_mem_iff"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_mem_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_mem_iff"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_mem_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_mem_iff"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_mem_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_mem_iff"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_mem_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.even_eq_fold"
#check @Zeta23.OPICARound4.NativeZeroFrame.even_eq_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.even_eq_fold"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.even_eq_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.odd_eq_fold"
#check @Zeta23.OPICARound4.NativeZeroFrame.odd_eq_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.odd_eq_fold"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.odd_eq_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates"
#check @Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawEvenLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawEvenLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawEvenLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawEvenLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawOddLift"
#check @Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawOddLift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawOddLift"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawOddLift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_positiveCoordinates"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_positiveCoordinates
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_positiveCoordinates"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_positiveCoordinates

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_positiveCoordinates"
#check @Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_positiveCoordinates
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_positiveCoordinates"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_positiveCoordinates

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingEvenCarrier_iff"
#check @Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingEvenCarrier_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingEvenCarrier_iff"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingEvenCarrier_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingOddCarrier_iff"
#check @Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingOddCarrier_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingOddCarrier_iff"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingOddCarrier_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.evenZeroEquiv"
#check @Zeta23.OPICARound4.NativeZeroFrame.evenZeroEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.evenZeroEquiv"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.evenZeroEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.oddZeroEquiv"
#check @Zeta23.OPICARound4.NativeZeroFrame.oddZeroEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.oddZeroEquiv"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.oddZeroEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.inner_even_fold"
#check @Zeta23.OPICARound4.NativeZeroFrame.inner_even_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.inner_even_fold"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.inner_even_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.inner_odd_fold"
#check @Zeta23.OPICARound4.NativeZeroFrame.inner_odd_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.inner_odd_fold"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.inner_odd_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_even_seed"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_even_seed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_even_seed"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_even_seed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_odd_seed"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_odd_seed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_odd_seed"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_odd_seed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_even_gram"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_even_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_even_gram"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_even_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeZeroFrame.zero_odd_gram"
#check @Zeta23.OPICARound4.NativeZeroFrame.zero_odd_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeZeroFrame.zero_odd_gram"
#print axioms Zeta23.OPICARound4.NativeZeroFrame.zero_odd_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression_isSymmetric"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression_isSymmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression_isSymmetric"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression_isSymmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSylvester"
#check @Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSylvester
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSylvester"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSylvester

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSeparationDet"
#check @Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSeparationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSeparationDet"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSeparationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_squared_ne_zero"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_squared_ne_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_squared_ne_zero"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_squared_ne_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeScaledCosineWeights"
#check @Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeScaledCosineWeights
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeScaledCosineWeights"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeScaledCosineWeights

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights_zero"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights_zero"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeScaledCosine_separation"
#check @Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeScaledCosine_separation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeScaledCosine_separation"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeScaledCosine_separation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights_affine"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights_affine
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights_affine"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights_affine

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_const"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_const
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_const"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_const

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_cosine"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_cosine
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_cosine"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_cosine

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_cosine"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_cosine
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_cosine"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_cosine

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeCosine_separation"
#check @Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeCosine_separation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeCosine_separation"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeCosine_separation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_injective"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_injective"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_separation"
#check @Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_separation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_separation"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_separation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_sylvester_injective"
#check @Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_sylvester_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_sylvester_injective"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_sylvester_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.isPreconnected_complexFrozenSourceDomain"
#check @Zeta23.OPICARound4.RegularCells.isPreconnected_complexFrozenSourceDomain
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.isPreconnected_complexFrozenSourceDomain"
#print axioms Zeta23.OPICARound4.RegularCells.isPreconnected_complexFrozenSourceDomain

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.isConnected_complexFrozenSourceDomain"
#check @Zeta23.OPICARound4.RegularCells.isConnected_complexFrozenSourceDomain
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.isConnected_complexFrozenSourceDomain"
#print axioms Zeta23.OPICARound4.RegularCells.isConnected_complexFrozenSourceDomain

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.eventually_mem_complexFrozenSourceDomain_at_zero"
#check @Zeta23.OPICARound4.RegularCells.eventually_mem_complexFrozenSourceDomain_at_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.eventually_mem_complexFrozenSourceDomain_at_zero"
#print axioms Zeta23.OPICARound4.RegularCells.eventually_mem_complexFrozenSourceDomain_at_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_nonzero_in_sourceDomain_of_germ"
#check @Zeta23.OPICARound4.RegularCells.exists_nonzero_in_sourceDomain_of_germ
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_nonzero_in_sourceDomain_of_germ"
#print axioms Zeta23.OPICARound4.RegularCells.exists_nonzero_in_sourceDomain_of_germ

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive"
#check @Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive"
#print axioms Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive_of_germ"
#check @Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive_of_germ
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive_of_germ"
#print axioms Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive_of_germ

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_finite_source_nonzero_in_open_positive_of_germ"
#check @Zeta23.OPICARound4.RegularCells.exists_finite_source_nonzero_in_open_positive_of_germ
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_finite_source_nonzero_in_open_positive_of_germ"
#print axioms Zeta23.OPICARound4.RegularCells.exists_finite_source_nonzero_in_open_positive_of_germ

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.oddNewborn_normalized_even_moment_cubic_energy_bound"
#check @Zeta23.OPICARound4.oddNewborn_normalized_even_moment_cubic_energy_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.oddNewborn_normalized_even_moment_cubic_energy_bound"
#print axioms Zeta23.OPICARound4.oddNewborn_normalized_even_moment_cubic_energy_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.evenNewborn_normalized_odd_corrected_energy_bound"
#check @Zeta23.OPICARound4.evenNewborn_normalized_odd_corrected_energy_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.evenNewborn_normalized_odd_corrected_energy_bound"
#print axioms Zeta23.OPICARound4.evenNewborn_normalized_odd_corrected_energy_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.exists_prime_below_cutoff_square_above"
#check @Zeta23.OPICARound4.PrimeIsolation.exists_prime_below_cutoff_square_above
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.exists_prime_below_cutoff_square_above"
#print axioms Zeta23.OPICARound4.PrimeIsolation.exists_prime_below_cutoff_square_above

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.prime_pow_below_square_eq"
#check @Zeta23.OPICARound4.PrimeIsolation.prime_pow_below_square_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.prime_pow_below_square_eq"
#print axioms Zeta23.OPICARound4.PrimeIsolation.prime_pow_below_square_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.primeSourceWeight_nonzero_isPrimePow"
#check @Zeta23.OPICARound4.PrimeIsolation.primeSourceWeight_nonzero_isPrimePow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.primeSourceWeight_nonzero_isPrimePow"
#print axioms Zeta23.OPICARound4.PrimeIsolation.primeSourceWeight_nonzero_isPrimePow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.weight_factorization_zero"
#check @Zeta23.OPICARound4.PrimeIsolation.weight_factorization_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.weight_factorization_zero"
#print axioms Zeta23.OPICARound4.PrimeIsolation.weight_factorization_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.singlePrimePhase"
#check @Zeta23.OPICARound4.PrimeIsolation.singlePrimePhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.singlePrimePhase"
#print axioms Zeta23.OPICARound4.PrimeIsolation.singlePrimePhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.monomial_singlePrimePhase"
#check @Zeta23.OPICARound4.PrimeIsolation.monomial_singlePrimePhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.monomial_singlePrimePhase"
#print axioms Zeta23.OPICARound4.PrimeIsolation.monomial_singlePrimePhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.weighted_single_prime_sum"
#check @Zeta23.OPICARound4.PrimeIsolation.weighted_single_prime_sum
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.weighted_single_prime_sum"
#print axioms Zeta23.OPICARound4.PrimeIsolation.weighted_single_prime_sum

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.scaledPrimeMatrix_one"
#check @Zeta23.OPICARound4.PrimeIsolation.scaledPrimeMatrix_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.scaledPrimeMatrix_one"
#print axioms Zeta23.OPICARound4.PrimeIsolation.scaledPrimeMatrix_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.scaledFrozenPrimeMatrix_single"
#check @Zeta23.OPICARound4.PrimeIsolation.scaledFrozenPrimeMatrix_single
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.scaledFrozenPrimeMatrix_single"
#print axioms Zeta23.OPICARound4.PrimeIsolation.scaledFrozenPrimeMatrix_single

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.circlePhase"
#check @Zeta23.OPICARound4.PrimeIsolation.circlePhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.circlePhase"
#print axioms Zeta23.OPICARound4.PrimeIsolation.circlePhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.circlePhase_zpow"
#check @Zeta23.OPICARound4.PrimeIsolation.circlePhase_zpow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.circlePhase_zpow"
#print axioms Zeta23.OPICARound4.PrimeIsolation.circlePhase_zpow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.circlePhase_symmetric"
#check @Zeta23.OPICARound4.PrimeIsolation.circlePhase_symmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.circlePhase_symmetric"
#print axioms Zeta23.OPICARound4.PrimeIsolation.circlePhase_symmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient"
#check @Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient"
#print axioms Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_pos"
#check @Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_pos"
#print axioms Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_eq"
#check @Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_eq"
#print axioms Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeIsolation.neg_scaledFrozen_single_zero"
#check @Zeta23.OPICARound4.PrimeIsolation.neg_scaledFrozen_single_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeIsolation.neg_scaledFrozen_single_zero"
#print axioms Zeta23.OPICARound4.PrimeIsolation.neg_scaledFrozen_single_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet_prime"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet_prime
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet_prime"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet_prime

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.primeFactors_subset_boundedPrimeSet"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.primeFactors_subset_boundedPrimeSet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.primeFactors_subset_boundedPrimeSet"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.primeFactors_subset_boundedPrimeSet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalExponent"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalExponent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalExponent"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalExponent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_eq_primePhase"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_eq_primePhase
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_eq_primePhase"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_eq_primePhase

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMonomial_zpow"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMonomial_zpow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMonomial_zpow"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMonomial_zpow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_zpow_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_zpow_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_zpow_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_zpow_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_eq"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_eq"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_actual"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_actual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_actual"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_actual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_det_expansion"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_det_expansion
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_det_expansion"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_det_expansion

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_mulVec"
#check @Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_mulVec
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_mulVec"
#print axioms Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_mulVec

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalScaledSourceMatrix"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalScaledSourceMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalScaledSourceMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalScaledSourceMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_rawPhysicalDiagonal"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_rawPhysicalDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_rawPhysicalDiagonal"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_rawPhysicalDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameGram"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameGram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameGram"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameGram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameSylvesterDet"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameSylvesterDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameSylvesterDet"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameSylvesterDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.actual_sylvester_germ_nonzero_of_formal_anchor"
#check @Zeta23.OPICARound4.PrimeSourceGerms.actual_sylvester_germ_nonzero_of_formal_anchor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.actual_sylvester_germ_nonzero_of_formal_anchor"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.actual_sylvester_germ_nonzero_of_formal_anchor

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.formalScaledSourceMatrix_single_zero"
#check @Zeta23.OPICARound4.PrimeSourceGerms.formalScaledSourceMatrix_single_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.formalScaledSourceMatrix_single_zero"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.formalScaledSourceMatrix_single_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_primeCommonScalar"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_primeCommonScalar
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_primeCommonScalar"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_primeCommonScalar

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualScaledSourceMatrix"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualScaledSourceMatrix
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualScaledSourceMatrix"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualScaledSourceMatrix

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualRawFrameSylvesterDet"
#check @Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualRawFrameSylvesterDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualRawFrameSylvesterDet"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualRawFrameSylvesterDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.PrimeSourceGerms.exists_actual_sylvester_nonzero_in_open_positive_of_anchor"
#check @Zeta23.OPICARound4.PrimeSourceGerms.exists_actual_sylvester_nonzero_in_open_positive_of_anchor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.PrimeSourceGerms.exists_actual_sylvester_nonzero_in_open_positive_of_anchor"
#print axioms Zeta23.OPICARound4.PrimeSourceGerms.exists_actual_sylvester_nonzero_in_open_positive_of_anchor

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.zeroCarrier"
#check @Zeta23.OPICARound4.NativeParityPencils.zeroCarrier
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.zeroCarrier"
#print axioms Zeta23.OPICARound4.NativeParityPencils.zeroCarrier

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.rawFrame"
#check @Zeta23.OPICARound4.NativeParityPencils.rawFrame
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.rawFrame"
#print axioms Zeta23.OPICARound4.NativeParityPencils.rawFrame

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalEquiv"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalEquiv"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_ofReal"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_ofReal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_ofReal"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_ofReal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_real_isSymmetric"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_real_isSymmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_real_isSymmetric"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_real_isSymmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_apply"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_apply"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_physical"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_physical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_physical"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_physical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameGram"
#check @Zeta23.OPICARound4.NativeParityPencils.frameGram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameGram"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameGram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameGram_physical"
#check @Zeta23.OPICARound4.NativeParityPencils.frameGram_physical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameGram_physical"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameGram_physical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_canonical_physical"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_canonical_physical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_canonical_physical"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_canonical_physical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameGram_zero"
#check @Zeta23.OPICARound4.NativeParityPencils.frameGram_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameGram_zero"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameGram_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource"
#check @Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource"
#print axioms Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalCommonShift"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalCommonShift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalCommonShift"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalCommonShift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource_eq"
#check @Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource_eq"
#print axioms Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_profiles"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_profiles
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_profiles"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_profiles

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_pole_zero"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_pole_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_pole_zero"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_pole_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_add"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_add
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_add"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_add

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_smul"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_smul
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_smul"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_smul

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_identity"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_identity"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_identity

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_sub"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_sub
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_sub"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_sub

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_scaledPhysicalSource"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_scaledPhysicalSource
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_scaledPhysicalSource"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_scaledPhysicalSource

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalAdjoint_injective"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalAdjoint_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalAdjoint_injective"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalAdjoint_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physical_pencil_eigen_iff"
#check @Zeta23.OPICARound4.NativeParityPencils.physical_pencil_eigen_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physical_pencil_eigen_iff"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physical_pencil_eigen_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physical_pencil_nonzero_eigen_iff"
#check @Zeta23.OPICARound4.NativeParityPencils.physical_pencil_nonzero_eigen_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physical_pencil_nonzero_eigen_iff"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physical_pencil_nonzero_eigen_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_even"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_even
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_even"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_even

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_odd"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_odd
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_odd"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_odd

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_even"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_even
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_even"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_even

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_odd"
#check @Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_odd
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_odd"
#print axioms Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_odd

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_weighted"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_weighted
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_weighted"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_weighted

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.centered_cosine_eq_fold"
#check @Zeta23.OPICARound4.NativeParityPencils.centered_cosine_eq_fold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.centered_cosine_eq_fold"
#print axioms Zeta23.OPICARound4.NativeParityPencils.centered_cosine_eq_fold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_cosine"
#check @Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_cosine
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_cosine"
#print axioms Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_cosine

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_matrix_injective"
#check @Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_matrix_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_matrix_injective"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_matrix_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_toEuclideanLin"
#check @Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_toEuclideanLin
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_toEuclideanLin"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_toEuclideanLin

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_injective_iff"
#check @Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_injective_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_injective_iff"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_injective_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_coordinate_injective"
#check @Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_coordinate_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_coordinate_injective"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_coordinate_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_intertwining"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_intertwining
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_intertwining"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_intertwining

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_injective_iff"
#check @Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_injective_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_injective_iff"
#print axioms Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_injective_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateIndex"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateIndex
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateIndex"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateIndex

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateIsometry"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateIsometry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateIsometry"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateIsometry

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_toEuclideanLin"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_toEuclideanLin
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_toEuclideanLin"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_toEuclideanLin

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.rawPhysicalDiagonal_eq"
#check @Zeta23.OPICARound4.NativeParityPencils.rawPhysicalDiagonal_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.rawPhysicalDiagonal_eq"
#print axioms Zeta23.OPICARound4.NativeParityPencils.rawPhysicalDiagonal_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.formalScaledSourceMatrix_actual_eq"
#check @Zeta23.OPICARound4.NativeParityPencils.formalScaledSourceMatrix_actual_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.formalScaledSourceMatrix_actual_eq"
#print axioms Zeta23.OPICARound4.NativeParityPencils.formalScaledSourceMatrix_actual_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinatePhysicalEquiv"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinatePhysicalEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinatePhysicalEquiv"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinatePhysicalEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram_physical"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram_physical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram_physical"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram_physical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy_physical"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy_physical
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy_physical"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy_physical

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_sylvester_det_iff"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_sylvester_det_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_sylvester_det_iff"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_sylvester_det_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalAdjointEquiv"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalAdjointEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalAdjointEquiv"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalAdjointEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.physicalFullPencil_injective_iff_disjoint"
#check @Zeta23.OPICARound4.NativeParityPencils.physicalFullPencil_injective_iff_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.physicalFullPencil_injective_iff_disjoint"
#print axioms Zeta23.OPICARound4.NativeParityPencils.physicalFullPencil_injective_iff_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_physical_det_iff_disjoint"
#check @Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_physical_det_iff_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_physical_det_iff_disjoint"
#print axioms Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_physical_det_iff_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.native_zero_single_prime_pencil"
#check @Zeta23.OPICARound4.NativeParityPencils.native_zero_single_prime_pencil
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.native_zero_single_prime_pencil"
#print axioms Zeta23.OPICARound4.NativeParityPencils.native_zero_single_prime_pencil

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_pencil_injective"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_pencil_injective
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_pencil_injective"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_pencil_injective

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.nativeFormalSeparationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.nativeFormalSeparationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.nativeFormalSeparationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.nativeFormalSeparationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_separation_anchor"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_separation_anchor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_separation_anchor"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_separation_anchor

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet_germ_nonzero"
#check @Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet_germ_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet_germ_nonzero"
#print axioms Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet_germ_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.analyticOnNhd_nativeActualSeparationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.analyticOnNhd_nativeActualSeparationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.analyticOnNhd_nativeActualSeparationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.analyticOnNhd_nativeActualSeparationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_nativeActualSeparationDet_nonzero_in_open_positive"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_nativeActualSeparationDet_nonzero_in_open_positive
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_nativeActualSeparationDet_nonzero_in_open_positive"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_nativeActualSeparationDet_nonzero_in_open_positive

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_finite_nativeActualSeparationDet_nonzero"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_finite_nativeActualSeparationDet_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_finite_nativeActualSeparationDet_nonzero"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_finite_nativeActualSeparationDet_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.isOpen_positive_nativeActualSeparationDet_nonzero"
#check @Zeta23.OPICARound4.NativeParityPencils.isOpen_positive_nativeActualSeparationDet_nonzero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.isOpen_positive_nativeActualSeparationDet_nonzero"
#print axioms Zeta23.OPICARound4.NativeParityPencils.isOpen_positive_nativeActualSeparationDet_nonzero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_regular_and_separationDet_in_open_fixedCell"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_regular_and_separationDet_in_open_fixedCell
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_regular_and_separationDet_in_open_fixedCell"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_regular_and_separationDet_in_open_fixedCell

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_bounded_regular_and_separationDet_in_open_above_one"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_bounded_regular_and_separationDet_in_open_above_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_bounded_regular_and_separationDet_in_open_above_one"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_bounded_regular_and_separationDet_in_open_above_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.cofinally_both_negative_regular_and_separationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.cofinally_both_negative_regular_and_separationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.cofinally_both_negative_regular_and_separationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.cofinally_both_negative_regular_and_separationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.separated_native_even_eigen_channels_visible"
#check @Zeta23.OPICARound4.separated_native_even_eigen_channels_visible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.separated_native_even_eigen_channels_visible"
#print axioms Zeta23.OPICARound4.separated_native_even_eigen_channels_visible

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.separated_native_odd_eigen_channels_visible"
#check @Zeta23.OPICARound4.separated_native_odd_eigen_channels_visible
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.separated_native_odd_eigen_channels_visible"
#print axioms Zeta23.OPICARound4.separated_native_odd_eigen_channels_visible

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.separated_native_even_eigenspace_finrank_le_one"
#check @Zeta23.OPICARound4.separated_native_even_eigenspace_finrank_le_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.separated_native_even_eigenspace_finrank_le_one"
#print axioms Zeta23.OPICARound4.separated_native_even_eigenspace_finrank_le_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.separated_native_odd_eigenspace_finrank_le_one"
#check @Zeta23.OPICARound4.separated_native_odd_eigenspace_finrank_le_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.separated_native_odd_eigenspace_finrank_le_one"
#print axioms Zeta23.OPICARound4.separated_native_odd_eigenspace_finrank_le_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.continuousAt_actual_original_phase_energy"
#check @Zeta23.OPICARound4.RegularCells.continuousAt_actual_original_phase_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.continuousAt_actual_original_phase_energy"
#print axioms Zeta23.OPICARound4.RegularCells.continuousAt_actual_original_phase_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_actual_original_depth_transport_threshold"
#check @Zeta23.OPICARound4.RegularCells.exists_actual_original_depth_transport_threshold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_actual_original_depth_transport_threshold"
#print axioms Zeta23.OPICARound4.RegularCells.exists_actual_original_depth_transport_threshold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_with_open_selection"
#check @Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_with_open_selection
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_with_open_selection"
#print axioms Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_with_open_selection

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_native_regular"
#check @Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_native_regular
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_native_regular"
#print axioms Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_native_regular

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.exists_actual_composed_packet_native_regular"
#check @Zeta23.OPICARound4.RegularCells.exists_actual_composed_packet_native_regular
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.exists_actual_composed_packet_native_regular"
#print axioms Zeta23.OPICARound4.RegularCells.exists_actual_composed_packet_native_regular

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.RegularCells.cofinally_actual_regular_packet_joint_detector_ground"
#check @Zeta23.OPICARound4.RegularCells.cofinally_actual_regular_packet_joint_detector_ground
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.RegularCells.cofinally_actual_regular_packet_joint_detector_ground"
#print axioms Zeta23.OPICARound4.RegularCells.cofinally_actual_regular_packet_joint_detector_ground

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_actual_generated_packet_regular_separationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_actual_generated_packet_regular_separationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_actual_generated_packet_regular_separationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_actual_generated_packet_regular_separationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.exists_actual_composed_packet_regular_separationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.exists_actual_composed_packet_regular_separationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.exists_actual_composed_packet_regular_separationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.exists_actual_composed_packet_regular_separationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_separationDet"
#check @Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_separationDet
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_separationDet"
#print axioms Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_separationDet

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra"
#check @Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra"
#print axioms Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.limiting_full_compressions_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.limiting_full_compressions_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.limiting_full_compressions_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.limiting_full_compressions_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.grouped_genuine_prime_laurent_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.grouped_genuine_prime_laurent_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.grouped_genuine_prime_laurent_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.grouped_genuine_prime_laurent_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.actual_full_source_nonidentity_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.actual_full_source_nonidentity_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.actual_full_source_nonidentity_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.actual_full_source_nonidentity_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.bounded_actual_regular_separation_selection_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.bounded_actual_regular_separation_selection_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.bounded_actual_regular_separation_selection_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.bounded_actual_regular_separation_selection_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.complete_even_source_and_eigenspace_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.complete_even_source_and_eigenspace_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.complete_even_source_and_eigenspace_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.complete_even_source_and_eigenspace_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.complete_odd_source_and_eigenspace_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.complete_odd_source_and_eigenspace_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.complete_odd_source_and_eigenspace_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.complete_odd_source_and_eigenspace_check

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_spectral_check"
#check @Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_spectral_check
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_spectral_check"
#print axioms Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_spectral_check

-- Exact fixed-margin and moment-slice extension; prior audit bytes are retained.
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 2000000

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFiniteApprox_interval_energy"
#check @Zeta23.OPICARound4.recenteredFiniteApprox_interval_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFiniteApprox_interval_energy"
#print axioms Zeta23.OPICARound4.recenteredFiniteApprox_interval_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredSmoothPhase_interval_energy_eq_one"
#check @Zeta23.OPICARound4.recenteredSmoothPhase_interval_energy_eq_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredSmoothPhase_interval_energy_eq_one"
#print axioms Zeta23.OPICARound4.recenteredSmoothPhase_interval_energy_eq_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recenteredFinitePhase_mass_error_le"
#check @Zeta23.OPICARound4.recenteredFinitePhase_mass_error_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recenteredFinitePhase_mass_error_le"
#print axioms Zeta23.OPICARound4.recenteredFinitePhase_mass_error_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exists_recentered_mass_control_threshold"
#check @Zeta23.OPICARound4.exists_recentered_mass_control_threshold
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exists_recentered_mass_control_threshold"
#print axioms Zeta23.OPICARound4.exists_recentered_mass_control_threshold

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.recentered_negative_phase_eventually_relative_margin"
#check @Zeta23.OPICARound4.recentered_negative_phase_eventually_relative_margin
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.recentered_negative_phase_eventually_relative_margin"
#print axioms Zeta23.OPICARound4.recentered_negative_phase_eventually_relative_margin

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventually_both_ground_margins_at_original_quartic"
#check @Zeta23.OPICARound4.eventually_both_ground_margins_at_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventually_both_ground_margins_at_original_quartic"
#print axioms Zeta23.OPICARound4.eventually_both_ground_margins_at_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.originalDetectorFiniteEvenPhase_moment_four"
#check @Zeta23.OPICARound4.originalDetectorFiniteEvenPhase_moment_four
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.originalDetectorFiniteEvenPhase_moment_four"
#print axioms Zeta23.OPICARound4.originalDetectorFiniteEvenPhase_moment_four

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_three"
#check @Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_three
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_three"
#print axioms Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_three

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_five"
#check @Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_five
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_five"
#print axioms Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_five

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventually_both_negative_moment_slices_at_original_quartic"
#check @Zeta23.OPICARound4.eventually_both_negative_moment_slices_at_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventually_both_negative_moment_slices_at_original_quartic"
#print axioms Zeta23.OPICARound4.eventually_both_negative_moment_slices_at_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.eventually_both_moment_slice_margins_at_original_quartic"
#check @Zeta23.OPICARound4.eventually_both_moment_slice_margins_at_original_quartic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.eventually_both_moment_slice_margins_at_original_quartic"
#print axioms Zeta23.OPICARound4.eventually_both_moment_slice_margins_at_original_quartic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_recentered_mass_error_consumer"
#check @Zeta23.OPICARound4.Validation.actual_recentered_mass_error_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_recentered_mass_error_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_recentered_mass_error_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.Validation.actual_both_moment_slice_margins_consumer"
#check @Zeta23.OPICARound4.Validation.actual_both_moment_slice_margins_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.Validation.actual_both_moment_slice_margins_consumer"
#print axioms Zeta23.OPICARound4.Validation.actual_both_moment_slice_margins_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_apply"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_apply"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_apply"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_apply
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_apply"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_apply

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.mem_evenMomentSlice_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.mem_evenMomentSlice_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.mem_evenMomentSlice_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.mem_evenMomentSlice_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.mem_oddMomentSlice_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.mem_oddMomentSlice_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.mem_oddMomentSlice_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.mem_oddMomentSlice_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound"
#check @Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound"
#check @Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound"
#check @Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceVanishingErrorBounds"
#check @Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceVanishingErrorBounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceVanishingErrorBounds"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceVanishingErrorBounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound.mono"
#check @Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound.mono
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound.mono"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound.mono

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound.mono"
#check @Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound.mono
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound.mono"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound.mono

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound.mono"
#check @Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound.mono
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound.mono"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound.mono

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_bottom"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_bottom
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_bottom"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_bottom

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_bottom"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_bottom
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_bottom"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_bottom

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slice_witnesses"
#check @Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slice_witnesses
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slice_witnesses"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slice_witnesses

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.eventually_no_moment_slice_lower_bound_below_margin"
#check @Zeta23.OPICARound4.ArithmeticFrontier.eventually_no_moment_slice_lower_bound_below_margin
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.eventually_no_moment_slice_lower_bound_below_margin"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.eventually_no_moment_slice_lower_bound_below_margin

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.spec_chart_eq_fixedSeedDiagonalEntry"
#check @Zeta23.OPICARound4.ArithmeticFrontier.spec_chart_eq_fixedSeedDiagonalEntry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.spec_chart_eq_fixedSeedDiagonalEntry"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.spec_chart_eq_fixedSeedDiagonalEntry

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenMomentSeed"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenMomentSeed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenMomentSeed"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenMomentSeed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedOddMomentSeed"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedOddMomentSeed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedOddMomentSeed"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedOddMomentSeed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedEvenMomentSeed_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedEvenMomentSeed_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedEvenMomentSeed_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedEvenMomentSeed_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedOddMomentSeed_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedOddMomentSeed_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedOddMomentSeed_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedOddMomentSeed_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_four_of_seed"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_four_of_seed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_four_of_seed"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_four_of_seed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_three_of_seed"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_three_of_seed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_three_of_seed"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_three_of_seed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_five_of_seed"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_five_of_seed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_five_of_seed"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_five_of_seed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenSeedPhysicalEquiv_mem_slice_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenSeedPhysicalEquiv_mem_slice_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenSeedPhysicalEquiv_mem_slice_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenSeedPhysicalEquiv_mem_slice_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedOddSeedPhysicalEquiv_mem_slice_iff"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedOddSeedPhysicalEquiv_mem_slice_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedOddSeedPhysicalEquiv_mem_slice_iff"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedOddSeedPhysicalEquiv_mem_slice_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_inner"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_inner
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_inner"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_inner

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_inner"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_inner
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_inner"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_inner

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_norm_sq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_norm_sq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_norm_sq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_norm_sq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_norm_sq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_norm_sq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_seed_gram"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_seed_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_seed_gram"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_seed_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_seed_gram"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_seed_gram
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_seed_gram"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_seed_gram

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.seedCoordinateNormSq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.seedCoordinateNormSq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.seedCoordinateNormSq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.seedCoordinateNormSq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_eq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_eq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_ge"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_ge
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_ge"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_ge

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_le"
#check @Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_le"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_coordinate_tolerance"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_coordinate_tolerance
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_coordinate_tolerance"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_coordinate_tolerance

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.coordinate_tolerance_of_evenMomentSliceLowerBound"
#check @Zeta23.OPICARound4.ArithmeticFrontier.coordinate_tolerance_of_evenMomentSliceLowerBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.coordinate_tolerance_of_evenMomentSliceLowerBound"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.coordinate_tolerance_of_evenMomentSliceLowerBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedEvenSeed_sixth_moment_one"
#check @Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedEvenSeed_sixth_moment_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedEvenSeed_sixth_moment_one"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedEvenSeed_sixth_moment_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_fifth_moment_one"
#check @Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_fifth_moment_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_fifth_moment_one"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_fifth_moment_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_seventh_moment_one"
#check @Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_seventh_moment_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_seventh_moment_one"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_seventh_moment_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.finrank_evenMomentSlice"
#check @Zeta23.OPICARound4.ArithmeticFrontier.finrank_evenMomentSlice
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.finrank_evenMomentSlice"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.finrank_evenMomentSlice

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.finrank_oddMomentSlice"
#check @Zeta23.OPICARound4.ArithmeticFrontier.finrank_oddMomentSlice
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.finrank_oddMomentSlice"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.finrank_oddMomentSlice

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.quartic_moment_slices_nontrivial"
#check @Zeta23.OPICARound4.ArithmeticFrontier.quartic_moment_slices_nontrivial
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.quartic_moment_slices_nontrivial"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.quartic_moment_slices_nontrivial

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice_eq_bot_of_le_three"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice_eq_bot_of_le_three
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice_eq_bot_of_le_three"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice_eq_bot_of_le_three

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice_eq_bot_of_le_four"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice_eq_bot_of_le_four
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice_eq_bot_of_le_four"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice_eq_bot_of_le_four

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_three"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_three
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_three"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_three

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_le_four"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_le_four
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_le_four"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_le_four

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_moment_slice_bounds"
#check @Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_moment_slice_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_moment_slice_bounds"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_moment_slice_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds"
#check @Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_bounds_of_off_line_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_bounds_of_off_line_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_bounds_of_off_line_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_bounds_of_off_line_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_even"
#check @Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_even
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_even"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_even

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_odd"
#check @Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_odd
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_odd"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_odd

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_tendsto"
#check @Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_tendsto
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_tendsto"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_tendsto

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.NativeGroundResponseRestriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.NativeGroundResponseRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.NativeGroundResponseRestriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.NativeGroundResponseRestriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.NativeSpectraDisjoint"
#check @Zeta23.OPICARound4.ArithmeticFrontier.NativeSpectraDisjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.NativeSpectraDisjoint"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.NativeSpectraDisjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.rayleighBottoms_ne_of_spectra_disjoint"
#check @Zeta23.OPICARound4.ArithmeticFrontier.rayleighBottoms_ne_of_spectra_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.rayleighBottoms_ne_of_spectra_disjoint"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.rayleighBottoms_ne_of_spectra_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.noBothNeg_of_ground_response_and_disjoint_spectra"
#check @Zeta23.OPICARound4.ArithmeticFrontier.noBothNeg_of_ground_response_and_disjoint_spectra
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.noBothNeg_of_ground_response_and_disjoint_spectra"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.noBothNeg_of_ground_response_and_disjoint_spectra

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.packetAperture"
#check @Zeta23.OPICARound4.ArithmeticFrontier.packetAperture
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.packetAperture"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.packetAperture

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_pos"
#check @Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_pos"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_gt"
#check @Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_gt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_gt"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_gt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.packetDetectorCutoff_three_le"
#check @Zeta23.OPICARound4.ArithmeticFrontier.packetDetectorCutoff_three_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.packetDetectorCutoff_three_le"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.packetDetectorCutoff_three_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketGroundRestriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketGroundRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketGroundRestriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketGroundRestriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_ground_restriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_ground_restriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_ground_restriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_ground_restriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.EventualDisjointQuarticGroundRestriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.EventualDisjointQuarticGroundRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.EventualDisjointQuarticGroundRestriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.EventualDisjointQuarticGroundRestriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.selected_packet_ground_restriction_of_eventual_disjoint"
#check @Zeta23.OPICARound4.ArithmeticFrontier.selected_packet_ground_restriction_of_eventual_disjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.selected_packet_ground_restriction_of_eventual_disjoint"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.selected_packet_ground_restriction_of_eventual_disjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.eventual_disjoint_quartic_ground_restriction_of_ground_closure"
#check @Zeta23.OPICARound4.ArithmeticFrontier.eventual_disjoint_quartic_ground_restriction_of_ground_closure
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.eventual_disjoint_quartic_ground_restriction_of_ground_closure"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.eventual_disjoint_quartic_ground_restriction_of_ground_closure

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketWithGroundRestriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketWithGroundRestriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketWithGroundRestriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketWithGroundRestriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_with_ground_restriction"
#check @Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_with_ground_restriction
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_with_ground_restriction"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_with_ground_restriction

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy"
#check @Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.correctedSchurForm"
#check @Zeta23.OPICARound4.ArithmeticFrontier.correctedSchurForm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.correctedSchurForm"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.correctedSchurForm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.inverseResidual"
#check @Zeta23.OPICARound4.ArithmeticFrontier.inverseResidual
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.inverseResidual"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.inverseResidual

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_eq_residual_form"
#check @Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_eq_residual_form
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_eq_residual_form"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_eq_residual_form

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate"
#check @Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.schur_inverse_residual_identity"
#check @Zeta23.OPICARound4.ArithmeticFrontier.schur_inverse_residual_identity
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.schur_inverse_residual_identity"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.schur_inverse_residual_identity

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_scalar_gap"
#check @Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_scalar_gap
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_scalar_gap"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_scalar_gap

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.shifted_form_mono"
#check @Zeta23.OPICARound4.ArithmeticFrontier.shifted_form_mono
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.shifted_form_mono"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.shifted_form_mono

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.CoreLeakageBound"
#check @Zeta23.OPICARound4.ArithmeticFrontier.CoreLeakageBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.CoreLeakageBound"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.CoreLeakageBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.selfAdjoint_energy_split"
#check @Zeta23.OPICARound4.ArithmeticFrontier.selfAdjoint_energy_split
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.selfAdjoint_energy_split"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.selfAdjoint_energy_split

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate"
#check @Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate_of_columns"
#check @Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate_of_columns
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate_of_columns"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate_of_columns

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.core_witness_transport"
#check @Zeta23.OPICARound4.ArithmeticFrontier.core_witness_transport
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.core_witness_transport"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.core_witness_transport

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.cofinal_moment_closure_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.cofinal_moment_closure_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.cofinal_moment_closure_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.cofinal_moment_closure_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.moment_slice_witness_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.moment_slice_witness_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.moment_slice_witness_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.moment_slice_witness_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.quartic_slice_dimension_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.quartic_slice_dimension_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.quartic_slice_dimension_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.quartic_slice_dimension_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.seed_gram_transport_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.seed_gram_transport_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.seed_gram_transport_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.seed_gram_transport_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.disjoint_quartic_ground_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.disjoint_quartic_ground_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.disjoint_quartic_ground_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.disjoint_quartic_ground_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.inverse_residual_certificate_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.inverse_residual_certificate_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.inverse_residual_certificate_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.inverse_residual_certificate_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.Validation.core_shift_consumer"
#check @Zeta23.OPICARound4.ArithmeticFrontier.Validation.core_shift_consumer
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.Validation.core_shift_consumer"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.Validation.core_shift_consumer

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_dot_oddBoundaryFlat_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_dot_oddBoundaryFlat_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_dot_oddBoundaryFlat_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_dot_oddBoundaryFlat_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_even_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_even_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_even_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_even_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_odd_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_odd_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_odd_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_odd_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_even_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_even_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_even_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_even_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_odd_eq_zero"
#check @Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_odd_eq_zero
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_odd_eq_zero"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_odd_eq_zero

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy_eq_neg_arch_sub_prime"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy_eq_neg_arch_sub_prime
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy_eq_neg_arch_sub_prime"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy_eq_neg_arch_sub_prime

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy_eq_neg_arch_sub_prime"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy_eq_neg_arch_sub_prime
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy_eq_neg_arch_sub_prime"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy_eq_neg_arch_sub_prime

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_arch_prime"
#check @Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_arch_prime
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_arch_prime"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_arch_prime

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_arch_prime"
#check @Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_arch_prime
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_arch_prime"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_arch_prime

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.leakage_adjoint"
#check @Zeta23.OPICARound4.ArithmeticFrontier.leakage_adjoint
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.leakage_adjoint"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.leakage_adjoint

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.compressed_geometry_mul_energy"
#check @Zeta23.OPICARound4.ArithmeticFrontier.compressed_geometry_mul_energy
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.compressed_geometry_mul_energy"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.compressed_geometry_mul_energy

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.compressed_energy_mul_geometry"
#check @Zeta23.OPICARound4.ArithmeticFrontier.compressed_energy_mul_geometry
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.compressed_energy_mul_geometry"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.compressed_energy_mul_geometry

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_one_normal"
#check @Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_one_normal
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_one_normal"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_one_normal

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_of_no_leakage"
#check @Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_of_no_leakage
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_of_no_leakage"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_of_no_leakage

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.froSq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.froSq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.froSq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.froSq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_add"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_add
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_add"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_add

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sub"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sub
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sub"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sub

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_smul"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_smul
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_smul"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_smul

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_one"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_one
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_one"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_one

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_mul_transpose_nonneg"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_mul_transpose_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_mul_transpose_nonneg"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_mul_transpose_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sq_le"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sq_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sq_le"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sq_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq_pos"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq_pos
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq_pos"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq_pos

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_near_shift"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_near_shift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_near_shift"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_near_shift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.pencil_checkpoint_of_posDef"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.pencil_checkpoint_of_posDef
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.pencil_checkpoint_of_posDef"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.pencil_checkpoint_of_posDef

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.shifted_factor_requires_positive_shift"
#check @Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.shifted_factor_requires_positive_shift
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.shifted_factor_requires_positive_shift"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.shifted_factor_requires_positive_shift

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_gram_eq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_gram_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_gram_eq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_gram_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_energy_eq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_energy_eq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_energy_eq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_energy_eq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_conjTranspose"
#check @Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_conjTranspose
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_conjTranspose"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_conjTranspose

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_idempotent"
#check @Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_idempotent
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_idempotent"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_idempotent

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.complementProjection_sq"
#check @Zeta23.OPICARound4.ArithmeticFrontier.complementProjection_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.complementProjection_sq"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.complementProjection_sq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_residual_trace"
#check @Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_residual_trace
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_residual_trace"
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_residual_trace
