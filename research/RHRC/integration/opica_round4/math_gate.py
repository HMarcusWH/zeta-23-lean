"""Current-source Lean support gate; all new outputs are external.

The caller prepares native parent/package objects once.  This runner performs
no broad build, cache download, pin change, or write to those input objects.
It compiles every owned module, the independent consumers, and the full audit.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import time

# Direct CLI execution resolves package helpers from this trusted source tree.
if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[4]))

BASELINE_EXPECTED_DECLARATIONS = [
  "Zeta23.OPICARound4.even_absolute_energy_anchor",
  "Zeta23.OPICARound4.odd_absolute_energy_anchor",
  "Zeta23.OPICARound4.real_scalar_shift_energy",
  "Zeta23.OPICARound4.scalar_shift_negative_control",
  "Zeta23.OPICARound4.no_even_eigen_from_independent_ray_bound",
  "Zeta23.OPICARound4.no_odd_eigen_from_independent_ray_bound",
  "Zeta23.OPICARound4.native_index_inverse_cost",
  "Zeta23.OPICARound4.native_even_bottom_le_quotient",
  "Zeta23.OPICARound4.native_odd_bottom_le_quotient",
  "Zeta23.OPICARound4.native_bottom_le_quotient",
  "Zeta23.OPICARound4.newborn_bottom_le_normalized_energy",
  "Zeta23.OPICARound4.newborn_witness_norm_branches",
  "Zeta23.OPICARound4.even_negative_witness_ground",
  "Zeta23.OPICARound4.odd_negative_witness_ground",
  "Zeta23.OPICARound4.common_cutoff_negative_ground_alternatives",
  "Zeta23.OPICARound4.even_eigenvectors_source_collinear",
  "Zeta23.OPICARound4.odd_eigenvectors_source_collinear",
  "Zeta23.OPICARound4.negative_subspace_finrank_le_shell",
  "Zeta23.OPICARound4.one_shell_negative_index_at_most_one",
  "Zeta23.OPICARound4.negative_vector_spans_negative_line",
  "Zeta23.OPICARound4.one_shell_negative_index_exact",
  "Zeta23.OPICARound4.nativeIndexInverseAdjoint",
  "Zeta23.OPICARound4.nativeIndexAdjointInverseAdjoint",
  "Zeta23.OPICARound4.hermitian_resolvent_signed_upper",
  "Zeta23.OPICARound4.native_even_signed_upper",
  "Zeta23.OPICARound4.native_odd_inverse_adjoint_eq_inverse",
  "Zeta23.OPICARound4.native_odd_signed_upper",
  "Zeta23.OPICARound4.RegularCells.frozen_source_cell_consumer",
  "Zeta23.OPICARound4.RegularCells.frozen_source_neutral_action",
  "Zeta23.OPICARound4.common_scalar_shift_invariant",
  "Zeta23.OPICARound4.orthogonal_source_row_shift",
  "Zeta23.OPICARound4.realCrossResidue",
  "Zeta23.OPICARound4.realCrossResidue_sum",
  "Zeta23.OPICARound4.realCrossResidue_variation_le",
  "Zeta23.OPICARound4.diagonalSpectralResolvent",
  "Zeta23.OPICARound4.diagonal_resolvent_response",
  "Zeta23.OPICARound4.diagonal_signed_norm_upper",
  "Zeta23.OPICARound4.signedSpectralResponse",
  "Zeta23.OPICARound4.signed_response_hasDerivAt",
  "Zeta23.OPICARound4.resolvent_kernel_unit_interval",
  "Zeta23.OPICARound4.signed_kernel_upper",
  "Zeta23.OPICARound4.signed_resolvent_upper",
  "Zeta23.OPICARound4.signed_response_lt_one_of_budget",
  "Zeta23.OPICARound4.signedPrefix",
  "Zeta23.OPICARound4.signed_prefix_abel",
  "Zeta23.OPICARound4.signed_prefix_nonnegative",
  "Zeta23.OPICARound4.sourceAtomPairing_eq_physical_inner",
  "Zeta23.OPICARound4.correctedSourceTest",
  "Zeta23.OPICARound4.correctedSourceTest_eq_inner",
  "Zeta23.OPICARound4.correctedSourceTest_lower_endpoint",
  "Zeta23.OPICARound4.correctedSourceTest_upper_endpoint",
  "Zeta23.OPICARound4.correctedSourceTest_hasDerivAt",
  "Zeta23.OPICARound4.correctedSourceTest_prime_pairing",
  "Zeta23.OPICARound4.correctedSourceTest_complete_arithmetic",
  "Zeta23.OPICARound4.actual_even_ray_test_prerequisites",
  "Zeta23.OPICARound4.actual_odd_resolvent_test_prerequisites",
  "Zeta23.OPICARound4.correctedSourceRow",
  "Zeta23.OPICARound4.correctedSourceRow_pairing",
  "Zeta23.OPICARound4.correctedSourceRow_orthogonal",
  "Zeta23.OPICARound4.correctedSourceRow_native",
  "Zeta23.OPICARound4.correctedSourceRow_pole_cancelled",
  "Zeta23.OPICARound4.correctedSourceRow_scalar_shift",
  "Zeta23.OPICARound4.rank_one_trace_displacement",
  "Zeta23.OPICARound4.rank_one_metric_identity",
  "Zeta23.OPICARound4.native_even_trace_displacement",
  "Zeta23.OPICARound4.native_odd_trace_displacement",
  "Zeta23.OPICARound4.Validation.native_inverse_cost_consumer",
  "Zeta23.OPICARound4.Validation.even_physical_quotient_consumer",
  "Zeta23.OPICARound4.Validation.odd_physical_quotient_consumer",
  "Zeta23.OPICARound4.Validation.native_newborn_normalized_cost_consumer",
  "Zeta23.OPICARound4.Validation.common_cutoff_source_or_shared_ground_consumer",
  "Zeta23.OPICARound4.Validation.corrected_native_row_consumer",
  "Zeta23.OPICARound4.Validation.complete_arithmetic_consumer",
  "Zeta23.OPICARound4.Validation.source_test_endpoint_consumer",
  "Zeta23.OPICARound4.Validation.source_test_derivative_consumer",
  "Zeta23.OPICARound4.Validation.exact_negative_index_consumer",
  "Zeta23.OPICARound4.Validation.trace_displacement_consumer",
  "Zeta23.OPICARound4.Validation.nonunit_metric_consumer",
  "Zeta23.OPICARound4.Validation.signed_resolvent_budget_consumer",
  "Zeta23.OPICARound4.Validation.signed_prefix_comparison_consumer",
  "Zeta23.OPICARound4.Validation.frozen_source_cell_consumer",
  "Zeta23.OPICARound4.Validation.actual_even_signed_bound_consumer",
  "Zeta23.OPICARound4.Validation.actual_odd_signed_bound_consumer",
  "Zeta23.OPICARound4.Validation.physical_shell_norm_consumer",
  "Zeta23.OPICARound4.Validation.regular_witness_norm_consumer",
  "Zeta23.OPICARound4.Validation.resonant_witness_norm_consumer",
  "Zeta23.OPICARound4.Validation.regular_witness_rayleigh_consumer",
  "Zeta23.OPICARound4.Validation.resonant_witness_rayleigh_consumer",
  "Zeta23.OPICARound4.Validation.common_scalar_shift_consumer",
  "Zeta23.OPICARound4.Validation.orthogonal_source_row_consumer",
  "Zeta23.OPICARound4.Validation.even_source_bound_consumer",
  "Zeta23.OPICARound4.Validation.odd_source_bound_consumer",
  "Zeta23.OPICARound4.shell_sub_norm_sq",
  "Zeta23.OPICARound4.regular_witness_norm_sq",
  "Zeta23.OPICARound4.resonant_witness_norm_sq",
  "Zeta23.OPICARound4.rayleighEnergy",
  "Zeta23.OPICARound4.regular_witness_rayleigh",
  "Zeta23.OPICARound4.resonant_witness_rayleigh"
]
BASELINE_MODULES = [
  "Zeta23.OPICARound4",
  "Zeta23.OPICARound4.AbsoluteAnchor",
  "Zeta23.OPICARound4.NativeRayConsumer",
  "Zeta23.OPICARound4.NativeWitnessCosts",
  "Zeta23.OPICARound4.NegativeIndex",
  "Zeta23.OPICARound4.OperatorSignedBound",
  "Zeta23.OPICARound4.RegularCells.SourceSupport",
  "Zeta23.OPICARound4.ScalarShift",
  "Zeta23.OPICARound4.SignedNormBound",
  "Zeta23.OPICARound4.SignedSpectral",
  "Zeta23.OPICARound4.SourceDiscrepancy",
  "Zeta23.OPICARound4.SourceRow",
  "Zeta23.OPICARound4.TraceMetric",
  "Zeta23.OPICARound4.Validation",
  "Zeta23.OPICARound4.Validation.Support",
  "Zeta23.OPICARound4.WitnessNorms"
]
INTEGRATION_EXPECTED_DECLARATIONS = BASELINE_EXPECTED_DECLARATIONS + [
  "Zeta23.OPICARound4.EvenNegativeGroundRestriction",
  "Zeta23.OPICARound4.EventualActualRayClosure",
  "Zeta23.OPICARound4.EventualNativeJointNegativeIndexCap",
  "Zeta23.OPICARound4.EventualNegativeGroundClosure",
  "Zeta23.OPICARound4.GroupedInputInvisible",
  "Zeta23.OPICARound4.GroupedOutputInvisible",
  "Zeta23.OPICARound4.GroupedSpectrum",
  "Zeta23.OPICARound4.IntegrationClosureTarget",
  "Zeta23.OPICARound4.IntegrationJointIndexTarget",
  "Zeta23.OPICARound4.IntegrationSourceBudgetTarget",
  "Zeta23.OPICARound4.NativeJointNegativeIndexAtMostOne",
  "Zeta23.OPICARound4.NativeNegativeObservationBound",
  "Zeta23.OPICARound4.NativePhysicalNeutralSubspace",
  "Zeta23.OPICARound4.OddNegativeGroundRestriction",
  "Zeta23.OPICARound4.RegularCells.centeredMoment_fixedSeedDiagonal",
  "Zeta23.OPICARound4.RegularCells.even_pole_fixedSeedDiagonal",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeed",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeedToPhysical",
  "Zeta23.OPICARound4.RegularCells.fixedEvenSeed_diagonal_iff",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeed",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeedToPhysical",
  "Zeta23.OPICARound4.RegularCells.fixedOddSeed_diagonal_iff",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEntry_pos",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonalEquiv",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_apply",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_even_iff",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_odd_iff",
  "Zeta23.OPICARound4.RegularCells.fixedSeedDiagonal_reverse",
  "Zeta23.OPICARound4.RegularCells.fixedSeedGram",
  "Zeta23.OPICARound4.RegularCells.fixedSeedGram_eq_physical_inner",
  "Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos",
  "Zeta23.OPICARound4.RegularCells.fixedSeedParameter",
  "Zeta23.OPICARound4.RegularCells.mem_fixedEvenSeed_iff",
  "Zeta23.OPICARound4.RegularCells.mem_fixedOddSeed_iff",
  "Zeta23.OPICARound4.RegularCells.odd_pole_fixedSeedDiagonal",
  "Zeta23.OPICARound4.RegularCells.poleEvenProfile_fixedSeedDiagonalEntry",
  "Zeta23.OPICARound4.RegularCells.poleOddProfile_fixedSeedDiagonalEntry",
  "Zeta23.OPICARound4.SearchSupport.index_two_contradicts_cap",
  "Zeta23.OPICARound4.SearchSupport.strict_response_of_signed_upper",
  "Zeta23.OPICARound4.StrictlyNegativeNativeSubspace",
  "Zeta23.OPICARound4.UniformPrimeDiscrepancyBound",
  "Zeta23.OPICARound4.Validation.actual_ground_closure_consumer",
  "Zeta23.OPICARound4.Validation.actual_ray_closure_consumer",
  "Zeta23.OPICARound4.Validation.allNegativeFamilyA",
  "Zeta23.OPICARound4.Validation.allNegativeFamilyB",
  "Zeta23.OPICARound4.Validation.allNegativeSpectralValue",
  "Zeta23.OPICARound4.Validation.allNegativeSpectralValue_injective",
  "Zeta23.OPICARound4.Validation.all_negative_family_coordinate_coefficient",
  "Zeta23.OPICARound4.Validation.all_negative_family_hermitian",
  "Zeta23.OPICARound4.Validation.all_negative_family_rank_one",
  "Zeta23.OPICARound4.Validation.arbitrarily_many_negative_atoms",
  "Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer",
  "Zeta23.OPICARound4.Validation.declared_input_reachability_consumer",
  "Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer",
  "Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer",
  "Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer",
  "Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer",
  "Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer",
  "Zeta23.OPICARound4.Validation.finite_observation_energy_consumer",
  "Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer",
  "Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer",
  "Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer",
  "Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer",
  "Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer",
  "Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer",
  "Zeta23.OPICARound4.Validation.general_cross_observation_cancellation",
  "Zeta23.OPICARound4.Validation.grouped_upper_away",
  "Zeta23.OPICARound4.Validation.hermitianUpperResponse",
  "Zeta23.OPICARound4.Validation.hermitian_rank_one_upper_pick_identity",
  "Zeta23.OPICARound4.Validation.hermitian_upper_response_expansion",
  "Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer",
  "Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer",
  "Zeta23.OPICARound4.Validation.invisible_shared_mode_control",
  "Zeta23.OPICARound4.Validation.nativeEvenUpperResponse",
  "Zeta23.OPICARound4.Validation.nativeOddUpperResponse",
  "Zeta23.OPICARound4.Validation.native_even_invisible_eigen_shared",
  "Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer",
  "Zeta23.OPICARound4.Validation.native_even_upper_pick_identity",
  "Zeta23.OPICARound4.Validation.native_even_zero_residue_classification",
  "Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer",
  "Zeta23.OPICARound4.Validation.native_odd_invisible_eigen_shared",
  "Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer",
  "Zeta23.OPICARound4.Validation.native_odd_upper_pick_identity",
  "Zeta23.OPICARound4.Validation.native_odd_zero_residue_classification",
  "Zeta23.OPICARound4.Validation.node_jets_suffice_consumer",
  "Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumA",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumB",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumCoordinateCoefficient",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumD",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumDinv",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumP\u2081",
  "Zeta23.OPICARound4.Validation.repeatedSpectrumP\u2082",
  "Zeta23.OPICARound4.Validation.repeated_spectrum_coordinate_projectors",
  "Zeta23.OPICARound4.Validation.repeated_spectrum_hermitian_controls",
  "Zeta23.OPICARound4.Validation.repeated_spectrum_nonreal_coordinates",
  "Zeta23.OPICARound4.Validation.repeated_spectrum_rank_one",
  "Zeta23.OPICARound4.Validation.repeated_spectrum_transport_inverse",
  "Zeta23.OPICARound4.actual_even_ray_adaptive_membership",
  "Zeta23.OPICARound4.actual_even_ray_gap_norm",
  "Zeta23.OPICARound4.actual_even_ray_priced_membership",
  "Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership",
  "Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm",
  "Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership",
  "Zeta23.OPICARound4.actual_odd_resolvent_gap_norm",
  "Zeta23.OPICARound4.actual_odd_resolvent_priced_membership",
  "Zeta23.OPICARound4.blind_vector_in_every_finite_gram_kernel",
  "Zeta23.OPICARound4.complexSignedSpectralResponse",
  "Zeta23.OPICARound4.correctedSourceTestDerivative",
  "Zeta23.OPICARound4.correctedSourceTestDerivative_continuous",
  "Zeta23.OPICARound4.diagonal_safe_source_regression",
  "Zeta23.OPICARound4.eigenmode_invisible_at_all_powers",
  "Zeta23.OPICARound4.even_negative_ground_restriction_of_all_ray",
  "Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds",
  "Zeta23.OPICARound4.eventual_ground_closure_of_three_thresholds",
  "Zeta23.OPICARound4.eventual_noBothNeg_of_actual_ray_closure",
  "Zeta23.OPICARound4.eventual_noBothNeg_of_ground_closure",
  "Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt",
  "Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets",
  "Zeta23.OPICARound4.finiteInputReachableSubspace",
  "Zeta23.OPICARound4.finiteObservationGram",
  "Zeta23.OPICARound4.finiteObservationGram_energy",
  "Zeta23.OPICARound4.finiteObservationGram_kernel_iff",
  "Zeta23.OPICARound4.finiteObservationGram_nonnegative",
  "Zeta23.OPICARound4.finite_grouped_residue_star",
  "Zeta23.OPICARound4.finite_signed_pick_gram",
  "Zeta23.OPICARound4.finite_signed_pick_gram_re",
  "Zeta23.OPICARound4.finite_signed_pick_identity",
  "Zeta23.OPICARound4.finite_signed_pick_negative_subspace_bound",
  "Zeta23.OPICARound4.finite_signed_pick_negative_subspace_exact",
  "Zeta23.OPICARound4.fixedSeedFrame",
  "Zeta23.OPICARound4.fixedSeedFrameDerivative",
  "Zeta23.OPICARound4.fixedSeedFrame_hasDerivAt",
  "Zeta23.OPICARound4.frameEnergyDerivative",
  "Zeta23.OPICARound4.frameEnergyEntry",
  "Zeta23.OPICARound4.frameEnergyEntry_hasDerivAt",
  "Zeta23.OPICARound4.frameGramDerivative",
  "Zeta23.OPICARound4.frameGramEntry",
  "Zeta23.OPICARound4.frameGramEntry_hasDerivAt",
  "Zeta23.OPICARound4.frame_contradicts_native_joint_index",
  "Zeta23.OPICARound4.frame_strictly_negative_native_plane",
  "Zeta23.OPICARound4.groupedEigenvalue",
  "Zeta23.OPICARound4.groupedEigenvalue_cast",
  "Zeta23.OPICARound4.groupedEigenvalue_injective",
  "Zeta23.OPICARound4.groupedShiftedEquiv",
  "Zeta23.OPICARound4.groupedSignedResidue",
  "Zeta23.OPICARound4.groupedSignedResidue_cast",
  "Zeta23.OPICARound4.groupedSpectralCoefficient",
  "Zeta23.OPICARound4.groupedSpectralCoefficient_star",
  "Zeta23.OPICARound4.groupedSpectralProjector",
  "Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization",
  "Zeta23.OPICARound4.groupedSpectralProjector_eq_starProjection",
  "Zeta23.OPICARound4.grouped_input_invisible_coefficient_zero",
  "Zeta23.OPICARound4.grouped_invisible_residue_zero",
  "Zeta23.OPICARound4.grouped_output_invisible_coefficient_zero",
  "Zeta23.OPICARound4.grouped_real_response",
  "Zeta23.OPICARound4.grouped_residue_zero_iff_input_or_output_invisible",
  "Zeta23.OPICARound4.grouped_residue_zero_iff_pairing_zero",
  "Zeta23.OPICARound4.grouped_resolvent_expansion",
  "Zeta23.OPICARound4.grouped_shift_away_of_equiv",
  "Zeta23.OPICARound4.grouped_shift_injective",
  "Zeta23.OPICARound4.grouped_signed_resolvent_expansion",
  "Zeta23.OPICARound4.grouped_zero_coefficient_rigidity",
  "Zeta23.OPICARound4.hermitian_det_star",
  "Zeta23.OPICARound4.integerNodePerturb",
  "Zeta23.OPICARound4.integerNodePerturb_deriv",
  "Zeta23.OPICARound4.integerNodePerturb_hasDerivAt",
  "Zeta23.OPICARound4.integerNodePerturb_value",
  "Zeta23.OPICARound4.integer_node_values_same_matrix_ne",
  "Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul",
  "Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt",
  "Zeta23.OPICARound4.nativeAdaptiveTestClass",
  "Zeta23.OPICARound4.nativeArchContinuumRow",
  "Zeta23.OPICARound4.nativeCompleteRowBudget",
  "Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg",
  "Zeta23.OPICARound4.nativeCorrectedVariation",
  "Zeta23.OPICARound4.nativeCorrectedVariation_nonneg",
  "Zeta23.OPICARound4.nativeEvenGroupedEigenvalue",
  "Zeta23.OPICARound4.nativeEvenGroupedProjector",
  "Zeta23.OPICARound4.nativeEvenGroupedResidue",
  "Zeta23.OPICARound4.nativeEvenObservation",
  "Zeta23.OPICARound4.nativeLatePrimePowers",
  "Zeta23.OPICARound4.nativeOddGroupedEigenvalue",
  "Zeta23.OPICARound4.nativeOddGroupedProjector",
  "Zeta23.OPICARound4.nativeOddGroupedResidue",
  "Zeta23.OPICARound4.nativeOddObservation",
  "Zeta23.OPICARound4.nativeOddReciprocalInput",
  "Zeta23.OPICARound4.nativeOldPrimePowers",
  "Zeta23.OPICARound4.nativePrimeConcentrationBudget",
  "Zeta23.OPICARound4.nativePrimeMass",
  "Zeta23.OPICARound4.nativeSinePotential",
  "Zeta23.OPICARound4.nativeSinePotential_deriv",
  "Zeta23.OPICARound4.nativeSinePotential_hasDerivAt",
  "Zeta23.OPICARound4.nativeSourceAtom",
  "Zeta23.OPICARound4.nativeSourceAtom_apply_norm",
  "Zeta23.OPICARound4.nativeSourceAtom_norm_le_two",
  "Zeta23.OPICARound4.nativeSourceAtom_symmetric",
  "Zeta23.OPICARound4.native_adaptive_complete_budget",
  "Zeta23.OPICARound4.native_complete_concentration_budget",
  "Zeta23.OPICARound4.native_complete_row_budget",
  "Zeta23.OPICARound4.native_corrected_riesz_budget",
  "Zeta23.OPICARound4.native_corrected_source_concentration_real_interval",
  "Zeta23.OPICARound4.native_even_complete_signed_budget",
  "Zeta23.OPICARound4.native_even_grouped_residue_cast",
  "Zeta23.OPICARound4.native_even_grouped_resolvent_expansion",
  "Zeta23.OPICARound4.native_even_invisible_gram",
  "Zeta23.OPICARound4.native_even_visible_or_shared_mode",
  "Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt",
  "Zeta23.OPICARound4.native_frame_negative_physical_plane",
  "Zeta23.OPICARound4.native_inverse_adjoint_cost",
  "Zeta23.OPICARound4.native_inverse_gap_norm",
  "Zeta23.OPICARound4.native_late_mixed_concentration_cost",
  "Zeta23.OPICARound4.native_late_prime_concentration",
  "Zeta23.OPICARound4.native_observation_bound_excludes_invisible_even",
  "Zeta23.OPICARound4.native_odd_adaptive_response_budget",
  "Zeta23.OPICARound4.native_odd_complete_signed_budget",
  "Zeta23.OPICARound4.native_odd_concentration_real_interval",
  "Zeta23.OPICARound4.native_odd_grouped_residue_cast",
  "Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion",
  "Zeta23.OPICARound4.native_odd_invisible_gram",
  "Zeta23.OPICARound4.native_odd_rank_one_unshifted",
  "Zeta23.OPICARound4.native_odd_response_complete_arithmetic",
  "Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source",
  "Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget",
  "Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor",
  "Zeta23.OPICARound4.native_odd_visible_or_shared_mode",
  "Zeta23.OPICARound4.native_old_mixed_concentration_cost",
  "Zeta23.OPICARound4.native_old_prime_concentration",
  "Zeta23.OPICARound4.native_prime_concentration_budget",
  "Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback",
  "Zeta23.OPICARound4.native_prime_discrepancy_integral",
  "Zeta23.OPICARound4.native_prime_half_coordinate_iff",
  "Zeta23.OPICARound4.native_prime_power_regime_partition",
  "Zeta23.OPICARound4.native_prime_row_budget",
  "Zeta23.OPICARound4.native_real_shift_inverse_symmetric",
  "Zeta23.OPICARound4.native_sine_nodeJet_eq_sourceEntryReal",
  "Zeta23.OPICARound4.native_source_energy_eq_exchange_difference",
  "Zeta23.OPICARound4.native_source_mixed_concentration_bound",
  "Zeta23.OPICARound4.native_source_mixed_norm",
  "Zeta23.OPICARound4.native_source_selected_membership",
  "Zeta23.OPICARound4.native_source_square_concentration_full",
  "Zeta23.OPICARound4.native_source_square_concentration_half",
  "Zeta23.OPICARound4.negativeAtomEmbedding",
  "Zeta23.OPICARound4.negativeAtomEmbedding_injective",
  "Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt",
  "Zeta23.OPICARound4.noBothNeg_of_actual_ground_comparisons",
  "Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons",
  "Zeta23.OPICARound4.noBothNeg_of_ground_restrictions",
  "Zeta23.OPICARound4.noBothNeg_of_research_targets",
  "Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure",
  "Zeta23.OPICARound4.no_off_line_zero_of_eventual_ground_closure",
  "Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index",
  "Zeta23.OPICARound4.no_off_line_zero_of_eventual_noBothNeg",
  "Zeta23.OPICARound4.nodeJetMatrix",
  "Zeta23.OPICARound4.nodeJetMatrix_diagonal",
  "Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets",
  "Zeta23.OPICARound4.observationBlindSubspace",
  "Zeta23.OPICARound4.observationBlindSubspace_invariant",
  "Zeta23.OPICARound4.observationBlindSubspace_mem",
  "Zeta23.OPICARound4.odd_negative_ground_restriction_of_all_ray",
  "Zeta23.OPICARound4.primeSourceCoordinate_mem_unit",
  "Zeta23.OPICARound4.prime_discrepancy_log_integral",
  "Zeta23.OPICARound4.prime_log_abel",
  "Zeta23.OPICARound4.prime_log_mem_interval",
  "Zeta23.OPICARound4.psi_eq_sum_Icc_two",
  "Zeta23.OPICARound4.psi_exp_eq_sum_steps",
  "Zeta23.OPICARound4.rank_one_kernel_pairing_rigidity",
  "Zeta23.OPICARound4.rank_one_visible_or_shared_mode",
  "Zeta23.OPICARound4.reachable_subspace_in_output_kernel",
  "Zeta23.OPICARound4.real_sub_upper_ne_zero",
  "Zeta23.OPICARound4.signedCauchyEvaluation",
  "Zeta23.OPICARound4.signedCauchyLinearMap",
  "Zeta23.OPICARound4.signedPickKernel",
  "Zeta23.OPICARound4.sourceConcentration",
  "Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus",
  "Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half",
  "Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq",
  "Zeta23.OPICARound4.sourceConcentration_nonneg",
  "Zeta23.OPICARound4.sourceExchangeMinus",
  "Zeta23.OPICARound4.sourceExchangeMixed",
  "Zeta23.OPICARound4.sourceExchangeMixed_eq_native",
  "Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le",
  "Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native",
  "Zeta23.OPICARound4.sourceExchangePlus",
  "Zeta23.OPICARound4.sourceExchange_nonneg",
  "Zeta23.OPICARound4.sourceFiniteFourier",
  "Zeta23.OPICARound4.sourceFiniteFourier_continuous",
  "Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp",
  "Zeta23.OPICARound4.sum_groupedSpectralProjector",
  "Zeta23.OPICARound4.upper_sub_conj_ne_zero",
  "Zeta23.OPICARound4.zero_residue_does_not_remove_eigenspace"
]
INTEGRATION_MODULES = BASELINE_MODULES + [
  "Zeta23.OPICARound4.AdaptiveBudget",
  "Zeta23.OPICARound4.ClosureConsumers",
  "Zeta23.OPICARound4.IntegrationTargets",
  "Zeta23.OPICARound4.NativeConcentrationBudget",
  "Zeta23.OPICARound4.NativeJointIndex",
  "Zeta23.OPICARound4.NativeObservation",
  "Zeta23.OPICARound4.NativeSourceBudget",
  "Zeta23.OPICARound4.NativeSpectralMeasure",
  "Zeta23.OPICARound4.NativeVisibility",
  "Zeta23.OPICARound4.NeutralContactPencil",
  "Zeta23.OPICARound4.OddReciprocalSource",
  "Zeta23.OPICARound4.PrimeDiscrepancyIntegral",
  "Zeta23.OPICARound4.RegularCells.FixedSeed",
  "Zeta23.OPICARound4.SearchSupport",
  "Zeta23.OPICARound4.SignedPickKernel",
  "Zeta23.OPICARound4.SourceDictionaryCrosswalk",
  "Zeta23.OPICARound4.SourceExchangeConcentration",
  "Zeta23.OPICARound4.Validation.IntegrationClosure",
  "Zeta23.OPICARound4.Validation.IntegrationDictionary",
  "Zeta23.OPICARound4.Validation.IntegrationObservation",
  "Zeta23.OPICARound4.Validation.IntegrationSource",
  "Zeta23.OPICARound4.Validation.IntegrationSpectral",
  "Zeta23.OPICARound4.Validation.IntegrationVisibilityRigidity",
  "Zeta23.OPICARound4.VisibilityRigidity"
]
INTEGRATION_DECLARATION_COUNT = 397
INTEGRATION_MODULE_COUNT = 40
# SOURCE_CONSTRAINT_INVENTORY_BEGIN
SOURCE_CONSTRAINT_DECLARATIONS = [
  "Zeta23.OPICARound4.nativeSignedPrimeDiscrepancy",
  "Zeta23.OPICARound4.nativeGroundArchPairing",
  "Zeta23.OPICARound4.nativeGroundPrimePairing",
  "Zeta23.OPICARound4.native_signed_source_decomposition",
  "Zeta23.OPICARound4.native_signed_discrepancy_integral",
  "Zeta23.OPICARound4.actual_even_ground_ray_facts",
  "Zeta23.OPICARound4.actual_odd_ground_ray_facts",
  "Zeta23.OPICARound4.actual_even_ground_signed_discrepancy",
  "Zeta23.OPICARound4.actual_odd_ground_reciprocal_discrepancy",
  "Zeta23.OPICARound4.actual_even_ground_signed_budget_feasibility",
  "Zeta23.OPICARound4.actual_odd_ground_signed_budget_feasibility",
  "Zeta23.OPICARound4.actual_even_ground_ray_moment_feasibility",
  "Zeta23.OPICARound4.native_even_eigen_absolute_energy",
  "Zeta23.OPICARound4.native_odd_eigen_absolute_energy",
  "Zeta23.OPICARound4.NativeStrictEvenGroundConstraints",
  "Zeta23.OPICARound4.NativeStrictEvenGroundConstraints.mk",
  "Zeta23.OPICARound4.NativeStrictOddGroundConstraints",
  "Zeta23.OPICARound4.NativeStrictOddGroundConstraints.mk",
  "Zeta23.OPICARound4.NativeTiedGroundConstraints",
  "Zeta23.OPICARound4.NativeTiedGroundConstraints.mk",
  "Zeta23.OPICARound4.NativeJointGroundConstraints",
  "Zeta23.OPICARound4.native_tied_ground_constraints",
  "Zeta23.OPICARound4.joint_ground_constraints_of_both_negative",
  "Zeta23.OPICARound4.cofinally_joint_ground_constraints_of_off_line_zero",
  "Zeta23.OPICARound4.sourceImageErrorBudget",
  "Zeta23.OPICARound4.sourceFiniteModeCost",
  "Zeta23.OPICARound4.sourceForcingErrorBudget",
  "Zeta23.OPICARound4.sourceWeilBoundConstant",
  "Zeta23.OPICARound4.sourceWeilBoundConstant_pos",
  "Zeta23.OPICARound4.finiteForcingBudget",
  "Zeta23.OPICARound4.sourceImageErrorBudget_nonneg",
  "Zeta23.OPICARound4.source_eta_nonneg",
  "Zeta23.OPICARound4.sourceForcingErrorBudget_nonneg",
  "Zeta23.OPICARound4.finiteForcingBudget_nonneg",
  "Zeta23.OPICARound4.smoothSourceL2",
  "Zeta23.OPICARound4.smoothSourceL2_ae",
  "Zeta23.OPICARound4.smoothSourceResponseL2",
  "Zeta23.OPICARound4.smoothSourceResponseL2_ae",
  "Zeta23.OPICARound4.smoothSourceForcing",
  "Zeta23.OPICARound4.smoothSourceForcing_pairing",
  "Zeta23.OPICARound4.smoothSourceForcing_error_pairing",
  "Zeta23.OPICARound4.smoothSourceForcing_channels",
  "Zeta23.OPICARound4.norm_le_of_all_inner_bound",
  "Zeta23.OPICARound4.smoothSourceForcing_error_bound",
  "Zeta23.OPICARound4.finiteForcing_norm_bound",
  "Zeta23.OPICARound4.smoothSourceForcing_norm_bound",
  "Zeta23.OPICARound4.sourcePhysicalL2_norm_eq",
  "Zeta23.OPICARound4.smoothSourceL2_error_bound",
  "Zeta23.OPICARound4.smoothSourceL2_norm_bound",
  "Zeta23.OPICARound4.detectorInverse",
  "Zeta23.OPICARound4.sourceInverseBudget",
  "Zeta23.OPICARound4.detectorSchurLoss",
  "Zeta23.OPICARound4.finiteSourceEnergy",
  "Zeta23.OPICARound4.smoothSourceMain",
  "Zeta23.OPICARound4.sourceEnergyErrorBudget",
  "Zeta23.OPICARound4.sourceSchurErrorBudget",
  "Zeta23.OPICARound4.detectorInverse_norm_bound",
  "Zeta23.OPICARound4.sourceInverseBudget_nonneg",
  "Zeta23.OPICARound4.detectorSchurLoss_lower",
  "Zeta23.OPICARound4.detectorSchurLoss_eq_forcing_energy",
  "Zeta23.OPICARound4.sourceQuadratic_perturbation_bound",
  "Zeta23.OPICARound4.smoothSourceL2_mass_error_bound",
  "Zeta23.OPICARound4.detectorSchurLoss_sub_smoothSourceMain_bound",
  "Zeta23.OPICARound4.detectorForcing_zero_at_first",
  "Zeta23.OPICARound4.detectorSchurLoss_at_first",
  "Zeta23.OPICARound4.quartic_polynomial_exp_tendsto_zero",
  "Zeta23.OPICARound4.quarticImageError",
  "Zeta23.OPICARound4.quarticImageError_nonneg",
  "Zeta23.OPICARound4.quarticImageError_mul_exp_tendsto_zero",
  "Zeta23.OPICARound4.pow_mul_exp_mul_quarticImageError_tendsto_zero",
  "Zeta23.OPICARound4.quarticCutoff_le_two_pow_four",
  "Zeta23.OPICARound4.quartic_mode_cost_le",
  "Zeta23.OPICARound4.quarticErrorEnvelope",
  "Zeta23.OPICARound4.quarticErrorEnvelope_nonneg",
  "Zeta23.OPICARound4.quarticErrorEnvelope_mul_exp_tendsto_zero",
  "Zeta23.OPICARound4.quarticErrorEnvelope_eventually_lt_exp",
  "Zeta23.OPICARound4.sourceEtaGrowthConstant",
  "Zeta23.OPICARound4.sourceEtaGrowthConstant_pos",
  "Zeta23.OPICARound4.source_eta_polynomial_bound",
  "Zeta23.OPICARound4.detector_inverse_polynomial_bound",
  "Zeta23.OPICARound4.sourceForcingGrowthConstant",
  "Zeta23.OPICARound4.sourceForcingErrorGrowthConstant",
  "Zeta23.OPICARound4.sourceForcingGrowthConstant_pos",
  "Zeta23.OPICARound4.sourceForcingErrorGrowthConstant_pos",
  "Zeta23.OPICARound4.finiteForcingBudget_polynomial_bound",
  "Zeta23.OPICARound4.sourceForcingErrorBudget_polynomial_bound",
  "Zeta23.OPICARound4.sourceSchurUniformEnvelope",
  "Zeta23.OPICARound4.sourceSchurErrorBudget_le_uniformEnvelope",
  "Zeta23.OPICARound4.sourceSchurUniformEnvelope_mul_exp_tendsto_zero",
  "Zeta23.OPICARound4.exists_uniform_source_schur_error_threshold",
  "Zeta23.OPICARound4.exists_uniform_smooth_source_main_lower_threshold",
  "Zeta23.OPICARound4.exists_generated_smooth_source_main_lower_threshold",
  "Zeta23.OPICARound4.validation_smooth_source_forcing",
  "Zeta23.OPICARound4.validation_detector_schur_error",
  "Zeta23.OPICARound4.validation_detector_first_cutoff",
  "Zeta23.OPICARound4.Validation.quartic_rate_consumer",
  "Zeta23.OPICARound4.Validation.source_shift_consumer",
  "Zeta23.OPICARound4.Validation.same_detector_inverse_consumer",
  "Zeta23.OPICARound4.Validation.complete_error_envelope_consumer",
  "Zeta23.OPICARound4.Validation.all_exponential_rates_consumer",
  "Zeta23.OPICARound4.Validation.threshold_before_packet_consumer",
  "Zeta23.OPICARound4.Validation.native_packet_lower_consumer",
  "Zeta23.OPICARound4.Validation.generated_packet_lower_consumer"
]
SOURCE_CONSTRAINT_MODULES = [
  "Zeta23.OPICARound4.GroundArithmetic",
  "Zeta23.OPICARound4.JointGroundConstraints",
  "Zeta23.OPICARound4.SmoothForcing",
  "Zeta23.OPICARound4.SchurErrorTransport",
  "Zeta23.OPICARound4.QuarticErrorReduction",
  "Zeta23.OPICARound4.Validation.GroundConstraints",
  "Zeta23.OPICARound4.Validation.DetectorErrors",
  "Zeta23.OPICARound4.Validation.ErrorReduction"
]
PRE_MADNESS_DECLARATIONS = INTEGRATION_EXPECTED_DECLARATIONS + SOURCE_CONSTRAINT_DECLARATIONS
PRE_MADNESS_MODULES = INTEGRATION_MODULES + SOURCE_CONSTRAINT_MODULES
PRE_MADNESS_DECLARATION_COUNT = 500
PRE_MADNESS_MODULE_COUNT = 48
# MADNESS_INVENTORY_BEGIN
MADNESS_DECLARATIONS = [
  "Zeta23.OPICARound4.mobiusR",
  "Zeta23.OPICARound4.arithmetic_sub_apply",
  "Zeta23.OPICARound4.weighted_convolution",
  "Zeta23.OPICARound4.weighted_mobius_inverse",
  "Zeta23.OPICARound4.arithmeticTruncation",
  "Zeta23.OPICARound4.arithmeticTruncation_apply",
  "Zeta23.OPICARound4.arithmeticTruncation_sum",
  "Zeta23.OPICARound4.tail_square_vanishes",
  "Zeta23.OPICARound4.tail_square_convolution_vanishes",
  "Zeta23.OPICARound4.mobius_hyperbola_coefficient",
  "Zeta23.OPICARound4.weighted_triple_convolution",
  "Zeta23.OPICARound4.hyperbolaU",
  "Zeta23.OPICARound4.hyperbolaE",
  "Zeta23.OPICARound4.hyperbolaT",
  "Zeta23.OPICARound4.truncated_convolution_is_hyperbolaT",
  "Zeta23.OPICARound4.finite_mobius_hyperbola",
  "Zeta23.OPICARound4.finiteLogarithmicTest",
  "Zeta23.OPICARound4.finiteLogarithmicTest_support",
  "Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU",
  "Zeta23.OPICARound4.finite_vonMangoldt_hyperbola",
  "Zeta23.OPICARound4.hyperbolaT_one",
  "Zeta23.OPICARound4.hyperbolaT_negative_test",
  "Zeta23.OPICARound4.finiteLogarithmicTest_half_support",
  "Zeta23.OPICARound4.hyperbolaU_shrink",
  "Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half",
  "Zeta23.OPICARound4.actualCorrelationKernel",
  "Zeta23.OPICARound4.actualCorrelationSource",
  "Zeta23.OPICARound4.actualCorrelationCutoff",
  "Zeta23.OPICARound4.actualCorrelationWeight",
  "Zeta23.OPICARound4.actualCorrelationPrimeField",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_eq_sourceConvolution",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_bound_of_native_bound",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_rapid_bound",
  "Zeta23.OPICARound4.actualCorrelationKernel_supported",
  "Zeta23.OPICARound4.actualCorrelationCutoff_exact",
  "Zeta23.OPICARound4.actualCorrelationWeight_zero_above",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_eq_weighted_vonMangoldt",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_eq_nativeSourceConvolution",
  "Zeta23.OPICARound4.actualCorrelationLogarithmicTest",
  "Zeta23.OPICARound4.actualCorrelationLogarithmicTest_eq_integerDrive",
  "Zeta23.OPICARound4.actualFlatMobiusTest",
  "Zeta23.OPICARound4.actualFlatMobiusTest_normalization",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_eq_mobius",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola",
  "Zeta23.OPICARound4.actualCorrelationLogarithmicTest_half_support",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half",
  "Zeta23.OPICARound4.actualNativeSourceConvolution_hyperbola_half",
  "Zeta23.OPICARound4.actualCorrelationShortTerm_rapid_bound",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound",
  "Zeta23.OPICARound4.higherPrimePowerCoefficient",
  "Zeta23.OPICARound4.higherPrimePowerCoefficient_nonneg",
  "Zeta23.OPICARound4.higherPrimePowerCoefficient_sum",
  "Zeta23.OPICARound4.actualCorrelationKernel_continuous",
  "Zeta23.OPICARound4.actualCorrelationSource_bounded",
  "Zeta23.OPICARound4.actualCorrelationWeight_uniform_bound",
  "Zeta23.OPICARound4.actualCorrelationHigherPrimePowers",
  "Zeta23.OPICARound4.actualCorrelationHigherPrimePowers_uniform_bound",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_split_prime_powers",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_hasDerivAt",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_deriv_rapid_bound",
  "Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt",
  "Zeta23.OPICARound4.actualFlatMobiusTest_zero_of_nonpos",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_contDiff_one",
  "Zeta23.OPICARound4.actualFlatMobiusTest_origin_bounds",
  "Zeta23.OPICARound4.actualFlatMobiusTest_hasDerivAt_zero",
  "Zeta23.OPICARound4.actualFlatMobiusTest_contDiff_one",
  "Zeta23.OPICARound4.actualFlatMobiusTest_zero_above",
  "Zeta23.OPICARound4.actualFlatMobiusTest_at_upper_collar",
  "Zeta23.OPICARound4.actualFlatMobiusTest_hasCompactSupport",
  "Zeta23.OPICARound4.actualFlatSamplingMass",
  "Zeta23.OPICARound4.actualFlatSamplingSum",
  "Zeta23.OPICARound4.actualFlatSamplingRemainder",
  "Zeta23.OPICARound4.actualFlatSamplingRemainder_bounded",
  "Zeta23.OPICARound4.actualFlatSamplingSum_eq_mass_add_remainder",
  "Zeta23.OPICARound4.actualFlatSamplingDiagonal_sqrt_bound",
  "Zeta23.OPICARound4.actualFlatSamplingSum_eq_tsum",
  "Zeta23.OPICARound4.actualFlatSampling_eventual_lower_iff",
  "Zeta23.OPICARound4.actualFlatSamplingSum_eq_hyperbola_history",
  "Zeta23.OPICARound4.actualCorrelationLongTerm_eq_sampling_quadratic",
  "Zeta23.OPICARound4.actualCorrelationNativeCutoff_sqrt_bound",
  "Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound",
  "Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined",
  "Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined",
  "Zeta23.OPICARound4.nativeOriginalIntegerDriveLaplace_half",
  "Zeta23.OPICARound4.actualSourceHalfMass",
  "Zeta23.OPICARound4.actualSourceHalfMass_integrable",
  "Zeta23.OPICARound4.actualSourceHalfMass_eq_product",
  "Zeta23.OPICARound4.actualSourceHalfMass_pos",
  "Zeta23.OPICARound4.nativeOriginalIntegerDrive_half_integral",
  "Zeta23.OPICARound4.actualFlatSamplingMass_eq_dampedDrive",
  "Zeta23.OPICARound4.actualCorrelationIntegerDrive_half_integral",
  "Zeta23.OPICARound4.actualFlatSamplingMass_eq_sourceHalfMass_sq",
  "Zeta23.OPICARound4.actualFlatSamplingMass_pos",
  "Zeta23.OPICARound4.actualCorrelationKernel_weilTest_translate",
  "Zeta23.OPICARound4.actualCorrelationArch",
  "Zeta23.OPICARound4.actualCorrelation_explicit_formula",
  "Zeta23.OPICARound4.actualCorrelationArch_uniform_bound",
  "Zeta23.OPICARound4.actualCorrelationPrimeField_reflected_zero",
  "Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower",
  "Zeta23.OPICARound4.aliasDiagonal",
  "Zeta23.OPICARound4.abs_aliasDiagonal_le_count",
  "Zeta23.OPICARound4.abs_aliasDiagonal_le_sqrt",
  "Zeta23.OPICARound4.lower_bound_remove_bounded_diagonal",
  "Zeta23.OPICARound4.lower_bound_restore_bounded_diagonal",
  "Zeta23.OPICARound4.mobiusPoissonRemainder",
  "Zeta23.OPICARound4.mobiusPoissonOffDiagonal",
  "Zeta23.OPICARound4.mobiusReciprocalSum",
  "Zeta23.OPICARound4.mobiusPoissonRankOne",
  "Zeta23.OPICARound4.mobiusPoissonQuadratic",
  "Zeta23.OPICARound4.mobiusPoissonRemainder_eq_diagonal_add_offDiagonal",
  "Zeta23.OPICARound4.mobiusPoissonRankOne_nonneg",
  "Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_add_remainder",
  "Zeta23.OPICARound4.mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal",
  "Zeta23.OPICARound4.HasEventualSqrtLower",
  "Zeta23.OPICARound4.eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal",
  "Zeta23.OPICARound4.validation_madness_actual_hyperbola",
  "Zeta23.OPICARound4.validation_madness_actual_drive",
  "Zeta23.OPICARound4.validation_madness_actual_normalization",
  "Zeta23.OPICARound4.validation_madness_drive_rapid_decay",
  "Zeta23.OPICARound4.validation_madness_short_term_rapid_decay",
  "Zeta23.OPICARound4.validation_madness_observable_remainder",
  "Zeta23.OPICARound4.validation_madness_complete_split",
  "Zeta23.OPICARound4.validation_madness_diagonal_budget",
  "Zeta23.OPICARound4.validation_madness_lower_equivalence",
  "Zeta23.OPICARound4.validation_madness_signed_test",
  "Zeta23.OPICARound4.validation_madness_higher_prime_powers_bounded",
  "Zeta23.OPICARound4.validation_madness_prime_power_split",
  "Zeta23.OPICARound4.validation_madness_drive_derivative_rapid",
  "Zeta23.OPICARound4.validation_madness_flat_test_derivative",
  "Zeta23.OPICARound4.validation_madness_flat_test_c1",
  "Zeta23.OPICARound4.validation_madness_flat_test_compact",
  "Zeta23.OPICARound4.validation_madness_actual_remainder_bounded",
  "Zeta23.OPICARound4.validation_madness_actual_diagonal",
  "Zeta23.OPICARound4.validation_madness_all_sampling_terms",
  "Zeta23.OPICARound4.validation_madness_actual_lower_equivalence",
  "Zeta23.OPICARound4.validation_madness_actualCorrelationNativeDiagonal_bound",
  "Zeta23.OPICARound4.validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined",
  "Zeta23.OPICARound4.validation_madness_exact_sampling_bridge",
  "Zeta23.OPICARound4.validation_madness_actual_mass_positive",
  "Zeta23.OPICARound4.validation_madness_actual_rank_one_nonnegative",
  "Zeta23.OPICARound4.validation_madness_actual_weil_translation",
  "Zeta23.OPICARound4.validation_madness_actual_explicit_formula",
  "Zeta23.OPICARound4.validation_madness_actual_arch_bound",
  "Zeta23.OPICARound4.validation_madness_actual_reflected_history",
  "Zeta23.OPICARound4.validation_madness_rh_of_actual_lower",
  "Zeta23.OPICARound4.recenteredSmoothPhase",
  "Zeta23.OPICARound4.recenteredFiniteApprox",
  "Zeta23.OPICARound4.recenteredFiniteHard",
  "Zeta23.OPICARound4.recenteredSmoothPhase_eq_translate",
  "Zeta23.OPICARound4.recenteredSmoothPhase_contDiff",
  "Zeta23.OPICARound4.recenteredSmoothPhase_L1_bound",
  "Zeta23.OPICARound4.recenteredSmoothPhase_zero_outside",
  "Zeta23.OPICARound4.recenteredFiniteHard_contDiff",
  "Zeta23.OPICARound4.recenteredFiniteApprox_jet_error",
  "Zeta23.OPICARound4.recenteredFiniteHard_L1_error",
  "Zeta23.OPICARound4.recenteredFinitePhase_Weil_error",
  "Zeta23.OPICARound4.recenteredFiniteHard_Weil_eq_native",
  "Zeta23.OPICARound4.recenteredSmoothPhase_fixed_energy",
  "Zeta23.OPICARound4.recentered_negative_phase_eventually_quartic",
  "Zeta23.OPICARound4.exists_fixed_negative_original_phase",
  "Zeta23.OPICARound4.eventually_both_negative_at_original_quartic",
  "Zeta23.OPICARound4.cofinally_both_negative_at_original_quartic",
  "Zeta23.OPICARound4.every_late_generated_packet_has_joint_detector_ground",
  "Zeta23.OPICARound4.first_common_cutoff_le_original_quartic",
  "Zeta23.OPICARound4.negative_eigenspace_finrank_le_shell",
  "Zeta23.OPICARound4.nativeNewborn_negative_eigenspace_finrank_le_one",
  "Zeta23.OPICARound4.nativeNewborn_even_ground_simple",
  "Zeta23.OPICARound4.nativeNewborn_even_tied_ground_momentFour_ne_zero",
  "Zeta23.OPICARound4.simple_native_tied_ground_not_both_silent",
  "Zeta23.OPICARound4.oneShell_negative_eigen_complement_nonnegative",
  "Zeta23.OPICARound4.oneShell_negative_eigen_shifted_complement_coercive",
  "Zeta23.OPICARound4.oneShell_negative_eigen_complement_response_norm",
  "Zeta23.OPICARound4.nativeNewborn_negative_eigen_complement_bounds",
  "Zeta23.OPICARound4.native_source_active_moment_pos_of_le_odd_bottom",
  "Zeta23.OPICARound4.native_source_normalized_tied_ground_moment_pos",
  "Zeta23.OPICARound4.simple_even_tie_source_silent_odd_kernel_visible",
  "Zeta23.OPICARound4.simple_even_tie_whole_kernel_exclusive_visibility",
  "Zeta23.OPICARound4.Validation.common_quartic_uniform_threshold_consumer",
  "Zeta23.OPICARound4.Validation.generated_packet_joint_consumer",
  "Zeta23.OPICARound4.Validation.first_common_quartic_bound_consumer",
  "Zeta23.OPICARound4.Validation.native_newborn_complement_consumer",
  "Zeta23.OPICARound4.Validation.source_active_ground_moment_consumer",
  "Zeta23.OPICARound4.Validation.actual_newborn_even_ground_simple_consumer",
  "Zeta23.OPICARound4.Validation.tied_ground_not_both_silent_consumer",
  "Zeta23.OPICARound4.Validation.tied_ground_whole_kernel_visibility_consumer",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_indexComplement_norm_le",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_active_source_moment_bounds",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_normalized_moment_bounds",
  "Zeta23.OPICARound4.nativeNewborn_negative_eigenvalue_eq_ground",
  "Zeta23.OPICARound4.evenNewborn_odd_negative_eigen_channels_visible",
  "Zeta23.OPICARound4.oddNewborn_even_negative_eigen_channels_visible",
  "Zeta23.OPICARound4.evenNewborn_odd_negative_eigenspace_finrank_le_one",
  "Zeta23.OPICARound4.oddNewborn_even_negative_eigenspace_finrank_le_one",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_energy_nonneg",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_active_cubic_channel_nonneg",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility",
  "Zeta23.OPICARound4.actual_normalized_even_moment_cubic_energy_lower",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_silent_moment_depth_lower",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower",
  "Zeta23.OPICARound4.actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple",
  "Zeta23.OPICARound4.exists_log_nonzero_in_open_positive",
  "Zeta23.OPICARound4.exists_finite_log_nonzero_in_open_positive",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedEntry",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_ofReal",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedEntry_one",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_one",
  "Zeta23.OPICARound4.RegularCells.liftedFullSource",
  "Zeta23.OPICARound4.RegularCells.normalizedFrameSource",
  "Zeta23.OPICARound4.RegularCells.normalizedFrameSource_apply",
  "Zeta23.OPICARound4.RegularCells.analyticOnNhd_normalizedFrameSource_apply",
  "Zeta23.OPICARound4.RegularCells.liftedNativeFrame",
  "Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrame_coord",
  "Zeta23.OPICARound4.RegularCells.liftedNativeFrame_deck_base",
  "Zeta23.OPICARound4.RegularCells.liftedNativeFrameDet",
  "Zeta23.OPICARound4.RegularCells.analyticOnNhd_liftedNativeFrameDet",
  "Zeta23.OPICARound4.RegularCells.exists_mem_corridor_liftedNativeFrameDet_ne_zero",
  "Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry",
  "Zeta23.OPICARound4.RegularCells.nativeSeedPhysicalTransport",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_physical_transport",
  "Zeta23.OPICARound4.RegularCells.nativeSeedAmbientIsometry_inner_canonical",
  "Zeta23.OPICARound4.RegularCells.liftedFullSource_log_fixedCell",
  "Zeta23.OPICARound4.RegularCells.normalizedSeedMatrix_real_isSymmetric",
  "Zeta23.OPICARound4.RegularCells.liftedNativeFrame_log_fixedCell",
  "Zeta23.OPICARound4.RegularCells.nativeCanonical_bijective_of_frameDet_ne_zero",
  "Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_fixedCell",
  "Zeta23.OPICARound4.RegularCells.exists_open_fixedCell_subset_positive",
  "Zeta23.OPICARound4.RegularCells.exists_finite_native_regular_in_open_positive",
  "Zeta23.OPICARound4.RegularCells.exists_bounded_native_regular_in_open_positive",
  "Zeta23.OPICARound4.RegularCells.cofinally_both_negative_and_native_regular",
  "Zeta23.OPICARound4.RegularCells.cofinally_regular_first_common_births",
  "Zeta23.OPICARound4.RegularCells.native_newborn_realization_regular_of_bijective",
  "Zeta23.OPICARound4.Validation.tied_newborn_active_response_consumer",
  "Zeta23.OPICARound4.Validation.newborn_opposite_source_channels_consumer",
  "Zeta23.OPICARound4.Validation.normalized_cubic_energy_lower_consumer",
  "Zeta23.OPICARound4.Validation.negative_cubic_energy_ground_simple_consumer",
  "Zeta23.OPICARound4.Validation.native_fixed_cell_regular_selection_consumer",
  "Zeta23.OPICARound4.Validation.cofinal_native_regular_births_consumer",
  "Zeta23.OPICARound4.Validation.same_newborn_regular_realization_consumer",
  "Zeta23.OPICARound4.NativeParitySeparation.diagonal_two_moment_compressions_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.native_squared_index_compressions_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeConstantVector",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeIndexVector",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSquareVector",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeReciprocalVector",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingEvenCarrier",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeLimitingOddCarrier",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexDiagonal",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSquaredIndexCompression",
  "Zeta23.OPICARound4.NativeParitySeparation.native_limiting_compressed_squared_index_no_common_eigenvalue",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_of_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_not_injective_of_common",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_injective_iff_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeSylvester_det_ne_zero_iff_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_common_scalar",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_scale",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_identity_gram",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_factor",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_injective_of_disjoint",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_disjoint_of_injective",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_frame_det_ne_zero_iff_disjoint",
  "Zeta23.OPICARound4.RegularCells.imaginaryReciprocal",
  "Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto",
  "Zeta23.OPICARound4.RegularCells.imaginaryReciprocal_tendsto_punctured",
  "Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_isBigO_pow",
  "Zeta23.OPICARound4.RegularCells.meromorphic_imaginaryReciprocal_div_exp_tendsto_zero",
  "Zeta23.OPICARound4.RegularCells.frequencyRayTerm",
  "Zeta23.OPICARound4.RegularCells.frequencyRayTerm_div",
  "Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_max_nonzero",
  "Zeta23.OPICARound4.RegularCells.meromorphic_frequency_ray_nonzero",
  "Zeta23.OPICARound4.RegularCells.exp_frequency_imaginaryReciprocal",
  "Zeta23.OPICARound4.RegularCells.meromorphic_frequency_germ_nonzero",
  "Zeta23.OPICARound4.RegularCells.primeLogFrequency",
  "Zeta23.OPICARound4.RegularCells.finite_prime_product_factorization",
  "Zeta23.OPICARound4.RegularCells.natural_prime_log_sum_injective",
  "Zeta23.OPICARound4.RegularCells.primeLogFrequency_injective",
  "Zeta23.OPICARound4.RegularCells.primeLaurentFrequency",
  "Zeta23.OPICARound4.RegularCells.primeLaurentFrequency_injective",
  "Zeta23.OPICARound4.RegularCells.primePhase",
  "Zeta23.OPICARound4.RegularCells.primeLaurentMonomial",
  "Zeta23.OPICARound4.RegularCells.primeLaurentMonomial_eq_exp",
  "Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient",
  "Zeta23.OPICARound4.RegularCells.primeLaurent_sum_grouped",
  "Zeta23.OPICARound4.RegularCells.groupedPrimeLaurentCoefficient_meromorphic",
  "Zeta23.OPICARound4.RegularCells.primeLaurent_sum_germ_nonzero",
  "Zeta23.OPICARound4.RegularCells.primeLogFrequency_factorization",
  "Zeta23.OPICARound4.RegularCells.primePhase_eq_factorization_monomial",
  "Zeta23.OPICARound4.RegularCells.formalPrimeMonomial",
  "Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_zero",
  "Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_add",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.congr",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.constant",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.monomial",
  "Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_single",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.coordinate_zpow",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.add",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.neg",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sub",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.mul",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.sum",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.prod",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.det",
  "Zeta23.OPICARound4.RegularCells.primePhaseUnits",
  "Zeta23.OPICARound4.RegularCells.formalPrimeMonomial_actual",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.exists_nonzero_coefficient",
  "Zeta23.OPICARound4.RegularCells.HasPrimeLaurentExpansion.actual_germ_nonzero",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_ne_zero",
  "Zeta23.OPICARound4.PrimeSourceLaurent.exp_source_angle",
  "Zeta23.OPICARound4.PrimeSourceLaurent.exp_neg_source_angle",
  "Zeta23.OPICARound4.PrimeSourceLaurent.potential_laurent",
  "Zeta23.OPICARound4.PrimeSourceLaurent.diagonal_laurent",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_one",
  "Zeta23.OPICARound4.PrimeSourceLaurent.frozenPrimeMatrix_laurent",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_eq",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_zero",
  "Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.tendsto_scaledPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.meromorphicAt_formalPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.primeCommonScalar",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalFrozenPrimeMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledFrozenPrimeMatrix_eq",
  "Zeta23.OPICARound4.PrimeSourceLaurent.analyticAt_scaledFrozenPrimeMatrix",
  "Zeta23.OPICARound4.NativeZeroFrame.center",
  "Zeta23.OPICARound4.NativeZeroFrame.pos",
  "Zeta23.OPICARound4.NativeZeroFrame.neg",
  "Zeta23.OPICARound4.NativeZeroFrame.centered_center",
  "Zeta23.OPICARound4.NativeZeroFrame.centered_pos",
  "Zeta23.OPICARound4.NativeZeroFrame.centered_neg",
  "Zeta23.OPICARound4.NativeZeroFrame.foldIndex",
  "Zeta23.OPICARound4.NativeZeroFrame.foldIndex_bijective",
  "Zeta23.OPICARound4.NativeZeroFrame.foldEquiv",
  "Zeta23.OPICARound4.NativeZeroFrame.sum_fold",
  "Zeta23.OPICARound4.NativeZeroFrame.rev_pos",
  "Zeta23.OPICARound4.NativeZeroFrame.rev_center",
  "Zeta23.OPICARound4.NativeZeroFrame.rev_neg",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift_center",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift_pos",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift_neg",
  "Zeta23.OPICARound4.NativeZeroFrame.fold_ext",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift_even",
  "Zeta23.OPICARound4.NativeZeroFrame.foldLift_odd",
  "Zeta23.OPICARound4.NativeZeroFrame.moment_foldLift",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift",
  "Zeta23.OPICARound4.NativeZeroFrame.rawOddLift",
  "Zeta23.OPICARound4.NativeZeroFrame.index_ne_zero",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawEvenLift",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_rawOddLift",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_zero",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_two",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_moment_four",
  "Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_one",
  "Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_moment_three",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_mem_iff",
  "Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_mem_iff",
  "Zeta23.OPICARound4.NativeZeroFrame.even_eq_fold",
  "Zeta23.OPICARound4.NativeZeroFrame.odd_eq_fold",
  "Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates",
  "Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawEvenLift",
  "Zeta23.OPICARound4.NativeZeroFrame.positiveCoordinates_rawOddLift",
  "Zeta23.OPICARound4.NativeZeroFrame.rawEvenLift_positiveCoordinates",
  "Zeta23.OPICARound4.NativeZeroFrame.rawOddLift_positiveCoordinates",
  "Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingEvenCarrier_iff",
  "Zeta23.OPICARound4.NativeZeroFrame.mem_nativeLimitingOddCarrier_iff",
  "Zeta23.OPICARound4.NativeZeroFrame.evenZeroEquiv",
  "Zeta23.OPICARound4.NativeZeroFrame.oddZeroEquiv",
  "Zeta23.OPICARound4.NativeZeroFrame.inner_even_fold",
  "Zeta23.OPICARound4.NativeZeroFrame.inner_odd_fold",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_even_seed",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_diagonal_odd_seed",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_even_gram",
  "Zeta23.OPICARound4.NativeZeroFrame.zero_odd_gram",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedCompression_isSymmetric",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester",
  "Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSylvester",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet",
  "Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeWeightedSeparationDet",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_squared_ne_zero",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights",
  "Zeta23.OPICARound4.NativeParitySeparation.continuous_nativeScaledCosineWeights",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeScaledCosineWeights_zero",
  "Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeScaledCosine_separation",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeCosineWeights_affine",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_const",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSylvester_cosine",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_cosine",
  "Zeta23.OPICARound4.NativeParitySeparation.eventually_nativeCosine_separation",
  "Zeta23.OPICARound4.NativeParitySeparation.nativeWeightedSeparationDet_injective",
  "Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_separation",
  "Zeta23.OPICARound4.NativeParitySeparation.exists_nativeCosine_sylvester_injective",
  "Zeta23.OPICARound4.RegularCells.isPreconnected_complexFrozenSourceDomain",
  "Zeta23.OPICARound4.RegularCells.isConnected_complexFrozenSourceDomain",
  "Zeta23.OPICARound4.RegularCells.eventually_mem_complexFrozenSourceDomain_at_zero",
  "Zeta23.OPICARound4.RegularCells.exists_nonzero_in_sourceDomain_of_germ",
  "Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive",
  "Zeta23.OPICARound4.RegularCells.exists_source_nonzero_in_open_positive_of_germ",
  "Zeta23.OPICARound4.RegularCells.exists_finite_source_nonzero_in_open_positive_of_germ",
  "Zeta23.OPICARound4.oddNewborn_normalized_even_moment_cubic_energy_bound",
  "Zeta23.OPICARound4.evenNewborn_normalized_odd_corrected_energy_bound",
  "Zeta23.OPICARound4.PrimeIsolation.exists_prime_below_cutoff_square_above",
  "Zeta23.OPICARound4.PrimeIsolation.prime_pow_below_square_eq",
  "Zeta23.OPICARound4.PrimeIsolation.primeSourceWeight_nonzero_isPrimePow",
  "Zeta23.OPICARound4.PrimeIsolation.weight_factorization_zero",
  "Zeta23.OPICARound4.PrimeIsolation.singlePrimePhase",
  "Zeta23.OPICARound4.PrimeIsolation.monomial_singlePrimePhase",
  "Zeta23.OPICARound4.PrimeIsolation.weighted_single_prime_sum",
  "Zeta23.OPICARound4.PrimeIsolation.scaledPrimeMatrix_one",
  "Zeta23.OPICARound4.PrimeIsolation.scaledFrozenPrimeMatrix_single",
  "Zeta23.OPICARound4.PrimeIsolation.circlePhase",
  "Zeta23.OPICARound4.PrimeIsolation.circlePhase_zpow",
  "Zeta23.OPICARound4.PrimeIsolation.circlePhase_symmetric",
  "Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient",
  "Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_pos",
  "Zeta23.OPICARound4.PrimeIsolation.isolatedPrimeCoefficient_eq",
  "Zeta23.OPICARound4.PrimeIsolation.neg_scaledFrozen_single_zero",
  "Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet",
  "Zeta23.OPICARound4.PrimeSourceLaurent.boundedPrimeSet_prime",
  "Zeta23.OPICARound4.PrimeSourceLaurent.primeFactors_subset_boundedPrimeSet",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalExponent",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerPhase_eq_primePhase",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMonomial_zpow",
  "Zeta23.OPICARound4.PrimeSourceLaurent.integerFormalPhase_zpow_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimePotential_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeDiagonal_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalPrimeMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredFrozenPrimeMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalWFreeSourceMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.scaledPrimeMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.factoredScaledPrimeMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_eq",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalScaledSourceMatrix_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal",
  "Zeta23.OPICARound4.PrimeSourceLaurent.rawPhysicalDiagonal_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameGram_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameEnergy_actual",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_det_expansion",
  "Zeta23.OPICARound4.PrimeSourceLaurent.formalRawFrameSylvester_mulVec",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalScaledSourceMatrix",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_rawPhysicalDiagonal",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameGram",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_formalRawFrameSylvesterDet",
  "Zeta23.OPICARound4.PrimeSourceGerms.actual_sylvester_germ_nonzero_of_formal_anchor",
  "Zeta23.OPICARound4.PrimeSourceGerms.formalScaledSourceMatrix_single_zero",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticAt_primeCommonScalar",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualScaledSourceMatrix",
  "Zeta23.OPICARound4.PrimeSourceGerms.analyticOnNhd_actualRawFrameSylvesterDet",
  "Zeta23.OPICARound4.PrimeSourceGerms.exists_actual_sylvester_nonzero_in_open_positive_of_anchor",
  "Zeta23.OPICARound4.NativeParityPencils.zeroCarrier",
  "Zeta23.OPICARound4.NativeParityPencils.rawFrame",
  "Zeta23.OPICARound4.NativeParityPencils.physicalEquiv",
  "Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal",
  "Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_ofReal",
  "Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_real_isSymmetric",
  "Zeta23.OPICARound4.NativeParityPencils.physicalDiagonal_apply",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_physical",
  "Zeta23.OPICARound4.NativeParityPencils.frameGram",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy",
  "Zeta23.OPICARound4.NativeParityPencils.frameGram_physical",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_canonical_physical",
  "Zeta23.OPICARound4.NativeParityPencils.frameGram_zero",
  "Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource",
  "Zeta23.OPICARound4.NativeParityPencils.physicalCommonShift",
  "Zeta23.OPICARound4.NativeParityPencils.scaledPhysicalSource_eq",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_profiles",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_pole_zero",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_add",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_smul",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_identity",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_sub",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_scaledPhysicalSource",
  "Zeta23.OPICARound4.NativeParityPencils.physicalAdjoint_injective",
  "Zeta23.OPICARound4.NativeParityPencils.physical_pencil_eigen_iff",
  "Zeta23.OPICARound4.NativeParityPencils.physical_pencil_nonzero_eigen_iff",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_even",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_rawFrame_zero_odd",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_even",
  "Zeta23.OPICARound4.NativeParityPencils.diagonal_fold_odd",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_weighted",
  "Zeta23.OPICARound4.NativeParityPencils.centered_cosine_eq_fold",
  "Zeta23.OPICARound4.NativeParityPencils.frameEnergy_zero_cosine",
  "Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_matrix_injective",
  "Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_toEuclideanLin",
  "Zeta23.OPICARound4.NativeParitySeparation.matrix_pencil_injective_iff",
  "Zeta23.OPICARound4.NativeParitySeparation.formalRawFrameSylvester_det_iff_coordinate_injective",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_intertwining",
  "Zeta23.OPICARound4.NativeParitySeparation.nativePencilSylvester_isometry_injective_iff",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateIndex",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateIsometry",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_toEuclideanLin",
  "Zeta23.OPICARound4.NativeParityPencils.rawPhysicalDiagonal_eq",
  "Zeta23.OPICARound4.NativeParityPencils.formalScaledSourceMatrix_actual_eq",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy",
  "Zeta23.OPICARound4.NativeParityPencils.coordinatePhysicalEquiv",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_gram_physical",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_energy_physical",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_sylvester_det_iff",
  "Zeta23.OPICARound4.NativeParityPencils.physicalAdjointEquiv",
  "Zeta23.OPICARound4.NativeParityPencils.physicalFullPencil_injective_iff_disjoint",
  "Zeta23.OPICARound4.NativeParityPencils.coordinateFrame_physical_det_iff_disjoint",
  "Zeta23.OPICARound4.NativeParityPencils.native_zero_single_prime_pencil",
  "Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_pencil_injective",
  "Zeta23.OPICARound4.NativeParityPencils.nativeFormalSeparationDet",
  "Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet",
  "Zeta23.OPICARound4.NativeParityPencils.exists_native_formal_separation_anchor",
  "Zeta23.OPICARound4.NativeParityPencils.nativeActualSeparationDet_germ_nonzero",
  "Zeta23.OPICARound4.NativeParityPencils.analyticOnNhd_nativeActualSeparationDet",
  "Zeta23.OPICARound4.NativeParityPencils.exists_nativeActualSeparationDet_nonzero_in_open_positive",
  "Zeta23.OPICARound4.NativeParityPencils.exists_finite_nativeActualSeparationDet_nonzero",
  "Zeta23.OPICARound4.NativeParityPencils.isOpen_positive_nativeActualSeparationDet_nonzero",
  "Zeta23.OPICARound4.NativeParityPencils.exists_regular_and_separationDet_in_open_fixedCell",
  "Zeta23.OPICARound4.NativeParityPencils.exists_bounded_regular_and_separationDet_in_open_above_one",
  "Zeta23.OPICARound4.NativeParityPencils.cofinally_both_negative_regular_and_separationDet",
  "Zeta23.OPICARound4.separated_native_even_eigen_channels_visible",
  "Zeta23.OPICARound4.separated_native_odd_eigen_channels_visible",
  "Zeta23.OPICARound4.separated_native_even_eigenspace_finrank_le_one",
  "Zeta23.OPICARound4.separated_native_odd_eigenspace_finrank_le_one",
  "Zeta23.OPICARound4.RegularCells.continuousAt_actual_original_phase_energy",
  "Zeta23.OPICARound4.RegularCells.exists_actual_original_depth_transport_threshold",
  "Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_with_open_selection",
  "Zeta23.OPICARound4.RegularCells.exists_actual_generated_packet_native_regular",
  "Zeta23.OPICARound4.RegularCells.exists_actual_composed_packet_native_regular",
  "Zeta23.OPICARound4.RegularCells.cofinally_actual_regular_packet_joint_detector_ground",
  "Zeta23.OPICARound4.NativeParityPencils.exists_actual_generated_packet_regular_separationDet",
  "Zeta23.OPICARound4.NativeParityPencils.exists_actual_composed_packet_regular_separationDet",
  "Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_separationDet",
  "Zeta23.OPICARound4.NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.limiting_full_compressions_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.grouped_genuine_prime_laurent_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.actual_full_source_nonidentity_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.bounded_actual_regular_separation_selection_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.complete_even_source_and_eigenspace_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.complete_odd_source_and_eigenspace_check",
  "Zeta23.OPICARound4.Validation.NativeNoncollision.genuine_packet_same_detector_spectral_check",
  "Zeta23.OPICARound4.recenteredFiniteApprox_interval_energy",
  "Zeta23.OPICARound4.recenteredSmoothPhase_interval_energy_eq_one",
  "Zeta23.OPICARound4.recenteredFinitePhase_mass_error_le",
  "Zeta23.OPICARound4.exists_recentered_mass_control_threshold",
  "Zeta23.OPICARound4.recentered_negative_phase_eventually_relative_margin",
  "Zeta23.OPICARound4.eventually_both_ground_margins_at_original_quartic",
  "Zeta23.OPICARound4.originalDetectorFiniteEvenPhase_moment_four",
  "Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_three",
  "Zeta23.OPICARound4.originalDetectorFiniteOddPhase_moment_five",
  "Zeta23.OPICARound4.eventually_both_negative_moment_slices_at_original_quartic",
  "Zeta23.OPICARound4.eventually_both_moment_slice_margins_at_original_quartic",
  "Zeta23.OPICARound4.Validation.actual_recentered_mass_error_consumer",
  "Zeta23.OPICARound4.Validation.actual_both_moment_slice_margins_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_apply",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_apply",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_evenMomentSlice_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_oddMomentSlice_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy",
  "Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceVanishingErrorBounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.EvenMomentSliceLowerBound.mono",
  "Zeta23.OPICARound4.ArithmeticFrontier.OddMomentSliceLowerBound.mono",
  "Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceLowerBound.mono",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_bottom",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_bottom",
  "Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slice_witnesses",
  "Zeta23.OPICARound4.ArithmeticFrontier.eventually_no_moment_slice_lower_bound_below_margin",
  "Zeta23.OPICARound4.ArithmeticFrontier.spec_chart_eq_fixedSeedDiagonalEntry",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenMomentSeed",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedOddMomentSeed",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedEvenMomentSeed_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_fixedOddMomentSeed_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenPhysicalMoment_four_of_seed",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_three_of_seed",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddPhysicalMoment_five_of_seed",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedEvenSeedPhysicalEquiv_mem_slice_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedOddSeedPhysicalEquiv_mem_slice_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_inner",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_inner",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceSeedEquiv_norm_sq",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceSeedEquiv_norm_sq",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_seed_gram",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_seed_gram",
  "Zeta23.OPICARound4.ArithmeticFrontier.seedCoordinateNormSq",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_ge",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedSeedGram_re_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_coordinate_tolerance",
  "Zeta23.OPICARound4.ArithmeticFrontier.coordinate_tolerance_of_evenMomentSliceLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedEvenSeed_sixth_moment_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_fifth_moment_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_fixedOddSeed_seventh_moment_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.finrank_evenMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.finrank_oddMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.quartic_moment_slices_nontrivial",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSlice_eq_bot_of_le_three",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSlice_eq_bot_of_le_four",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_three",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_le_four",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_moment_slice_bounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_bounds_of_off_line_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_even",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_odd",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_tendsto",
  "Zeta23.OPICARound4.ArithmeticFrontier.NativeGroundResponseRestriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.NativeSpectraDisjoint",
  "Zeta23.OPICARound4.ArithmeticFrontier.rayleighBottoms_ne_of_spectra_disjoint",
  "Zeta23.OPICARound4.ArithmeticFrontier.noBothNeg_of_ground_response_and_disjoint_spectra",
  "Zeta23.OPICARound4.ArithmeticFrontier.packetAperture",
  "Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_pos",
  "Zeta23.OPICARound4.ArithmeticFrontier.packetAperture_gt",
  "Zeta23.OPICARound4.ArithmeticFrontier.packetDetectorCutoff_three_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketGroundRestriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_ground_restriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.EventualDisjointQuarticGroundRestriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.selected_packet_ground_restriction_of_eventual_disjoint",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.eventual_disjoint_quartic_ground_restriction_of_ground_closure",
  "Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketWithGroundRestriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_selected_packet_with_ground_restriction",
  "Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy",
  "Zeta23.OPICARound4.ArithmeticFrontier.correctedSchurForm",
  "Zeta23.OPICARound4.ArithmeticFrontier.inverseResidual",
  "Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_eq_residual_form",
  "Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.schur_inverse_residual_identity",
  "Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_scalar_gap",
  "Zeta23.OPICARound4.ArithmeticFrontier.shifted_form_mono",
  "Zeta23.OPICARound4.ArithmeticFrontier.CoreLeakageBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.selfAdjoint_energy_split",
  "Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.core_shift_certificate_of_columns",
  "Zeta23.OPICARound4.ArithmeticFrontier.core_witness_transport",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.cofinal_moment_closure_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.moment_slice_witness_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.quartic_slice_dimension_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.seed_gram_transport_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.disjoint_quartic_ground_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.inverse_residual_certificate_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.core_shift_consumer",
  "Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_dot_oddBoundaryFlat_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_even_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_toEuclideanLin_odd_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_even_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalPole_inner_odd_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenNativeEnergy_eq_neg_arch_sub_prime",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddNativeEnergy_eq_neg_arch_sub_prime",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_iff_arch_prime",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_iff_arch_prime",
  "Zeta23.OPICARound4.ArithmeticFrontier.leakage_adjoint",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_geometry_mul_energy",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_energy_mul_geometry",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_one_normal",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_commutator_eq_of_no_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.froSq",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_add",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sub",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_smul",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_mul_transpose_nonneg",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_sq_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.normSq_pos",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.quad_near_shift",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.pencil_checkpoint_of_posDef",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.shifted_factor_requires_positive_shift",
  "Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_gram_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_energy_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_conjTranspose",
  "Zeta23.OPICARound4.ArithmeticFrontier.columnProjection_idempotent",
  "Zeta23.OPICARound4.ArithmeticFrontier.complementProjection_sq",
  "Zeta23.OPICARound4.ArithmeticFrontier.sourceColumn_residual_trace",
  "Zeta23.OPICARound4.ArithmeticFrontier.originalDetectorFiniteEvenPhaseUnit_mem_evenMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.originalDetectorFiniteOddPhaseUnit_mem_oddMomentSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_evenMomentSlice_exp_depth",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_oddMomentSlice_exp_depth",
  "Zeta23.OPICARound4.ArithmeticFrontier.EvenFixedRateMomentSliceBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.OddFixedRateMomentSliceBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.FixedParitySubexponentialMomentSliceBounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.FixedParityPolynomialMomentSliceBounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.mul_exp_lt_exp_of_log_div_lt",
  "Zeta23.OPICARound4.ArithmeticFrontier.abs_re_sub_half_le_of_even_fixed_rate",
  "Zeta23.OPICARound4.ArithmeticFrontier.abs_re_sub_half_le_of_odd_fixed_rate",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_fixed_parity_subexponential",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_fixed_parity_subexponential",
  "Zeta23.OPICARound4.ArithmeticFrontier.one_add_pow_le_mul_exp",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixed_parity_subexponential_of_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_fixed_parity_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.not_fixed_parity_polynomial_of_off_line_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.recentered_phase_energy_lt_explicit",
  "Zeta23.OPICARound4.ArithmeticFrontier.recentered_phase_relative_margin_explicit",
  "Zeta23.OPICARound4.ArithmeticFrontier.exists_fixed_phase_below",
  "Zeta23.OPICARound4.ArithmeticFrontier.eventually_both_moment_slices_below",
  "Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentSliceSemibounded",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_cofinal_semibounded",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_semibounded",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_semibounded_of_cofinal_moment_slice_bounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.not_cofinal_moment_slice_semibounded_of_off_line_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.ActualLongTermFixedRateLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.ActualLongTermSubexponentialLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.ActualLongTermPolynomialLowerBound",
  "Zeta23.OPICARound4.ArithmeticFrontier.correlation_lower_of_longTerm_fixed_rate",
  "Zeta23.OPICARound4.ArithmeticFrontier.abs_re_sub_half_le_of_longTerm_fixed_rate",
  "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_longTerm_subexponential",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_longTerm_subexponential",
  "Zeta23.OPICARound4.ArithmeticFrontier.longTerm_subexponential_of_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_longTerm_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.longTerm_fixed_rate_zero_of_constant",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexMatrix",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexMatrix_eq_diagonal",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexMatrix_conjTranspose",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_commutator_apply",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_commutator_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.star_dotProduct_vecMulVec_mulVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.one_dotProduct_eq_centeredMoment_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.index_dotProduct_eq_centeredMoment_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.star_dotProduct_one",
  "Zeta23.OPICARound4.ArithmeticFrontier.star_dotProduct_index",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_commutator_form_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_commutator_form_eq_zero_of_boundaryFlat",
  "Zeta23.OPICARound4.ArithmeticFrontier.conjTranspose_mul_mul_apply",
  "Zeta23.OPICARound4.ArithmeticFrontier.compressed_squaredIndex_commutator_eq_zero",
  "Zeta23.OPICARound4.ArithmeticFrontier.native_compressed_commutator_eq",
  "Zeta23.OPICARound4.ArithmeticFrontier.centeredMoment_squaredIndex_mulVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_mem_even",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_mem_odd",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_even_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_odd_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.poleEvenProfile_mul_centeredIndex_sq",
  "Zeta23.OPICARound4.ArithmeticFrontier.poleOddProfile_mul_centeredIndex_sq",
  "Zeta23.OPICARound4.ArithmeticFrontier.poleEven_sum_squaredIndex_mulVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.poleOdd_sum_squaredIndex_mulVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_even_slice_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndex_mulVec_odd_slice_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszCoeff",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_rieszSlice_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszVec_mem",
  "Zeta23.OPICARound4.ArithmeticFrontier.inner_rieszVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.inner_rieszVec_of_mem_slice",
  "Zeta23.OPICARound4.ArithmeticFrontier.sub_rieszCoeff_mem",
  "Zeta23.OPICARound4.ArithmeticFrontier.starProjection_rieszSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.sub_starProjection_rieszSlice",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszSlice_compressed_commutator",
  "Zeta23.OPICARound4.ArithmeticFrontier.centeredPowerVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.inner_centeredPowerVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenFlatPoleAmb",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddFlatPoleM3Amb",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenSliceAmb",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddSliceAmb",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenLeakageVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddLeakageVec",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_evenSliceAmb_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.mem_oddSliceAmb_iff",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexOp",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalSourceOp",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexOp_isSymmetric",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalSourceOp_isSymmetric",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexOp_source_commute_form",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexOp_mem_evenFlatPole",
  "Zeta23.OPICARound4.ArithmeticFrontier.squaredIndexOp_mem_oddFlatPoleM3",
  "Zeta23.OPICARound4.ArithmeticFrontier.inner_evenLeakageVec_squaredIndexOp",
  "Zeta23.OPICARound4.ArithmeticFrontier.inner_oddLeakageVec_squaredIndexOp",
  "Zeta23.OPICARound4.ArithmeticFrontier.even_slice_rank_one_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.odd_slice_rank_one_leakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.even_native_rank_two_commutator",
  "Zeta23.OPICARound4.ArithmeticFrontier.odd_native_rank_two_commutator",
  "Zeta23.OPICARound4.ArithmeticFrontier.reconstruction_offdiag_entry_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.sum_norm_mul_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.reconstruction_lower_bound",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszSlice_eigen_commutator",
  "Zeta23.OPICARound4.ArithmeticFrontier.rieszSlice_form_lower_of_geometry_basis",
  "Zeta23.OPICARound4.ArithmeticFrontier.EvenGeometryResponseCertificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.OddGeometryResponseCertificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_certificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_certificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.FixedParityGeometryResponsePolynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixed_parity_polynomial_of_geometry_response",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_geometry_response_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_cexp_I_mul_le_of_mem_Icc",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_paperFT_le_of_support_Icc",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_paperFT_mul_sq_le_of_support_Icc",
  "Zeta23.OPICARound4.ArithmeticFrontier.weilL1Budget",
  "Zeta23.OPICARound4.ArithmeticFrontier.weilL1Budget_nonneg",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_paperFT_mul_one_add_normSq_le_of_support_Icc",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_paperFT_pair_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.zetaZeroInvSqWeight",
  "Zeta23.OPICARound4.ArithmeticFrontier.summable_zetaZeroInvSqWeight",
  "Zeta23.OPICARound4.ArithmeticFrontier.zetaZeroInvSqWeight_nonneg",
  "Zeta23.OPICARound4.ArithmeticFrontier.zeta_W_self_re_ge_neg_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_localizedFrequency_centered_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_localizedFiniteFunction_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.norm_localizedFiniteSecondJet_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.integral_norm_indicator_Icc_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.deriv_deriv_localizedFiniteVector_of_boundaryFlat",
  "Zeta23.OPICARound4.ArithmeticFrontier.weilL1Budget_localizedFiniteVector_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.sq_sum_norm_equiv_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeFloorBudget",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeFloorBudget_nonneg",
  "Zeta23.OPICARound4.ArithmeticFrontier.canonicalSource_re_inner_ge_neg_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeFloorBudget_quartic_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenFixedRateMomentSliceBound_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddFixedRateMomentSliceBound_of_zeroStrip",
  "Zeta23.OPICARound4.ArithmeticFrontier.zeroStrip_iff_even_fixed_rates",
  "Zeta23.OPICARound4.ArithmeticFrontier.zeroStrip_iff_odd_fixed_rates",
  "Zeta23.OPICARound4.ArithmeticFrontier.abs_re_sub_half_le_of_re_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedRateMomentSliceBounds_of_re_le",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixedRateMomentSliceBounds_of_half_lt",
  "Zeta23.OPICARound4.ArithmeticFrontier.evenMomentSliceLowerBound_zero_of_critical_line",
  "Zeta23.OPICARound4.ArithmeticFrontier.oddMomentSliceLowerBound_zero_of_critical_line",
  "Zeta23.OPICARound4.ArithmeticFrontier.momentSliceLowerBounds_zero_of_riemannHypothesis",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_riemannHypothesis",
  "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_semibounded_of_riemannHypothesis",
  "Zeta23.OPICARound4.ArithmeticFrontier.fixed_parity_polynomial_of_riemannHypothesis",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_bounds",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_semibounded",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_fixed_parity_polynomial",
  "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_fixed_parity_subexponential",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeDeepThresholdGround_depth_pos",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeDeepThresholdGround_predecessor_empty_of_bottom_three_lt",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeDeepThresholdGround_cutoff_eq_three_of_even_trial",
  "Zeta23.OPICARound4.ArithmeticFrontier.nativeDeepThresholdGround_cutoff_eq_three_of_odd_trial"
]
MADNESS_MODULES = [
  "Zeta23.OPICARound4.MobiusHyperbola",
  "Zeta23.OPICARound4.ActualSourceHyperbola",
  "Zeta23.OPICARound4.HyperbolaDiagonal",
  "Zeta23.OPICARound4.Validation.Hyperbola",
  "Zeta23.OPICARound4.CommonQuarticGround",
  "Zeta23.OPICARound4.JointGroundBirth",
  "Zeta23.OPICARound4.Validation.JointGround",
  "Zeta23.OPICARound4.TiedNewbornResponse",
  "Zeta23.OPICARound4.NewbornSpectralVisibility",
  "Zeta23.OPICARound4.TiedCubicEnergy",
  "Zeta23.OPICARound4.TiedSilentMoment",
  "Zeta23.OPICARound4.RegularCells.AnalyticFiniteSelector",
  "Zeta23.OPICARound4.RegularCells.NativeZeroRegularity",
  "Zeta23.OPICARound4.RegularCells.NativeRegularBirthSelection",
  "Zeta23.OPICARound4.Validation.NativeGroundRegularity",
  "Zeta23.OPICARound4.RegularCells.NativeDiagonalSeparation",
  "Zeta23.OPICARound4.RegularCells.NativeCompressionSeparation",
  "Zeta23.OPICARound4.RegularCells.SylvesterSeparation",
  "Zeta23.OPICARound4.RegularCells.MeromorphicFrequencyIndependence",
  "Zeta23.OPICARound4.RegularCells.PrimeLaurentNonidentity",
  "Zeta23.OPICARound4.RegularCells.FinitePrimeLaurentAlgebra",
  "Zeta23.OPICARound4.RegularCells.PrimeSourceLaurent",
  "Zeta23.OPICARound4.RegularCells.NativeZeroFrame",
  "Zeta23.OPICARound4.RegularCells.NativeCosineSeparation",
  "Zeta23.OPICARound4.RegularCells.FrozenSourceContinuation",
  "Zeta23.OPICARound4.NewbornCubicEnergyBound",
  "Zeta23.OPICARound4.RegularCells.NativePrimeIsolation",
  "Zeta23.OPICARound4.RegularCells.NativePrimeExpansion",
  "Zeta23.OPICARound4.RegularCells.NativePrimeGerms",
  "Zeta23.OPICARound4.RegularCells.NativeParityPencils",
  "Zeta23.OPICARound4.RegularCells.NativeParityZeroPencils",
  "Zeta23.OPICARound4.RegularCells.MatrixSylvesterCoordinates",
  "Zeta23.OPICARound4.RegularCells.NativeParityMatrixPencils",
  "Zeta23.OPICARound4.RegularCells.NativeParityPhysicalSeparation",
  "Zeta23.OPICARound4.RegularCells.NativeParityPrimeAnchor",
  "Zeta23.OPICARound4.RegularCells.NativeParityNonidentity",
  "Zeta23.OPICARound4.RegularCells.NativeParityRegularSelection",
  "Zeta23.OPICARound4.SeparatedSourceVisibility",
  "Zeta23.OPICARound4.RegularCells.PacketRegularSelection",
  "Zeta23.OPICARound4.RegularCells.PacketNoncollisionSelection",
  "Zeta23.OPICARound4.RegularCells.PacketSpectralSelection",
  "Zeta23.OPICARound4.Validation.NativeNoncollision",
  "Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices",
  "Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates",
  "Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure",
  "Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketClosure",
  "Zeta23.OPICARound4.ArithmeticFrontier.PhysicalBlockCertificate",
  "Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnCore",
  "Zeta23.OPICARound4.ArithmeticFrontier.Validation.Carriers",
  "Zeta23.OPICARound4.ArithmeticFrontier.PoleChannel",
  "Zeta23.OPICARound4.ArithmeticFrontier.MomentLeakage",
  "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness",
  "Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnTrace",
  "Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure",
  "Zeta23.OPICARound4.ArithmeticFrontier.CofinalSemiboundedClosure",
  "Zeta23.OPICARound4.ArithmeticFrontier.C2GrowthClosure",
  "Zeta23.OPICARound4.ArithmeticFrontier.NativeMomentDisplacement",
  "Zeta23.OPICARound4.ArithmeticFrontier.NativeLeakageFactor",
  "Zeta23.OPICARound4.ArithmeticFrontier.GeometryReconstruction",
  "Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor"
]
EXPECTED_DECLARATIONS = PRE_MADNESS_DECLARATIONS + MADNESS_DECLARATIONS
MODULES = PRE_MADNESS_MODULES + MADNESS_MODULES
EXPECTED_DECLARATION_COUNT = 1367
EXPECTED_MODULE_COUNT = 108
# The exact 1079/90/84 PR299 scope preceding the arithmetic-frontier extension remains mandatory.
PRE_FRONTIER_DECLARATION_COUNT = 1079
PRE_FRONTIER_MODULE_COUNT = 90
PRE_FRONTIER_DECLARATIONS_SHA256 = 'b4b77c8135ec01660329f03c246ca89592871b4ccd30a39926c4e33ed9276779'
PRE_FRONTIER_MODULES_SHA256 = 'e11179414a48aa1b0124040c2d67efa38aa8c3bdcd59fe8e195d50fe09cca881'
FRONTIER_MODULES = ["Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices", "Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates", "Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure", "Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketClosure", "Zeta23.OPICARound4.ArithmeticFrontier.PhysicalBlockCertificate", "Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnCore", "Zeta23.OPICARound4.ArithmeticFrontier.Validation.Carriers", "Zeta23.OPICARound4.ArithmeticFrontier.PoleChannel", "Zeta23.OPICARound4.ArithmeticFrontier.MomentLeakage", "Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness", "Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnTrace", "Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure", "Zeta23.OPICARound4.ArithmeticFrontier.CofinalSemiboundedClosure", "Zeta23.OPICARound4.ArithmeticFrontier.C2GrowthClosure", "Zeta23.OPICARound4.ArithmeticFrontier.NativeMomentDisplacement", "Zeta23.OPICARound4.ArithmeticFrontier.NativeLeakageFactor", "Zeta23.OPICARound4.ArithmeticFrontier.GeometryReconstruction", "Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor"]
# MADNESS_INVENTORY_END
# SOURCE_CONSTRAINT_INVENTORY_END
BASELINE_DECLARATION_COUNT = 98
BASELINE_MODULE_COUNT = 16
# SOURCE_CONSTRAINT_MUTATIONS_BEGIN
INTEGRATION_SEMANTIC_MUTATIONS = 'import Zeta23.OPICARound4.Validation.Support\nimport Zeta23.OPICARound4.OddReciprocalSource\nimport Zeta23.OPICARound4.Validation.IntegrationSpectral\nimport Zeta23.OPICARound4.VisibilityRigidity\n\nnoncomputable section\nnamespace Zeta23.OPICARound4.RejectedSemanticMutations\nopen CCM OPICARound3\nopen scoped BigOperators\n\nvariable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]\n  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]\n  [FiniteDimensional ℂ F]\n\n-- Removing the witness-response norm cost must be rejected.\nexample (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)\n    (e : isometricDetectorComplement J)\n    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :\n    ‖regularSchurWitness J T e hb‖ ^ 2 = ‖(e : F)‖ ^ 2 :=\n  regular_witness_norm_sq J T e hb\n\n-- PSD predecessor plus a one-dimensional shell does not assert successor negativity.\nexample (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)\n    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)\n    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1) (w : F) :\n    (∀ N : Submodule ℂ F,\n      (∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) → Module.finrank ℂ N ≤ 1) ∧\n    ∃ N : Submodule ℂ F, Module.finrank ℂ N = 1 ∧\n      ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0 :=\n  one_shell_negative_index_exact J T hP hshell w\n\n-- Omitting the removed canonical output changes the source functional.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)\n    (u : poleNeutralEvenSubspace L K) :\n    cubicDefectFunctional L K u.val =\n      inner ℂ (correctedSourceRow L K) ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) :=\n  correctedSourceRow_native hL K hK u\n\n-- A source equality at K cannot be silently transported to a different M.\nexample {L : ℝ} (hL : 0 < L) (K M : ℕ) (hK : 3 ≤ K) (hM : 3 ≤ M)\n    (lam : ℝ) (hlamK : lam < poleNeutralOddRayleighBottom L K hL hK)\n    (hlamM : lam < poleNeutralOddRayleighBottom L M hL hM)\n    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)\n    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :\n    poleNeutralCorrectedCubicSource L M (poleNeutralEvenShiftedRay hL M hM lam hlamM) = 1 :=\n  poleNeutral_even_eigen_shiftedRay_source_eq_one hL K hK lam hlamK u hu0 hu\n\n-- The response-facing odd test uses the reciprocal input, not the Riesz input.\n-- Scalar aliases retain exact native values while avoiding huge inverse reduction.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)\n    (sourceRiesz sourceReciprocal : ℂ)\n    (_hRiesz : sourceRiesz = poleNeutralCorrectedCubicSource L K\n      ((poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm\n        (poleNeutralCorrectedCubicRieszVector L K)))\n    (hReciprocal : sourceReciprocal = poleNeutralCorrectedCubicSource L K\n      (nativeOddReciprocalInput hL K hK lam hlam)) :\n    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =\n      -star sourceRiesz := by\n  have htrue : poleNeutralCubicPairingFunctional L K\n      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) = -star sourceReciprocal := by\n    rw [hReciprocal]\n    exact native_odd_response_eq_reciprocal_source hL K hK lam hlam\n  exact htrue\n\n-- Omitting the material odd-response minus sign changes the statement.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)\n    (sourceReciprocal : ℂ)\n    (hReciprocal : sourceReciprocal = poleNeutralCorrectedCubicSource L K\n      (nativeOddReciprocalInput hL K hK lam hlam)) :\n    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =\n      star sourceReciprocal := by\n  have htrue : poleNeutralCubicPairingFunctional L K\n      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) = -star sourceReciprocal := by\n    rw [hReciprocal]\n    exact native_odd_response_eq_reciprocal_source hL K hK lam hlam\n  exact htrue\n\n-- Reality of the grouped residue does not give reality of basis-coordinate terms.\nexample :\n    (Validation.repeatedSpectrumCoordinateCoefficient Validation.repeatedSpectrumP₁).im = 0 :=\n  Validation.repeated_spectrum_nonreal_coordinates.2.2.1\n\n-- Full input/output visibility gives nonzero mass, not nonnegative mass.\nexample (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) (hB : B.IsSymmetric)\n    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)\n    (hrank : RankOneIntertwining A B D g f) (β : GroupedSpectrum B)\n    (hin : ¬ GroupedInputInvisible hB g β) (hout : ¬ GroupedOutputInvisible hB D f β) :\n    0 ≤ groupedSignedResidue hB D g f β := by\n  have hnonzero : groupedSignedResidue hB D g f β ≠ 0 := by\n    intro hz\n    rcases (grouped_residue_zero_iff_input_or_output_invisible hA hB D g f hrank β).mp hz with h | h\n    · exact hin h\n    · exact hout h\n  exact hnonzero\n\n-- The signed Pick index is bounded by the negative atom count, not by one.\nexample {ι κ : Type*} [Fintype ι] [Fintype κ]\n    (eigenvalue residue : ι → ℝ) (points : κ → ℂ) (N : Submodule ℂ (κ → ℂ))\n    (hN : ∀ a : N, a ≠ 0 →\n      (∑ j, ∑ k, (a : κ → ℂ) j * signedPickKernel eigenvalue residue\n        (points j) (points k) * star ((a : κ → ℂ) k)).re < 0) :\n    Module.finrank ℂ N ≤ 1 :=\n  finite_signed_pick_negative_subspace_bound eigenvalue residue points N hN\n\n\nend Zeta23.OPICARound4.RejectedSemanticMutations\n'
INTEGRATION_SEMANTIC_MUTATION_COUNT = 9
SOURCE_CONSTRAINT_MUTATIONS = '-- Source constraint mutation: geometry_wrong_even_sign.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :\n    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs\n    nativeSignedPrimeDiscrepancy L K r = nativeArchContinuumRow L K r + 1 :=\n  (actual_even_ground_signed_discrepancy hL K hK hs).2.1\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: geometry_wrong_odd_input.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :\n    poleNeutralCorrectedCubicSource L K\n      ((poleNeutralEvenShiftedCanonicalEquiv hL K hK\n        (poleNeutralOddRayleighBottom L K hL hK) hs).symm (poleNeutralCorrectedCubicRieszVector L K)) = -1 :=\n  (actual_odd_ground_reciprocal_discrepancy hL K hK hs).1\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: geometry_omitted_tie.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :\n    NativeStrictEvenGroundConstraints hL K hK ∨ NativeStrictOddGroundConstraints hL K hK :=\n  joint_ground_constraints_of_both_negative hL K hK hboth\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/WrongSmoothShift.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a)\n    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)\n      (out.retained.state.selection.cutoff - 1)) :\n    inner ℂ v (smoothSourceForcing out) =\n      zetaZeroConfig.W out.originalTrial (out.forcingTest v) -\n        (out.retained.state.selection.eta : ℂ) * EF.weilTest out.originalTrial (out.forcingTest v) 0 :=\n  validation_smooth_source_forcing out v\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/DroppedSchurMassError.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a) :\n    |detectorSchurLoss out - smoothSourceMain out| ≤\n      sourceInverseBudget out * sourceForcingErrorBudget out *\n        (2 * finiteForcingBudget out + sourceForcingErrorBudget out) +\n      sourceEnergyErrorBudget (fixedOriginalSincTrialAperture a) :=\n  detectorSchurLoss_sub_smoothSourceMain_bound out\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/DroppedFirstCutoffEnergy.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a)\n    (hK : out.retained.state.selection.cutoff = 3) :\n    detectorSchurLoss out = -out.retained.state.selection.eta :=\n  detectorSchurLoss_at_first out hK\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: quartic/mutations/SourceErrorWrongQuantifier.lean\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\n\n-- Incorrect strengthening: one threshold is required to pay every M\n-- simultaneously. The proved threshold is selected after each fixed M.\nexample (δ : ℝ) (hδ : 0 < δ) :\n    ∃ L₀ : ℝ, ∀ (M β : ℝ) (σ : ReversalParity) (a : ℝ)\n      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →\n      |detectorSchurLoss out - smoothSourceMain out| <\n        δ * Real.exp (-M * fixedOriginalSincTrialAperture a) := by\n  exact exists_uniform_source_schur_error_threshold 0 δ hδ\n\n\n-- Source constraint mutation: quartic/mutations/SourceMainWrongSign.lean\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\n\n-- The surviving source requirement is a lower bound. Treating it as an\n-- independently proved upper bound would manufacture the missing Step4 law.\nexample :\n    ∃ L₀ : ℝ, ∀ (ρ : zetaZeroConfig.carrier) (β : ℝ)\n      (σ : ReversalParity) (R : ℝ)\n      (g : GeneratedStep123CompleteOutput ρ β σ R), L₀ ≤ R →\n        smoothSourceMain g.generated.native <\n          Real.exp (β * fixedOriginalSincTrialAperture g.generated.sourceData.separation) / 4 := by\n  exact exists_generated_smooth_source_main_lower_threshold\n'
SOURCE_CONSTRAINT_MUTATION_IMPORTS = 'import Zeta23.OPICARound4.JointGroundConstraints\nimport Zeta23.OPICARound4.QuarticErrorReduction\nimport Zeta23.OPICARound4.Validation.DetectorErrors\n'
PRE_MADNESS_SEMANTIC_MUTATIONS = SOURCE_CONSTRAINT_MUTATION_IMPORTS + INTEGRATION_SEMANTIC_MUTATIONS + SOURCE_CONSTRAINT_MUTATIONS
PRE_MADNESS_SEMANTIC_MUTATION_COUNT = 17
MADNESS_SEMANTIC_MUTATION_IMPORTS = 'import Zeta23.OPICARound4.RegularCells.NativeDiagonalSeparation\nimport Zeta23.OPICARound4.RegularCells.NativeCosineSeparation\nimport Zeta23.OPICARound4.RegularCells.NativeZeroFrame\nimport Zeta23.OPICARound4.RegularCells.NativePrimeIsolation\nimport Zeta23.OPICARound4.RegularCells.NativePrimeExpansion\nimport Zeta23.OPICARound4.RegularCells.NativePrimeGerms\nimport Zeta23.OPICARound4.RegularCells.NativeParityPencils\nimport Zeta23.OPICARound4.RegularCells.NativeParityNonidentity\nimport Zeta23.OPICARound4.SeparatedSourceVisibility\nimport Zeta23.OPICARound4.RegularCells.PacketRegularSelection\nimport Zeta23.OPICARound4.RegularCells.PacketNoncollisionSelection\nimport Zeta23.OPICARound4.RegularCells.NativeParityPhysicalSeparation\nimport Zeta23.OPICARound4.Validation.Hyperbola\nimport Zeta23.OPICARound4.Validation.JointGround\nimport Zeta23.OPICARound4.TiedNewbornResponse\nimport Zeta23.OPICARound4.NewbornSpectralVisibility\nimport Zeta23.OPICARound4.TiedCubicEnergy\nimport Zeta23.OPICARound4.TiedSilentMoment\nimport Zeta23.OPICARound4.RegularCells.NativeZeroRegularity\nimport Zeta23.OPICARound4.RegularCells.NativeRegularBirthSelection\n'
MADNESS_SEMANTIC_MUTATIONS = 'noncomputable section\nnamespace Zeta23.OPICARound4.MadnessRejectedMutations\nopen Finset\n\n-- The hyperbola boundary has a minus sign.\nexample (t : ℝ) :\n    actualCorrelationPrimeField t =\n      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) +\n        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) :=\n  actualCorrelationPrimeField_hyperbola_half t\n\n-- Removing the square-root normalization changes the actual integer-drive identity.\nexample (t : ℝ) (a : ℕ) (ha : 0 < a) :\n    actualCorrelationLogarithmicTest t a = actualCorrelationIntegerDrive (t - Real.log a) :=\n  actualCorrelationLogarithmicTest_eq_integerDrive t a ha\n\n-- The exact total cannot discard the diagonal contribution.\nexample (P R : ℝ → ℝ) (I x : ℝ) (Y : ℕ)\n    (hP : ∀ y : ℝ, P y = I * y + R y) :\n    mobiusPoissonQuadratic P x Y =\n      mobiusPoissonRankOne I x Y + mobiusPoissonOffDiagonal R x Y :=\n  mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal P R I x Y hP\n\n-- An equivalence between two lower bounds does not prove either lower bound.\nexample (P R : ℝ → ℝ) (I : ℝ) {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)\n    (hP : ∀ y : ℝ, P y = I * y + R y)\n    (hR : ∀ y : ℝ, 1 / T ≤ y → |R y| ≤ M) :\n    HasEventualSqrtLower (fun x => mobiusPoissonQuadratic P x ⌊Real.sqrt (T*x)⌋₊) :=\n  eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal P R I hT hM hP hR\n\n\n-- A bounded higher-power part does not bound the complete prime field.\nexample : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |actualCorrelationPrimeField t| ≤ C :=\n  actualCorrelationHigherPrimePowers_uniform_bound\n\n-- The complete prime field must retain the higher-power contribution.\nexample (t : ℝ) : actualCorrelationPrimeField t =\n    (∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t) with n.Prime,\n      Real.log n * actualCorrelationWeight t n) :=\n  actualCorrelationPrimeField_split_prime_powers t\n\n-- Rapid decay of the integer-drive derivative is not decay of its Mobius inverse.\nexample (A : ℝ) (hA : 0 < A) :\n    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →\n      |actualCorrelationPrimeField t| ≤ C * Real.exp (-A * t) :=\n  actualCorrelationIntegerDrive_deriv_rapid_bound A hA\n\n-- The derivative must include the derivative of the square-root normalization.\nexample {r : ℝ} (hr : 0 < r) :\n    HasDerivAt actualFlatMobiusTest\n      (-(deriv actualCorrelationIntegerDrive (-Real.log r)) / (r * Real.sqrt r)) r :=\n  actualFlatMobiusTest_hasDerivAt hr\n\n\n-- The actual diagonal sqrt bound is not a uniform constant bound.\nexample (T : ℝ) (hT : 0 < T) :\n    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 0 < x →\n      |aliasDiagonal actualFlatSamplingRemainder x ⌊Real.sqrt (T*x)⌋₊| ≤ D :=\n  actualFlatSamplingDiagonal_sqrt_bound T hT\n\n-- An equivalence of the two remaining targets proves neither lower bound.\nexample (T : ℝ) (hT : 0 < T) :\n    HasEventualSqrtLower (fun x =>\n      mobiusPoissonQuadratic actualFlatSamplingSum x ⌊Real.sqrt (T*x)⌋₊) :=\n  actualFlatSampling_eventual_lower_iff T hT\n\n\n-- The literal diagonal cannot be discarded as zero.\nexample (t : ℝ) :\n    |aliasDiagonal actualFlatSamplingRemainder (Real.exp t)\n      (Nat.sqrt (actualCorrelationCutoff t / 2))| ≤ 0 := by\n  exact (Classical.choose_spec actualCorrelationNativeDiagonal_bound).2 t\n\n-- A conversion still requires a proof of its input bound.\nexample : ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →\n    -C ≤ hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) := by\n  exact actualCorrelationLongTerm_eventual_lower_iff_combined.mpr\n\n\n-- Positive actual mass controls the rank-one term, not the complete quadratic.\nexample {x : ℝ} (hx : 0 ≤ x) (Y : ℕ) :\n    0 ≤ mobiusPoissonQuadratic actualFlatSamplingSum x Y :=\n  mobiusPoissonRankOne_nonneg actualFlatSamplingMass_pos.le hx Y\n\n\n-- The literal translated correlation has 2*a, not a, in both prime histories.\nexample (a : ℝ) :\n    ExceptionalZero.fixedOriginalSincCorrelationReal a = actualCorrelationArch a -\n      actualCorrelationPrimeField a - actualCorrelationPrimeField (-a) :=\n  actualCorrelation_explicit_formula a\n\n-- The reflected history cannot be dropped without its late-support condition.\nexample (a : ℝ) :\n    ExceptionalZero.fixedOriginalSincCorrelationReal a = actualCorrelationArch (2*a) -\n      actualCorrelationPrimeField (2*a) :=\n  actualCorrelation_explicit_formula a\n\n-- A conditional RH implication does not provide its arithmetic premise.\nexample : RiemannHypothesis :=\n  riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower\n\nend Zeta23.OPICARound4.MadnessRejectedMutations\n\nnoncomputable section\nopen Set Complex Filter\nopen scoped Topology ComplexConjugate\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4\n\n-- CONTROL 1: an eventual common-cutoff theorem is not every-aperture negativity.\nexample (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :\n    ∀ L : ℝ, BothNeutralNegative L (originalDetectorQuarticCutoff L) := by\n  exact eventually_both_negative_at_original_quartic ρ hoff\n\n-- CONTROL 2: detector cutoff is not a selected, possibly smaller cutoff.\nexample (L : ℝ) (Kselected : ℕ)\n    (hK : Kselected ≤ originalDetectorQuarticCutoff L)\n    (hb : BothNeutralNegative L (originalDetectorQuarticCutoff L)) :\n    BothNeutralNegative L Kselected := by\n  exact hb\n\n-- CONTROL 3: fixed recentered negative form depth is not exponential-in-L depth.\nexample {σ a : ℝ} (hσ : σ=1 ∨ σ= -1) (ha : UniversalSinc.fixedScale < a)\n    (hn : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)\n      (fixedOriginalSincPhaseTrial σ a)).re < 0) :\n    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, ∃ hL : 2 ≤ L,\n      (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin\n        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)))\n        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith))).re < -Real.exp L := by\n  exact recentered_negative_phase_eventually_quartic hσ ha hn\n\n-- CONTROL 4: an own-newborn witness cannot be transferred to another cutoff.\nexample (p : ReversalParity) {L : ℝ} {hL : 0 < L} (Ke Ktarget : ℕ)\n    (s : NativeNewbornSourceWitness p L Ke hL) :\n    NativeNewbornSourceWitness p L Ktarget hL := by\n  exact s\n\n-- CONTROL 5: complement coercivity cannot drop ground orthogonality.\nexample (p : ReversalParity) {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness p L K hL) (lam : ℝ) (hlam : lam < 0)\n    (u : nativePoleNeutralParitySpace p L K) (hu0 : u ≠ 0)\n    (hu : nativePoleNeutralParityCanonical p L K u = (lam : ℂ) • u)\n    (x : nativePoleNeutralParitySpace p L K) :\n    0 ≤ (inner ℂ (nativePoleNeutralParityCanonical p L K x) x).re ∧\n      (-lam)*‖x‖^2 ≤ (inner ℂ\n        (nativePoleNeutralParityCanonical p L K x-(lam : ℂ) • x) x).re ∧\n      ‖x‖ ≤ ‖nativePoleNeutralParityCanonical p L K x-(lam : ℂ) • x‖/(-lam) := by\n  exact nativeNewborn_negative_eigen_complement_bounds p s lam hlam u hu0 hu x\n\n-- CONTROL 6: source positivity at the odd floor needs actual corrected source nonzero.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)\n    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK) :\n    0 < (star (poleNeutralCorrectedCubicSource L K u)*\n      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by\n  exact native_source_active_moment_pos_of_le_odd_bottom hL K hK lam u hu hle\n\n-- CONTROL 7: an even actual ground ray cannot stand in for the odd ground carrier.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (u : poleNeutralEvenSubspace L K) : poleNeutralOddSubspace L K := by\n  exact u\n-- NATIVE_GROUND_CONTROL: tied_response_missing_source_activity\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\n\n-- The strict positive interval cannot be obtained by omitting f(u) != 0.\nexample {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .odd L K hL)\n    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =\n      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u =\n      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u) :\n    0 < (star (poleNeutralCorrectedCubicSource L K u) *\n      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ∧\n    (star (poleNeutralCorrectedCubicSource L K u) *\n      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤\n      ‖poleNeutralCorrectedCubicSource L K u‖^2 * ‖poleNeutralCubicCompressionVector L K‖^2 /\n        (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) := by\n  exact actual_odd_newborn_tied_active_source_moment_bounds s htie u hu\n\n\n-- NATIVE_GROUND_CONTROL: tied_response_wrong_newborn_parity\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\n\n-- Even own-newborn data does not supply the odd own-predecessor gap.\nexample {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .even L K hL)\n    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =\n      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u =\n      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)\n    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :\n    0 < (star (poleNeutralCorrectedCubicSource L K u) *\n      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ∧\n    (star (poleNeutralCorrectedCubicSource L K u) *\n      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤\n      ‖poleNeutralCorrectedCubicSource L K u‖^2 * ‖poleNeutralCubicCompressionVector L K‖^2 /\n        (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) := by\n  exact actual_odd_newborn_tied_active_source_moment_bounds s htie u hu hf\n\n\n-- NATIVE_GROUND_CONTROL: spectral_visibility_missing_separation\nopen Zeta23.OPICARound4 Zeta23.OPICARound3 Zeta23.CCM\nnoncomputable section\n\nexample {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .even L K hL) (lam : ℝ) (hlam : lam < 0)\n    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)\n    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :\n    poleNeutralCubicPairingFunctional L K w ≠ 0 := by\n  exact (evenNewborn_odd_negative_eigen_channels_visible s lam hlam w hw0 hw).1\n\n\n-- NATIVE_GROUND_CONTROL: spectral_visibility_wrong_newborn_parity\nopen Zeta23.OPICARound4 Zeta23.OPICARound3 Zeta23.CCM\nnoncomputable section\n\nexample {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .odd L K hL) (lam : ℝ) (hlam : lam < 0)\n    (hne : lam ≠ poleNeutralEvenRayleighBottom L K hL s.cutoff_lower)\n    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)\n    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :\n    poleNeutralCubicPairingFunctional L K w ≠ 0 := by\n  exact (evenNewborn_odd_negative_eigen_channels_visible s lam hlam hne w hw0 hw).1\n\n\n-- NATIVE_GROUND_CONTROL: cubic_energy_wrong_newborn_parity\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\nexample\n    {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .even L K hL)\n    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =\n      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u =\n      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)\n    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :\n    0 ≤ (inner ℂ (poleNeutralOddCompressedCanonical L K\n      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re := by\n  exact actual_odd_newborn_tied_active_cubic_energy_nonneg s htie u hu hf\n\n\n-- NATIVE_GROUND_CONTROL: cubic_energy_missing_source_normalization\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\nexample\n    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)\n    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK)\n    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :\n    (‖poleNeutralCubicCompressionVector L K‖^2)^2 ≤\n      (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re *\n      ((inner ℂ (poleNeutralOddCompressedCanonical L K\n        (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re -\n        lam * ‖poleNeutralCubicCompressionVector L K‖^2) := by\n  exact actual_normalized_even_moment_cubic_energy_lower hL K hK lam u hu hle hf\n\n\n-- NATIVE_GROUND_CONTROL: silent_moment_missing_source_silence\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\nexample\n    {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .odd L K hL)\n    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =\n      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)\n    (u : poleNeutralEvenSubspace L K)\n    (hu : poleNeutralEvenCompressedCanonical L K u =\n      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)\n    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :\n    (-(inner ℂ (poleNeutralOddCompressedCanonical L K\n      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re) *\n      ‖poleNeutralIndexLinearMap hL K u‖^2 ≤\n    (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) *\n      ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)‖^2 := by\n  exact actual_odd_newborn_tied_silent_moment_depth_lower s htie u hu hf\n\n\n-- NATIVE_GROUND_CONTROL: silent_moment_zero_energy_promotion\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4\nexample\n    {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness .odd L K hL)\n    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =\n      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)\n    (hgneg : (inner ℂ (poleNeutralOddCompressedCanonical L K\n      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re = 0) :\n    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)\n      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) = 1 := by\n  exact actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple s htie hgneg\n\n\n-- NATIVE_GROUND_CONTROL: native_regularity_wrong_source_cell\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.RegularCells Set\nexample {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset (ReversalParity × ℕ)) {J : Set ℝ}\n    (ho : IsOpen J) (hn : J.Nonempty) (hc : J ⊆ fixedCanonicalCutoffCell (Q+1)) :\n    ∃ L ∈ J, ∀ i ∈ s, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2) := by\n  exact exists_finite_native_regular_in_open_fixedCell hQ s ho hn hc\n\n\n-- NATIVE_GROUND_CONTROL: native_regularity_missing_source_cell\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.RegularCells Set\nexample {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset (ReversalParity × ℕ)) {J : Set ℝ}\n    (ho : IsOpen J) (hn : J.Nonempty) (hc : J ⊆ Ioi 0) :\n    ∃ L ∈ J, ∀ i ∈ s, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2) := by\n  exact exists_finite_native_regular_in_open_fixedCell hQ s ho hn hc\n\n\n-- NATIVE_GROUND_CONTROL: regular_birth_wrong_predecessor_cutoff\n\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4.RegularCells\n\nexample {p : ReversalParity} {L : ℝ} {K : ℕ} {hL : 0 < L}\n    (s : NativeNewbornSourceWitness p L K hL)\n    (hwrong : Function.Bijective (nativePoleNeutralParityCanonical p L K)) : True := by\n  have h := native_newborn_realization_regular_of_bijective s hwrong\n  trivial\n\n\n-- NATIVE_GROUND_CONTROL: regular_birth_exists_to_forall_promotion\n\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound3 Zeta23.OPICARound4.RegularCells\n\nexample (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :\n    ∀ L : ℝ, R < L → ∀ (p : ReversalParity) (K : ℕ),\n      K ≤ originalDetectorQuarticCutoff L →\n        Function.Bijective (nativePoleNeutralParityCanonical p L K) := by\n  exact cofinally_both_negative_and_native_regular ρ hoff R\n\n\n-- Close preserved preceding anonymous sections before new isolated controls.\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\nend\n\n\n-- NONCOLLISION_CONTROL: WrongGram\nsection NoncollisionMutation01\nopen scoped BigOperators\nopen Zeta23.OPICARound4.NativeParitySeparation\n\n-- Removing the positive Gram from the pulled-back odd relation is not admissible.\nexample (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (hinj : Function.Injective a)\n    (lam : ℝ) (x z : Fin 3 → ℂ) (hx : x ≠ 0) (hz : z ≠ 0)\n    (hx0 : ∑ i, x i = 0) (hx1 : ∑ i, (a i : ℂ) * x i = 0)\n    (hz0 : ∑ i, z i = 0) (hz1 : ∑ i, (a i : ℂ) * z i = 0)\n    (c d e f : ℂ)\n    (hxE : ∀ i, ((a i : ℂ) - (lam : ℂ)) * x i = c + d * (a i : ℂ))\n    (hzO : ∀ i, ((a i : ℂ) - (lam : ℂ)) * z i = e + f * (a i : ℂ)) : False := by\n  exact diagonal_two_moment_compressions_disjoint a ha hinj lam x z hx hz\n    hx0 hx1 hz0 hz1 c d e f hxE hzO\nend NoncollisionMutation01\n\n-- NONCOLLISION_CONTROL: NonnegativeOnly\nsection NoncollisionMutation02\nopen scoped BigOperators\nopen Zeta23.OPICARound4.NativeParitySeparation\n\n-- Semidefiniteness does not discharge the strict positive diagonal hypothesis.\nexample (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) (hinj : Function.Injective a)\n    (lam : ℝ) (x z : Fin 3 → ℂ) (hx : x ≠ 0) (hz : z ≠ 0)\n    (hx0 : ∑ i, x i = 0) (hx1 : ∑ i, (a i : ℂ) * x i = 0)\n    (hz0 : ∑ i, z i = 0) (hz1 : ∑ i, (a i : ℂ) * z i = 0)\n    (c d e f : ℂ)\n    (hxE : ∀ i, ((a i : ℂ) - (lam : ℂ)) * x i = c + d * (a i : ℂ))\n    (hzO : ∀ i, (a i : ℂ) * ((a i : ℂ) - (lam : ℂ)) * z i = e + f * (a i : ℂ)) : False := by\n  exact diagonal_two_moment_compressions_disjoint a ha hinj lam x z hx hz\n    hx0 hx1 hz0 hz1 c d e f hxE hzO\nend NoncollisionMutation02\n\n-- NONCOLLISION_CONTROL: MissingNonzero\nsection NoncollisionMutation03\nopen Filter\nopen scoped Topology\nopen Zeta23.OPICARound4.NativeParitySeparation\nexample (K : ℕ) (hK : 3 ≤ K) :\n    ∀ᶠ theta in 𝓝 (0 : ℝ),\n      nativeWeightedSeparationDet K (nativeCosineWeights K theta) ≠ 0 := by\n  exact eventually_nativeCosine_separation K hK\nend NoncollisionMutation03\n\n-- NONCOLLISION_CONTROL: ArbitraryPhase\nsection NoncollisionMutation04\nopen Zeta23.OPICARound4.NativeParitySeparation\nexample (K : ℕ) (hK : 3 ≤ K) (epsilon : ℝ) (he : 0 < epsilon)\n    (theta : ℝ) (ht : 0 < theta) (hte : theta < epsilon) :\n    nativeWeightedSeparationDet K (nativeCosineWeights K theta) ≠ 0 := by\n  exact exists_nativeCosine_separation K hK epsilon he\nend NoncollisionMutation04\n\n-- NONCOLLISION_CONTROL: NegativeIdentityGram\nsection NoncollisionMutation05\nopen Zeta23.OPICARound4.NativeZeroFrame Zeta23.OPICARound4.RegularCells\nexample (K : ℕ) (u v : fixedEvenSeed K) :\n    inner ℂ (WithLp.toLp 2 (fixedSeedDiagonal 0 K u) : EuclideanSpace ℂ (Fin (2*K+1)))\n      (WithLp.toLp 2 (fixedSeedDiagonal 0 K v)) =\n        inner ℂ ((evenZeroEquiv K u).val) ((evenZeroEquiv K v).val) :=\n  zero_even_gram K u v\nend NoncollisionMutation05\n\n-- NONCOLLISION_CONTROL: NegativeParityMoments\nsection NoncollisionMutation06\nopen Zeta23.OPICARound4.NativeZeroFrame Zeta23.OPICARound4.RegularCells\nopen scoped BigOperators\nexample (K : ℕ) (x : Fin K → ℂ) : rawEvenLift K x ∈ fixedEvenSeed K ↔\n    (∑ i, x i / (i.val + 1 : ℂ) = 0) ∧ (∑ i, (i.val + 1 : ℂ) * x i = 0) :=\n  rawEvenLift_mem_iff K x\nend NoncollisionMutation06\n\n-- NONCOLLISION_CONTROL: NegativeSquareCutoff\nsection NoncollisionMutation07\nopen Zeta23.OPICARound4.PrimeIsolation\nexample {Q p q : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) (hq : q ≤ Q)\n    (hpp : IsPrimePow q) (hd : p ∣ q) : q = p :=\n  prime_pow_below_square_eq hp hpQ hq hpp hd\nend NoncollisionMutation07\n\n-- NONCOLLISION_CONTROL: NegativeAnchorSign\nsection NoncollisionMutation08\nopen Zeta23.OPICARound4.PrimeIsolation Zeta23.OPICARound4.PrimeSourceLaurent\nopen Zeta23.OPICARound4.RegularCells Zeta23.CCM\nexample (Q : ℕ) (s : Finset ℕ) (p : s) (hp : p.val.Prime) (hpQ : p.val ≤ Q)\n    (hQ : Q < p.val^2) (theta : ℝ) (K : ℕ) :\n    scaledFrozenPrimeMatrix Q 0 (fun q => formalPrimeMonomial s\n      (fun r => (q.factorization r.val : ℤ)) (singlePrimePhase s p (circlePhase theta))) K =\n      (isolatedPrimeCoefficient p.val : ℂ) •\n        (Matrix.diagonal (fun i : Fin (2*K+1) =>\n          (Real.cos ((centeredIndex K i : ℝ)*theta) : ℂ)) - 1) :=\n  neg_scaledFrozen_single_zero Q s p hp hpQ hQ theta K\nend NoncollisionMutation08\n\n-- NONCOLLISION_CONTROL: OmittedMultiplicity\nsection NoncollisionMutation09\nopen Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells\nopen scoped BigOperators\nexample (Q q : ℕ) (hq : q ≤ Q) (z : ℂ) :\n    integerPhase q z = formalPrimeMonomial (boundedPrimeSet Q) (fun _ => 1)\n      (primePhaseUnits (boundedPrimeSet Q) z) := by\n  exact (integerFormalPhase_actual Q q hq z).symm\nend NoncollisionMutation09\n\n-- NONCOLLISION_CONTROL: DroppedGram\nsection NoncollisionMutation10\nopen Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells\nopen Matrix\nopen scoped BigOperators\nexample {ι κ : Type*} [Fintype ι] [Fintype κ] (Q K : ℕ)\n    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)\n    (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) (V : Matrix κ ι ℂ) (i : κ) (j : ι) :\n    (formalRawFrameSylvester Q K Ce Co z X *ᵥ (fun ij => V ij.1 ij.2)) (i,j) =\n      (formalRawFrameEnergy Q K Co z X * V - V * formalRawFrameEnergy Q K Ce z X) i j := by\n  exact formalRawFrameSylvester_mulVec Q K Ce Co z X V i j\nend NoncollisionMutation10\n\n-- NONCOLLISION_CONTROL: SingularAffine\nsection NoncollisionMutation11\nopen Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells\nopen scoped BigOperators\nexample (Q K : ℕ) (z : ℂ) (hz : z = 0) (X : boundedPrimeSet Q → ℂˣ) :\n    formalScaledSourceMatrix Q z X K =\n      z • (formalWFreeSourceMatrix Q z X K + primeCommonScalar Q z • 1) := by\n  exact formalScaledSourceMatrix_eq Q K hz X\nend NoncollisionMutation11\n\n-- NONCOLLISION_CONTROL: NegativeZeroAnchor\nsection NoncollisionMutation12\nnoncomputable section\nopen Zeta23.OPICARound4.PrimeSourceGerms Zeta23.OPICARound4.PrimeSourceLaurent\nopen Zeta23.OPICARound4.RegularCells Filter\nopen scoped Topology\nexample (Q K : ℕ) (Ce Co : Matrix (Fin (2*K+1)) (Fin 1) ℂ)\n    (X : boundedPrimeSet Q → ℂˣ)\n    (h0 : (formalRawFrameSylvester Q K Ce Co 0 X).det = 0) :\n    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),\n      (formalRawFrameSylvester Q K Ce Co z (primePhaseUnits (boundedPrimeSet Q) z)).det = 0 := by\n  exact actual_sylvester_germ_nonzero_of_formal_anchor Q K Ce Co X h0\nend\nend NoncollisionMutation12\n\n-- NONCOLLISION_CONTROL: NegativeVariablePhaseExampleDirect\nsection NoncollisionMutation13\nnoncomputable section\nopen Zeta23.OPICARound4.PrimeSourceGerms Zeta23.OPICARound4.PrimeSourceLaurent\nopen Zeta23.CCM\n\nexample (Q K : ℕ) (Ce Co : Matrix (Fin (2*K+1)) (Fin 1) ℂ)\n    (X : ℂ → boundedPrimeSet Q → ℂˣ) : True := by\n  have h := analyticAt_formalRawFrameSylvesterDet (ι := Fin 1) (κ := Fin 1)\n    Q K Ce Co X (z := 0) (by simp)\n  trivial\nend\nend NoncollisionMutation13\n\n-- NONCOLLISION_CONTROL: DroppedZeroGram\nsection NoncollisionMutation14\nopen Zeta23.CCM Zeta23.OPICARound4.NativeParityPencils\nnoncomputable section\nexample (K : ℕ) : frameGram .even K 0 = LinearMap.id := by\n  exact frameGram_zero .even K\nend\nend NoncollisionMutation14\n\n-- NONCOLLISION_CONTROL: DroppedPhysicalScale\nsection NoncollisionMutation15\nopen Zeta23.CCM Zeta23.OPICARound4.NativeParityPencils\nnoncomputable section\nexample (p : ReversalParity) {L : ℝ} (hL : 0 < L) (Q K : ℕ)\n    (hQ : ⌊Real.exp L⌋₊ = Q) (mu : ℂ) (u : zeroCarrier p K) :\n    frameEnergy p K L (scaledPhysicalSource Q K L) u =\n        (mu + physicalCommonShift Q L) • frameGram p K L u ↔\n      nativePoleNeutralParityCanonical p L K (physicalEquiv p hL K u) =\n        mu • physicalEquiv p hL K u := by\n  exact physical_pencil_eigen_iff p hL Q K hQ mu u\nend\nend NoncollisionMutation15\n\n-- NONCOLLISION_CONTROL: NegativeNoPrimeHorizon\nsection NoncollisionMutation16\nopen Zeta23.OPICARound4.NativeParityPencils Zeta23.OPICARound4.PrimeSourceLaurent Filter\nopen scoped Topology\nexample : ∀ Q K : ℕ, 3 ≤ K →\n    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), nativeActualSeparationDet Q K z = 0 :=\n  nativeActualSeparationDet_germ_nonzero\nend NoncollisionMutation16\n\n-- NONCOLLISION_CONTROL: NegativeEveryAperture\nsection NoncollisionMutation17\nopen Zeta23.OPICARound4.NativeParityPencils\nexample (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :\n    ∀ L : ℝ, 0 < L → nativeActualSeparationDet Q K (L : ℂ) ≠ 0 :=\n  exists_nativeActualSeparationDet_nonzero_in_open_positive Q K hQ hK\nend NoncollisionMutation17\n\n-- NONCOLLISION_CONTROL: NegativeUniformMargin\nsection NoncollisionMutation18\nopen Zeta23.OPICARound4.NativeParityPencils Zeta23.OPICARound4.PrimeSourceLaurent\nexample (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :\n    ∃ X : boundedPrimeSet Q → ℂˣ, 1 ≤ ‖nativeFormalSeparationDet Q K 0 X‖ :=\n  exists_native_formal_separation_anchor Q K hQ hK\nend NoncollisionMutation18\n\n-- NONCOLLISION_CONTROL: NegativeRegularityAsSeparation\nsection NoncollisionMutation19\nopen Zeta23.OPICARound4 Zeta23.CCM Module.End\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hreg : Function.Bijective (poleNeutralEvenCompressedCanonical L K) ∧\n      Function.Bijective (poleNeutralOddCompressedCanonical L K))\n    (mu : ℂ) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)\n    (hu : poleNeutralEvenCompressedCanonical L K u = mu • u) :\n    poleNeutralCorrectedCubicSource L K u ≠ 0 :=\n  (separated_native_even_eigen_channels_visible hL K hK hreg mu u hu0 hu).1\nend NoncollisionMutation19\n\n-- NONCOLLISION_CONTROL: NegativeSourcePositiveFromVisible\nsection NoncollisionMutation20\nopen Zeta23.OPICARound4 Zeta23.CCM Module.End\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hsep : ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →\n      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu)\n    (mu : ℂ) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)\n    (hu : poleNeutralEvenCompressedCanonical L K u = mu • u) :\n    0 < (poleNeutralCorrectedCubicSource L K u).re :=\n  (separated_native_even_eigen_channels_visible hL K hK hsep mu u hu0 hu).1\nend NoncollisionMutation20\n\n-- NONCOLLISION_CONTROL: DroppedFiniteCap\nsection NoncollisionMutation21\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.RegularCells\nexample (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)\n    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :\n    ∃ out : GeneratedStep123Output ρ β p R,\n      ∀ q K, Function.Bijective (nativePoleNeutralParityCanonical q\n        (fixedOriginalSincTrialAperture out.sourceData.separation) K) := by\n  obtain ⟨out,h⟩ := exists_actual_generated_packet_native_regular ρ hβ hβρ p R\n  exact ⟨out,fun q K => h q K⟩\nend\nend NoncollisionMutation21\n\n-- NONCOLLISION_CONTROL: AllPacketsRegular\nsection NoncollisionMutation22\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.RegularCells\nexample (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)\n    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :\n    ∀ out : GeneratedStep123Output ρ β p R,\n      ∀ q K, K ≤ originalDetectorQuarticCutoff\n        (fixedOriginalSincTrialAperture out.sourceData.separation) →\n        Function.Bijective (nativePoleNeutralParityCanonical q\n          (fixedOriginalSincTrialAperture out.sourceData.separation) K) := by\n  exact exists_actual_generated_packet_native_regular ρ hβ hβρ p R\nend\nend NoncollisionMutation22\n\n-- NONCOLLISION_CONTROL: ChangedOriginalPhase\nsection NoncollisionMutation23\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.RegularCells\nexample (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)\n    (hβρ : β < |(ρ : ℂ).re - 1/2|) (R : ℝ) :\n    Nonempty (GeneratedStep123Output ρ β .odd R) := by\n  obtain ⟨out,h⟩ := exists_actual_generated_packet_native_regular ρ hβ hβρ .even R\n  exact ⟨out⟩\nend\nend NoncollisionMutation23\n\n-- NONCOLLISION_CONTROL: ChangedSourceHorizon\nsection NoncollisionMutation24\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.NativeParityPencils\n-- Keep the literal source-horizon head visible instead of expanding the complete determinant.\nattribute [local irreducible] nativeActualSeparationDet\nexample (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)\n    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) (Q : ℕ) :\n    ∃ out : GeneratedStep123Output ρ β p R,\n      let L := fixedOriginalSincTrialAperture out.sourceData.separation\n      ∀ K, 3 ≤ K → K ≤ originalDetectorQuarticCutoff L →\n        nativeActualSeparationDet Q K (L : ℂ) ≠ 0 := by\n  obtain ⟨out,hreg,hsep⟩ := exists_actual_generated_packet_regular_separationDet ρ hβ hβρ p R\n  refine ⟨out,?_⟩\n  dsimp only\n  intro K hK hcap\n  exact hsep K hK hcap\nend\nend NoncollisionMutation24\n\n-- NONCOLLISION_CONTROL: ClaimedUniformMargin\nsection NoncollisionMutation25\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.NativeParityPencils\nexample (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)\n    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :\n    ∃ out : GeneratedStep123Output ρ β p R,\n      let L := fixedOriginalSincTrialAperture out.sourceData.separation\n      ∀ K, 3 ≤ K → K ≤ originalDetectorQuarticCutoff L →\n        1 ≤ ‖nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ)‖ := by\n  obtain ⟨out,hreg,hsep⟩ := exists_actual_generated_packet_regular_separationDet ρ hβ hβρ p R\n  refine ⟨out,?_⟩\n  dsimp only\n  intro K hK hcap\n  exact hsep K hK hcap\nend\nend NoncollisionMutation25\n\n-- NONCOLLISION_CONTROL: MissingGram\nsection NoncollisionMutation26\nopen Zeta23.OPICARound4.NativeParityPencils Zeta23.OPICARound4.NativeParitySeparation Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells Zeta23.CCM\nattribute [local irreducible] nativePencilSylvester nativeSylvester frameEnergy frameGram\nexample (Q K : ℕ) (z : ℂ) (X : boundedPrimeSet Q → ℂˣ)\n    (hd : (formalRawFrameSylvester Q K (coordinateFrame .even K)\n      (coordinateFrame .odd K) z X).det ≠ 0) :\n    Function.Injective (nativeSylvester\n      (E := zeroCarrier .even K) (F := zeroCarrier .odd K)\n      (frameEnergy .even K z (formalScaledSourceMatrix Q z X K))\n      (frameEnergy .odd K z (formalScaledSourceMatrix Q z X K))) := by\n  exact (coordinateFrame_sylvester_det_iff Q K z X).mp hd\nend NoncollisionMutation26\n\n-- NONCOLLISION_CONTROL: WrongSourceCell\nsection NoncollisionMutation27\nopen Zeta23.OPICARound4.NativeParityPencils Zeta23.OPICARound4.NativeParitySeparation Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells Zeta23.CCM\nexample {L : ℝ} (hL : 0 < L)\n    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q+1) :\n    (formalRawFrameSylvester Q K (coordinateFrame .even K)\n      (coordinateFrame .odd K) L (primePhaseUnits (boundedPrimeSet Q) L)).det ≠ 0 ↔\n    ∀ mu : ℂ, Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .even L K) mu →\n      ¬ Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) mu := by\n  exact coordinateFrame_physical_det_iff_disjoint hL Q K hQ\nend NoncollisionMutation27\n\n-- NONCOLLISION_CONTROL: ZeroAperture\nsection NoncollisionMutation28\nopen Zeta23.OPICARound4.NativeParityPencils Zeta23.OPICARound4.NativeParitySeparation Zeta23.OPICARound4.PrimeSourceLaurent Zeta23.OPICARound4.RegularCells Zeta23.CCM\nexample {L : ℝ} (hL : L = 0)\n    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) :\n    (formalRawFrameSylvester Q K (coordinateFrame .even K)\n      (coordinateFrame .odd K) L (primePhaseUnits (boundedPrimeSet Q) L)).det ≠ 0 ↔\n    ∀ mu : ℂ, Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .even L K) mu →\n      ¬ Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) mu := by\n  exact coordinateFrame_physical_det_iff_disjoint hL Q K hQ\nend NoncollisionMutation28\n\n-- Moment-margin controls: retain the preceding 80 examples verbatim.\n\nsection MomentMarginMutation1\nnoncomputable section\nopen Set Complex MeasureTheory Filter\nopen scoped Topology\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\nexample {σ L c : ℝ} (hσ : σ=1 ∨ σ= -1) (hL : 0<L)\n    (hleft : 1+UniversalSinc.fixedScale≤c)\n    (hright : c+UniversalSinc.fixedScale≤L-1) :\n    (∫ x in (0:ℝ)..L, ‖recenteredSmoothPhase σ L c x‖^2)=1 := by\n  exact recenteredSmoothPhase_interval_energy_eq_one hσ hL hleft hleft hright\nend\nend MomentMarginMutation1\n\nsection MomentMarginMutation2\nnoncomputable section\nopen Set Complex MeasureTheory Filter\nopen scoped Topology\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\nexample {σ L c : ℝ} (hL : 2≤L) (hσ : σ=1 ∨ σ= -1)\n    (ha : UniversalSinc.fixedScale<L/2-c)\n    (hleft : 1+UniversalSinc.fixedScale≤c)\n    (hright : c+UniversalSinc.fixedScale≤L-1) :\n    |‖originalDetectorFinitePhaseVector σ L c (by linarith)‖^2-1| ≤\n      originalDetectorFinitePhaseMassErrorBudget σ L := by\n  exact recenteredFinitePhase_mass_error_le hL hσ ha hleft hright\nend\nend MomentMarginMutation2\n\nsection MomentMarginMutation3\nnoncomputable section\nopen Set Complex Filter\nopen scoped Topology\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4\nexample\n    (ρ : zetaZeroConfig.carrier) :\n    ∀ᶠ L : ℝ in atTop, ∃ hL : 2 ≤ L,\n      (∃ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),\n        centeredMoment (originalDetectorQuarticCutoff L) 4\n          ((EuclideanSpace.equiv _ ℂ) u.val.val) = 0 ∧\n        (inner ℂ (poleNeutralEvenCompressedCanonical L\n          (originalDetectorQuarticCutoff L) u) u).re < 0) ∧\n      (∃ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),\n        centeredMoment (originalDetectorQuarticCutoff L) 3\n          ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 ∧\n        centeredMoment (originalDetectorQuarticCutoff L) 5\n          ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 ∧\n        (inner ℂ (poleNeutralOddCompressedCanonical L\n          (originalDetectorQuarticCutoff L) v) v).re < 0) := by\n  exact eventually_both_negative_moment_slices_at_original_quartic ρ\nend\nend MomentMarginMutation3\n\nsection MomentMarginMutation4\nnoncomputable section\nopen Set Complex Filter\nopen scoped Topology\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4\nexample (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :\n    centeredMoment (originalDetectorQuarticCutoff L) 6\n      ((EuclideanSpace.equiv _ ℂ)\n        ((originalDetectorFiniteEvenPhase c hL).val.val)) = 0 := by\n  exact originalDetectorFiniteEvenPhase_moment_four c hL\nend\nend MomentMarginMutation4\n'
FRONTIER_SEMANTIC_MUTATION_IMPORTS = 'import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices\nimport Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates\nimport Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure\nimport Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketClosure\nimport Zeta23.OPICARound4.ArithmeticFrontier.PhysicalBlockCertificate\nimport Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnCore\nimport Zeta23.OPICARound4.ArithmeticFrontier.Validation.Carriers\nimport Zeta23.OPICARound4.ArithmeticFrontier.PoleChannel\nimport Zeta23.OPICARound4.ArithmeticFrontier.MomentLeakage\nimport Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness\nimport Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnTrace\nimport Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure\nimport Zeta23.OPICARound4.ArithmeticFrontier.CofinalSemiboundedClosure\nimport Zeta23.OPICARound4.ArithmeticFrontier.C2GrowthClosure\nimport Zeta23.OPICARound4.ArithmeticFrontier.NativeMomentDisplacement\nimport Zeta23.OPICARound4.ArithmeticFrontier.NativeLeakageFactor\nimport Zeta23.OPICARound4.ArithmeticFrontier.GeometryReconstruction\nimport Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor\n'
FRONTIER_SEMANTIC_MUTATIONS = "\nsection FrontierMutation1\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A positive trial vector is not an all-vector bound on the whole slice.\nexample {L : ℝ} {K : ℕ} {ε : ℝ}\n    (h : ∃ u : poleNeutralEvenSubspace L K, u ∈ evenMomentSlice L K ∧ u ≠ 0 ∧\n      -ε * ‖u‖ ^ 2 ≤ evenNativeEnergy L K u) :\n    EvenMomentSliceLowerBound L K ε := h\nend\nend FrontierMutation1\n\nsection FrontierMutation2\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A smaller cutoff is not the literal quartic detector cutoff.\nexample {L ε : ℝ} {K : ℕ} (hK : K < originalDetectorQuarticCutoff L)\n    (h : EvenMomentSliceLowerBound L K ε) :\n    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) ε := h\nend\nend FrontierMutation2\n\nsection FrontierMutation3\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The vacuous K = 3 slice bound cannot stand in for the nonzero quartic slice.\nexample {L ε : ℝ} (hL : 0 < L) :\n    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) ε :=\n  evenMomentSliceLowerBound_three hL ε\nend\nend FrontierMutation3\n\nsection FrontierMutation4\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- Slice membership of a source trial is not a ground eigenvector equation.\nexample {L : ℝ} {K : ℕ} (u : poleNeutralEvenSubspace L K) (μ : ℂ)\n    (hu : u ∈ evenMomentSlice L K) :\n    poleNeutralEvenCompressedCanonical L K u = μ • u := hu\nend\nend FrontierMutation4\n\nsection FrontierMutation5\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- An even slice bound does not cover the odd slice.\nexample {L ε : ℝ} {K : ℕ} (h : EvenMomentSliceLowerBound L K ε) :\n    OddMomentSliceLowerBound L K ε := h\nend\nend FrontierMutation5\n\nsection FrontierMutation6\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A coordinate-identity tolerance is not the same physical tolerance.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) {ε : ℝ} (hε : 0 ≤ ε)\n    (h : ∀ y : fixedEvenMomentSeed K, -ε * seedCoordinateNormSq K y ≤\n      evenNativeEnergy L K\n        ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K)) :\n    EvenMomentSliceLowerBound L K ε :=\n  evenMomentSliceLowerBound_of_coordinate_tolerance hL K hε h\nend\nend FrontierMutation6\n\nsection FrontierMutation7\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- One fixed tolerance is not the vanishing-error contract (C1).\nexample (h : ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧\n      MomentSliceLowerBound L (originalDetectorQuarticCutoff L) ε) :\n    CofinalMomentSliceVanishingErrorBounds := h\nend\nend FrontierMutation7\n\nsection FrontierMutation8\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- Bounded apertures do not escape to infinity.\nexample (h : ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, 2 ≤ L ∧\n      MomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1 / (n : ℝ))) :\n    CofinalMomentSliceVanishingErrorBounds := h\nend\nend FrontierMutation8\n\nsection FrontierMutation9\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- No tie exclusion follows at a state without spectral disjointness.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :\n    poleNeutralEvenRayleighBottom L K hL hK ≠ poleNeutralOddRayleighBottom L K hL hK :=\n  rayleighBottoms_ne_of_spectra_disjoint hL K hK\nend\nend FrontierMutation9\n\nsection FrontierMutation10\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The packet consumer still needs the ground-response restriction itself.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (hsep : NativeSpectraDisjoint L K) :\n    ¬ Zeta23.OPICARound3.BothNeutralNegative L K :=\n  noBothNeg_of_ground_response_and_disjoint_spectra hL K hK hsep\nend\nend FrontierMutation10\n\nsection FrontierMutation11\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier\n-- The inverse residual cannot be dropped from the coupled certificate.\nexample {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]\n    [NormedAddCommGroup F] [InnerProductSpace ℂ F]\n    (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F) (A : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F)\n    {a : ℝ} (ha : 0 < a)\n    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))\n    (hApos : ∀ z : F, a * ‖z‖ ^ 2 ≤ (inner ℂ (A z) z).re)\n    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u))\n    (hcert : ∀ u : E, 0 ≤ correctedSchurForm D C A X u) (u : E) (w : F) :\n    0 ≤ blockEnergy D C A u w :=\n  blockEnergy_nonneg_of_inverse_residual_certificate D C Cadj A X ha hA hApos hC hcert u w\nend\nend FrontierMutation11\n\nsection FrontierMutation12\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier\n-- The core margin must be strictly better than the claimed physical shift.\nexample {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]\n    (H : E →ₗ[ℂ] E) (S : Submodule ℂ E) [S.HasOrthogonalProjection]\n    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) {ε η : ℝ}\n    (hη : 0 ≤ η) (hηε : η ≤ ε / 4) (hleak : CoreLeakageBound H S η)\n    (hcore : ∀ p ∈ S, -ε * ‖p‖ ^ 2 ≤ (inner ℂ (H p) p).re) :\n    ∀ v : E, -ε * ‖v‖ ^ 2 ≤ (inner ℂ (H v) v).re :=\n  core_shift_certificate H S hH hη hηε hleak hcore\nend\nend FrontierMutation12\n\nsection FrontierMutation13\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- Pole annihilation needs pole neutrality: a boundary-flat vector alone does not suffice.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (u : euclideanEvenBoundaryFlatSubspace K) :\n    canonicalPoleMatrix L K *ᵥ evenBoundaryFlatRawCoefficients K u = 0 :=\n  canonicalPoleMatrix_mulVec_poleNeutralEven_eq_zero hL K u\nend\nend FrontierMutation13\n\nsection FrontierMutation14\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The energy identity is not available at a nonpositive aperture.\nexample {L : ℝ} (hL : L ≤ 0) (K : ℕ) (u : poleNeutralEvenSubspace L K) :\n    evenNativeEnergy L K u =\n      -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))\n          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re -\n        (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))\n          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re :=\n  evenNativeEnergy_eq_neg_arch_sub_prime hL K u\nend\nend FrontierMutation14\n\nsection FrontierMutation15\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The leakage terms cannot be dropped from the compressed commutator.\nexample {N k r : Type*} [Fintype N] [DecidableEq N] [Fintype k] [Fintype r]\n    (V : Matrix N k \u2102) (D\u2080 E : Matrix N N \u2102) (W : Matrix N r \u2102) (L : Matrix k r \u2102)\n    (hD : D\u2080\u1d34 = D\u2080) (hE : E\u1d34 = E) (hleak : (1 - V * V\u1d34) * D\u2080 * V = W * L\u1d34) :\n    (V\u1d34 * D\u2080 * V) * (V\u1d34 * E * V) - (V\u1d34 * E * V) * (V\u1d34 * D\u2080 * V) = V\u1d34 * (D\u2080 * E - E * D\u2080) * V :=\n  compressed_commutator_eq V D\u2080 E W L hD hE hleak\nend\nend FrontierMutation15\n\nsection FrontierMutation16\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The shifted-factor certificate needs a strictly positive shift.\nexample {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A : Matrix n n \u211d) (R : Matrix n m \u211d) {\u03c4 : \u211d}\n    (h\u03c4 : 0 \u2264 \u03c4) (hfro : FiniteCertificateSoundness.froSq (A - \u03c4 \u2022 (1 : Matrix n n \u211d) - R * R\u1d40) < \u03c4 ^ 2)\n    {x : n \u2192 \u211d} (hx : x \u2260 0) : 0 < FiniteCertificateSoundness.quad A x :=\n  FiniteCertificateSoundness.posDef_of_shifted_factor A R h\u03c4 hfro hx\nend\nend FrontierMutation16\n\nsection FrontierMutation17\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The discarded-sector trace identity needs a self-adjoint source, not a symmetric one.\nexample {N k : Type*} [Fintype N] [DecidableEq N] [Fintype k] [DecidableEq k]\n    (H : Matrix N N \u2102) (S : Matrix N k \u2102) (hH : H\u1d40 = H) (hG : IsUnit ((H * S)\u1d34 * (H * S)).det) :\n    trace (((1 - (H * S) * ((H * S)\u1d34 * (H * S))\u207b\u00b9 * (H * S)\u1d34) * H)\u1d34 *\n        ((1 - (H * S) * ((H * S)\u1d34 * (H * S))\u207b\u00b9 * (H * S)\u1d34) * H))\n      = trace (H * H) - trace (((H * S)\u1d34 * (H * S))\u207b\u00b9 * (S\u1d34 * (H * H * H * H) * S)) :=\n  sourceColumn_residual_trace H S hH hG\nend\nend FrontierMutation17\n\nsection FrontierMutation18\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A constant chosen separately at each aperture is not the polynomial contract (PG).\nexample (h : \u2200 L : \u211d, \u2203 C : \u211d, 0 < C \u2227\n      EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ 2)) :\n    RiemannHypothesis :=\n  riemannHypothesis_of_fixed_parity_polynomial h\nend\nend FrontierMutation18\n\nsection FrontierMutation19\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- Cofinal coverage is not the all-late subexponential contract (SE).\nexample (h : \u2200 \u03b1 : \u211d, 0 < \u03b1 \u2192 \u2203 C : \u211d, 0 < C \u2227 \u2200 R : \u211d, \u2203 L : \u211d, R < L \u2227\n      EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * Real.exp (\u03b1 * L))) :\n    RiemannHypothesis :=\n  riemannHypothesis_of_fixed_parity_subexponential h\nend\nend FrontierMutation19\n\nsection FrontierMutation20\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- One positive rate bounds the displacement; it does not put the zero on the line.\nexample (h : EvenFixedRateMomentSliceBound 1) (\u03c1 : Zeta23.zetaZeroConfig.carrier) :\n    (\u03c1 : \u2102).re = 1 / 2 :=\n  abs_re_sub_half_le_of_even_fixed_rate zero_le_one h \u03c1\nend\nend FrontierMutation20\n\nsection FrontierMutation21\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A parity chosen after the vector is not the semibounded contract (SB).\nexample (h : \u2203 C : \u211d, 0 \u2264 C \u2227 \u2200 R : \u211d, \u2203 L : \u211d, max R 2 < L \u2227\n      \u2200 u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),\n      \u2200 v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),\n        (u \u2208 evenMomentSlice L (originalDetectorQuarticCutoff L) \u2192\n          -C * \u2016u\u2016 ^ 2 \u2264 evenNativeEnergy L (originalDetectorQuarticCutoff L) u) \u2228\n        (v \u2208 oddMomentSlice L (originalDetectorQuarticCutoff L) \u2192\n          -C * \u2016v\u2016 ^ 2 \u2264 oddNativeEnergy L (originalDetectorQuarticCutoff L) v)) :\n    RiemannHypothesis :=\n  riemannHypothesis_of_cofinal_moment_slice_semibounded h\nend\nend FrontierMutation21\n\nsection FrontierMutation22\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The all-late witnesses have a fixed depth M, not exponential depth at every aperture.\nexample (\u03c1 : Zeta23.zetaZeroConfig.carrier) (hoff : (\u03c1 : \u2102).re \u2260 1 / 2) :\n    \u2200\u1da0 L : \u211d in Filter.atTop, \u2203 u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),\n      u \u2208 evenMomentSlice L (originalDetectorQuarticCutoff L) \u2227 \u2016u\u2016 = 1 \u2227\n      evenNativeEnergy L (originalDetectorQuarticCutoff L) u \u2264 -Real.exp L :=\n  eventually_both_moment_slices_below \u03c1 hoff 1\nend\nend FrontierMutation22\n\nsection FrontierMutation23\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A long-term rate \u03b1 in t = 2a is a correlation rate 2\u03b1 in a, not \u03b1.\nexample {\u03b1 : \u211d} (h\u03b1 : 0 \u2264 \u03b1) (h : ActualLongTermFixedRateLowerBound \u03b1) :\n    \u2203 K A : \u211d, 0 < K \u2227 0 \u2264 A \u2227 \u2200 a : \u211d, A \u2264 a \u2192\n      -(K * Real.exp (\u03b1 * a)) \u2264 Zeta23.ExceptionalZero.fixedOriginalSincCorrelationReal a :=\n  correlation_lower_of_longTerm_fixed_rate h\u03b1 h\nend\nend FrontierMutation23\n\nsection FrontierMutation24\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The ambient commutator cancels only on boundary-flat columns.\nexample {L : \u211d} (hL : 0 < L) (N : \u2115) (V : Matrix (Fin (2 * N + 1)) (Fin 1) \u2102) :\n    V\u1d34 * (squaredIndexMatrix N * canonicalSourceMatrix L N -\n      canonicalSourceMatrix L N * squaredIndexMatrix N) * V = 0 :=\n  compressed_squaredIndex_commutator_eq_zero hL N V\nend\nend FrontierMutation24\n\nsection FrontierMutation25\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The squared-index geometry does not preserve the even slice: its leakage is M\u2086(u).\nexample {L : \u211d} (hL : 0 < L) (K : \u2115) {u : Fin (2 * K + 1) \u2192 \u2102}\n    (hu : u \u2208 evenBoundaryFlatSubspace K) (hpole : \u2211 i, poleEvenProfile L K i * u i = 0)\n    (h4 : centeredMoment K 4 u = 0) :\n    centeredMoment K 4 (squaredIndexMatrix K *\u1d65 u) = 0 :=\n  (squaredIndex_mulVec_even_slice_leakage hL K hu hpole h4).2.2\nend\nend FrontierMutation25\n\nsection FrontierMutation26\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The even leakage coefficient is the sixth moment M\u2086, not M\u2084 (which vanishes on the slice).\nexample {L : \u211d} (hL : 0 < L) (K : \u2115) {u : EuclideanSpace \u2102 (Fin (2 * K + 1))}\n    (hu : u \u2208 evenSliceAmb L K) :\n    squaredIndexOp K u - (evenSliceAmb L K).starProjection (squaredIndexOp K u) =\n      (centeredMoment K 4 (WithLp.ofLp u) / ((\u2016evenLeakageVec L K\u2016 : \u2102) ^ 2)) \u2022\n        evenLeakageVec L K :=\n  even_slice_rank_one_leakage hL K hu\nend\nend FrontierMutation26\n\nsection FrontierMutation27\nnoncomputable section\nopen Zeta23.OPICARound4.ArithmeticFrontier Matrix\n-- The reconstruction floor pays 2 n_z n_\u2113 / g, not n_z n_\u2113 / g.\nexample {n : \u2115} (H : Matrix (Fin n) (Fin n) \u2102) (\u03b8 : Fin n \u2192 \u211d) (z \u2113 : Fin n \u2192 \u2102)\n    {g h\u2080 nz nl : \u211d} (hg : 0 < g) (hgap : \u2200 i j, i \u2260 j \u2192 g \u2264 |\u03b8 i - \u03b8 j|)\n    (hcomm : \u2200 i j, i \u2260 j \u2192 ((\u03b8 i : \u2102) - \u03b8 j) * H i j = z i * star (\u2113 j) - \u2113 i * star (z j))\n    (hdiag : \u2200 i, h\u2080 \u2264 (H i i).re) (hnz : 0 \u2264 nz) (hnl : 0 \u2264 nl)\n    (hz : \u2211 i, \u2016z i\u2016 ^ 2 \u2264 nz ^ 2) (hl : \u2211 i, \u2016\u2113 i\u2016 ^ 2 \u2264 nl ^ 2) (x : Fin n \u2192 \u2102) :\n    (h\u2080 - nz * nl / g) * \u2211 i, \u2016x i\u2016 ^ 2 \u2264 (star x \u2b1d\u1d65 (H *\u1d65 x)).re :=\n  reconstruction_lower_bound H \u03b8 z \u2113 hg hgap hcomm hdiag hnz hnl hz hl x\nend\nend FrontierMutation27\n\nsection FrontierMutation28\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A geometry-response certificate gives the slice bound at its own floor, not at floor zero.\nexample {L : \u211d} (hL : 0 < L) {K : \u2115} {m : \u211d} (h : EvenGeometryResponseCertificate L K m) :\n    EvenMomentSliceLowerBound L K 0 :=\n  evenMomentSliceLowerBound_of_certificate hL h\nend\nend FrontierMutation28\n\nsection FrontierMutation29\nnoncomputable section\nopen Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- Cofinal geometry certificates are not the all-late (SG) contract.\nexample (h : \u2203 (C : \u211d) (d : \u2115), 0 < C \u2227 \u2200 R : \u211d, \u2203 L : \u211d, R < L \u2227\n      EvenGeometryResponseCertificate L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ d)) :\n    FixedParityGeometryResponsePolynomial :=\n  h\nend\nend FrontierMutation29\n\nsection FrontierMutation30\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A strip of half-width a costs exp (a L) on a native carrier, not exp (a L / 2).\nexample {a L : \u211d} (hL : 0 < L)\n    (hstrip : \u2200 \u03c1 \u2208 zetaZeroConfig.carrier, |\u03c1.re - 1 / 2| \u2264 a) (K : \u2115)\n    (x : EuclideanSpace \u2102 (Fin (2 * K + 1)))\n    (hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) \u2102) x)) :\n    -(zetaZeroInvSqWeight * Real.exp (a * L / 2) * nativeFloorBudget L K) * \u2016x\u2016 ^ 2 \u2264\n      (inner \u2102 ((canonicalSourceMatrix L K).toEuclideanLin x) x).re :=\n  canonicalSource_re_inner_ge_neg_of_zeroStrip hL hstrip K x hflat\nend\nend FrontierMutation30\n\nsection FrontierMutation31\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A strip of half-width a gives every rate above a, not the rate a itself.\nexample {a : \u211d} (hstrip : \u2200 \u03c1 \u2208 zetaZeroConfig.carrier, |\u03c1.re - 1 / 2| \u2264 a) :\n    EvenFixedRateMomentSliceBound a :=\n  evenFixedRateMomentSliceBound_of_zeroStrip (le_refl a) hstrip\nend\nend FrontierMutation31\n\nsection FrontierMutation32\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- A half-plane Re \u03c1 \u2264 \u03b8 gives the rates above \u03b8 - 1/2, not the rates above \u03b8 - 1.\nexample {\u03b8 \u03b1 : \u211d} (h\u03b8 : \u2200 \u03c1 \u2208 zetaZeroConfig.carrier, \u03c1.re \u2264 \u03b8) (h\u03b1 : \u03b8 - 1 < \u03b1) :\n    EvenFixedRateMomentSliceBound \u03b1 \u2227 OddFixedRateMomentSliceBound \u03b1 :=\n  fixedRateMomentSliceBounds_of_re_le h\u03b8 h\u03b1\nend\nend FrontierMutation32\n\nsection FrontierMutation33\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The unconditional rates are those above 1/2; nothing here gives every positive rate.\nexample {\u03b1 : \u211d} (h\u03b1 : 0 < \u03b1) :\n    EvenFixedRateMomentSliceBound \u03b1 \u2227 OddFixedRateMomentSliceBound \u03b1 :=\n  fixedRateMomentSliceBounds_of_half_lt h\u03b1\nend\nend FrontierMutation33\n\nsection FrontierMutation34\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- The cutoff-3 bottom must lie below -D/2, beyond every admissible eta; below -D/3 is not enough.\nexample {L : \u211d} {Kd : \u2115} {D : \u211d} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)\n    (h3 : poleNeutralGlobalRayleighBottom L 3 hL le_rfl < -(D / 3)) : g.cutoff = 3 :=\n  nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g h3\nend\nend FrontierMutation34\n\nsection FrontierMutation35\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.OPICARound4.ArithmeticFrontier\n-- RH gives (PG); the adapter does not make (PG) unconditional.\nexample : FixedParityPolynomialMomentSliceBounds :=\n  fixed_parity_polynomial_of_riemannHypothesis\nend\nend FrontierMutation35\n"
FRONTIER_SEMANTIC_MUTATION_COUNT = 35
PRE_FRONTIER_SEMANTIC_MUTATION_COUNT = 84
PRE_FRONTIER_SEMANTIC_MUTATIONS_SHA256 = '5370614cfdc17c2a0c8ea56dafd0ae170a5797b27f4500bca31fa4a9676e78b0'
# Lean stops reporting after 100 errors, so one rejected-control file cannot carry more controls.
# Shard 01 is the exact pinned 84-control text preceding the arithmetic frontier; shard 02 holds
# every frontier control. Each shard compiles alone under the fixed worker source name, and
# every control must own exactly one type-mismatch error. No control is removed.
SEMANTIC_MUTATION_SOURCE = "RejectedSemanticMutations.lean"
SEMANTIC_MUTATION_SHARD_LIMIT = 90
SEMANTIC_MUTATION_SHARDS = (
    ("01", MADNESS_SEMANTIC_MUTATION_IMPORTS + PRE_MADNESS_SEMANTIC_MUTATIONS + MADNESS_SEMANTIC_MUTATIONS),
    ("02", FRONTIER_SEMANTIC_MUTATION_IMPORTS + FRONTIER_SEMANTIC_MUTATIONS))
SEMANTIC_MUTATIONS = "".join(text for _, text in SEMANTIC_MUTATION_SHARDS)
SEMANTIC_MUTATION_COUNT = 119
SEMANTIC_ENVIRONMENTAL_TERMS = ("unknown module", "unknown identifier", "unknown constant", "file not found",
                                "maximum number of heartbeats", "maximum recursion", "out of memory", "panic")
# SOURCE_CONSTRAINT_MUTATIONS_END
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    from research.RHRC.integration.opica_composition.snapshot import hash_inventory
    return hash_inventory(path.parent, [path.name])[path.name]

def require(value: bool, message: str) -> None:
    if not value:
        raise RuntimeError(message)

def dump(path: Path, value: object) -> None:
    def float_free(item: object) -> None:
        require(not isinstance(item, float), "Floating-point JSON evidence is forbidden")
        if isinstance(item, dict):
            for child in item.values():
                float_free(child)
        elif isinstance(item, (list, tuple)):
            for child in item:
                float_free(child)
    float_free(value)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

def relative(module: str, suffix: str = ".lean") -> Path:
    return Path(*module.split(".")).with_suffix(suffix)

def imports(path: Path) -> list[str]:
    return re.findall(r"(?m)^import\s+(Zeta23(?:\.[A-Za-z0-9_]+)+)", path.read_text(encoding="utf-8"))

def public_declarations(text: str) -> list[str]:
    """Closed module census, including the full field telescope of structures.

    The audited modules each use one public namespace and default constructor
    names. A structure's type alone is only Prop; auditing its constructor is
    necessary to expose every source-dependent hypothesis and field.
    """
    namespace = re.search(r"(?m)^namespace (\S+)", text)
    if namespace is None:
        return []
    declarations = re.findall(
        r"(?m)^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|structure)\s+(\w+(?:\.\w+)*)", text)
    result = []
    for kind, short in declarations:
        name = namespace.group(1) + "." + short
        result.append(name)
        if kind == "structure":
            result.append(name + ".mk")
    return result

def semantic_mutation_shard_scope() -> int:
    """The shards partition the complete control text; each stays below Lean's error cap."""
    ids = [shard_id for shard_id, _ in SEMANTIC_MUTATION_SHARDS]
    counts = [len(re.findall(r"(?m)^example\b", text)) for _, text in SEMANTIC_MUTATION_SHARDS]
    require(ids == ["01", "02"] and
            SEMANTIC_MUTATION_SHARDS[0][1] == MADNESS_SEMANTIC_MUTATION_IMPORTS +
                PRE_MADNESS_SEMANTIC_MUTATIONS + MADNESS_SEMANTIC_MUTATIONS and
            hashlib.sha256(SEMANTIC_MUTATION_SHARDS[0][1].encode()).hexdigest() ==
                PRE_FRONTIER_SEMANTIC_MUTATIONS_SHA256 and
            SEMANTIC_MUTATION_SHARDS[1][1] == FRONTIER_SEMANTIC_MUTATION_IMPORTS + FRONTIER_SEMANTIC_MUTATIONS and
            SEMANTIC_MUTATIONS == "".join(text for _, text in SEMANTIC_MUTATION_SHARDS) and
            counts == [PRE_FRONTIER_SEMANTIC_MUTATION_COUNT, FRONTIER_SEMANTIC_MUTATION_COUNT] and
            all(0 < count <= SEMANTIC_MUTATION_SHARD_LIMIT < 100 for count in counts) and
            sum(counts) == SEMANTIC_MUTATION_COUNT ==
                len(re.findall(r"(?m)^example\b", SEMANTIC_MUTATIONS)),
            "Semantic mutation shard scope changed")
    return sum(counts)

def semantic_shard_binding(text: str, log: str, source_name: str) -> dict:
    """Each control owns exactly one type mismatch, and no error escapes the controls."""
    lines = text.split("\n")
    starts = [number for number, line in enumerate(lines, 1) if re.match(r"example\b", line)]
    spans = []
    for start in starts:
        end = start
        while end < len(lines) and (not lines[end].strip() or lines[end][0].isspace()):
            end += 1
        spans.append((start, end))
    errors = [line for line in log.splitlines() if "error:" in line or "error(" in line]
    located = [re.match(r"^(.*?):(\d+):(\d+): error(?:\(|:)", line) for line in errors]
    require(all(m is not None and re.split(r"[\\/]", m.group(1))[-1] == source_name for m in located),
            "Semantic mutation error outside the rejected-control source")
    owners = [next((start for start, end in spans if start <= int(m.group(2)) <= end), None) for m in located]
    require(0 < len(starts) <= SEMANTIC_MUTATION_SHARD_LIMIT and None not in owners and sorted(owners) == starts and
            all("type mismatch" in line.casefold() for line in errors),
            "Semantic mutations not rejected as intended")
    require(not any(term in log.casefold() for term in SEMANTIC_ENVIRONMENTAL_TERMS),
            "Semantic mutation failure was environmental rather than a type rejection")
    return {"control_count": len(starts), "error_count": len(errors)}

def retained_support_scope() -> dict:
    """The integration checkpoint remains an exact subset of the larger gate."""
    require(len(INTEGRATION_EXPECTED_DECLARATIONS) == INTEGRATION_DECLARATION_COUNT == 397 and
            len(set(INTEGRATION_EXPECTED_DECLARATIONS)) == 397 and
            len(INTEGRATION_MODULES) == INTEGRATION_MODULE_COUNT == 40 and
            len(set(INTEGRATION_MODULES)) == 40 and
            set(INTEGRATION_EXPECTED_DECLARATIONS) <= set(EXPECTED_DECLARATIONS) and
            set(INTEGRATION_MODULES) <= set(MODULES), "Retained 397/40 integration scope changed")
    require(INTEGRATION_SEMANTIC_MUTATION_COUNT == 9 and
            len(re.findall(r"(?m)^example\b", INTEGRATION_SEMANTIC_MUTATIONS)) == 9 and
            PRE_MADNESS_SEMANTIC_MUTATIONS == SOURCE_CONSTRAINT_MUTATION_IMPORTS +
                INTEGRATION_SEMANTIC_MUTATIONS + SOURCE_CONSTRAINT_MUTATIONS and
            semantic_mutation_shard_scope() == SEMANTIC_MUTATION_COUNT,
            "Retained or complete semantic mutation scope changed")
    return {"declarations": INTEGRATION_EXPECTED_DECLARATIONS,
            "modules": INTEGRATION_MODULES, "declaration_count": 397, "module_count": 40,
            "semantic_mutation_count": 9,
            "semantic_mutations_sha256": hashlib.sha256(INTEGRATION_SEMANTIC_MUTATIONS.encode("utf-8")).hexdigest()}

def retained_pre_madness_scope() -> dict:
    """The exact merged Round4 500/48/17 scope remains independently mandatory."""
    require(len(PRE_MADNESS_DECLARATIONS) == PRE_MADNESS_DECLARATION_COUNT == 500 and
            len(PRE_MADNESS_MODULES) == PRE_MADNESS_MODULE_COUNT == 48 and
            hashlib.sha256(json.dumps(PRE_MADNESS_DECLARATIONS, separators=(",", ":")).encode()).hexdigest() == '0e1a0057bd52dc579492214c28bdcd15386ec05fa709c6270faec877d2e84975' and
            hashlib.sha256(json.dumps(PRE_MADNESS_MODULES, separators=(",", ":")).encode()).hexdigest() == 'e54ec086b6c93296406ae4cda5c14d9dfba69ccd029c7fd16eeb4262319c6fd8' and
            set(PRE_MADNESS_DECLARATIONS) <= set(EXPECTED_DECLARATIONS) and
            set(PRE_MADNESS_MODULES) <= set(MODULES), "Retained 500/48 scope changed")
    require(PRE_MADNESS_SEMANTIC_MUTATION_COUNT == 17 and
            len(re.findall(r"(?m)^example\b", PRE_MADNESS_SEMANTIC_MUTATIONS)) == 17 and
            hashlib.sha256(PRE_MADNESS_SEMANTIC_MUTATIONS.encode()).hexdigest() == 'a95ef16e4fdfa6276e1b44b7e3d197fbf63994a17c6e0189f83d746ae11032bd',
            "Retained 17 semantic controls changed")
    return {"declarations": PRE_MADNESS_DECLARATIONS, "modules": PRE_MADNESS_MODULES,
            "declaration_count": 500, "module_count": 48, "semantic_mutation_count": 17,
            "semantic_mutations_sha256": 'a95ef16e4fdfa6276e1b44b7e3d197fbf63994a17c6e0189f83d746ae11032bd'}


def retained_pre_frontier_scope() -> dict:
    """The exact PR299 1079/90/84 scope preceding the arithmetic frontier stays mandatory."""
    declarations = EXPECTED_DECLARATIONS[:PRE_FRONTIER_DECLARATION_COUNT]
    modules = MODULES[:PRE_FRONTIER_MODULE_COUNT]
    previous_mutations = (MADNESS_SEMANTIC_MUTATION_IMPORTS + PRE_MADNESS_SEMANTIC_MUTATIONS +
                          MADNESS_SEMANTIC_MUTATIONS)
    require(len(declarations) == 1079 and len(set(declarations)) == 1079 and
            hashlib.sha256(json.dumps(declarations, separators=(",", ":")).encode()).hexdigest() ==
                PRE_FRONTIER_DECLARATIONS_SHA256 and
            len(modules) == 90 and
            hashlib.sha256(json.dumps(modules, separators=(",", ":")).encode()).hexdigest() ==
                PRE_FRONTIER_MODULES_SHA256 and
            MODULES[PRE_FRONTIER_MODULE_COUNT:] == FRONTIER_MODULES and
            len(re.findall(r"(?m)^example\b", previous_mutations)) == PRE_FRONTIER_SEMANTIC_MUTATION_COUNT and
            hashlib.sha256(previous_mutations.encode()).hexdigest() == PRE_FRONTIER_SEMANTIC_MUTATIONS_SHA256 and
            len(re.findall(r"(?m)^example\b", FRONTIER_SEMANTIC_MUTATIONS)) == FRONTIER_SEMANTIC_MUTATION_COUNT,
            "Retained 1079/90/84 pre-frontier scope changed")
    return {"declaration_count": 1079, "module_count": 90, "semantic_mutation_count": 84,
            "declarations_sha256": PRE_FRONTIER_DECLARATIONS_SHA256,
            "modules_sha256": PRE_FRONTIER_MODULES_SHA256,
            "semantic_mutations_sha256": PRE_FRONTIER_SEMANTIC_MUTATIONS_SHA256}

def root_names(path: Path) -> tuple[list[str], list[dict]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data.get("roots", data) if isinstance(data, dict) else data
    require(isinstance(rows, list), "ROOTS must contain a roots list")
    names, open_rows = [], []
    for row in rows:
        if isinstance(row, str):
            name = row
        else:
            require(isinstance(row, dict), "Malformed ROOTS entry")
            name = row.get("declaration")
            if not name and str(row.get("status", "")).startswith("OPEN"):
                open_rows.append(row)
                continue
        require(isinstance(name, str) and name in EXPECTED_DECLARATIONS,
                "Unknown or missing Lean declaration in ROOTS: " + str(name))
        names.append(name)
    require(bool(names) and len(names) == len(set(names)), "Empty or duplicate Lean ROOTS")
    return names, open_rows

def audit_validation(text: str) -> dict[str, dict]:
    """Read actual compiler output, refusing missing/duplicate types or new axioms."""
    axioms = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        atoms = [a.strip() for a in raw.replace("\n", " ").split(",") if a.strip()]
        require(set(atoms) <= ALLOWED_AXIOMS, "Forbidden transitive axiom in " + name)
        axioms[name] = atoms
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        axioms[name] = []
    require(set(axioms) == set(EXPECTED_DECLARATIONS), "Incomplete or substituted axiom inventory")
    types = {}
    for name in EXPECTED_DECLARATIONS:
        begin, end = "OPICA4_TYPE_BEGIN " + name, "OPICA4_TYPE_END " + name
        require(text.count(begin + "\n") == 1 and text.count(end + "\n") == 1,
                "Missing or duplicate full-type record for " + name)
        match = re.search(re.escape(begin) + r"\n(.*?)\n" + re.escape(end), text, re.S)
        require(match is not None and (match.group(1).startswith("@" + name + " :") or
                match.group(1).startswith(name + " :")), "Missing complete type/axiom audit for " + name)
        types[name] = {"type": match.group(1), "axioms": axioms[name]}
    return types

def _regular(path: Path) -> Path:
    from research.RHRC.integration.opica_composition.snapshot import unlinked
    path = unlinked(path)
    require(stat.S_ISREG(path.lstat().st_mode),
            "Regular mathematical gate file required: " + str(path))
    return path


def _copy_regular(source: Path, target: Path) -> str:
    from research.RHRC.integration.opica_composition.snapshot import unlinked
    source = _regular(source); target = unlinked(target)
    expected = sha(source)
    fd = os.open(source, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0))
    with os.fdopen(fd, "rb") as stream, target.open("xb") as destination:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode) and not (getattr(before, "st_file_attributes", 0) & 1024),
                "Regular no-reparse mathematical input required")
        shutil.copyfileobj(stream, destination)
        after = os.fstat(stream.fileno())
        require((before.st_ino, before.st_dev, before.st_size, before.st_mtime_ns) ==
                (after.st_ino, after.st_dev, after.st_size, after.st_mtime_ns), "Mathematical input changed during copy")
    require(sha(source) == expected == sha(_regular(target)), "Copied mathematical file differs")
    return expected


def _lib_inventory(lib: Path) -> dict[str, str]:
    rows = {}
    for path in sorted(lib.rglob("*")):
        require(not path.is_symlink() and not path.is_junction(), "Linked mathematical import view forbidden")
        if path.is_file():
            rows[path.relative_to(lib).as_posix()] = sha(_regular(path))
        else:
            require(path.is_dir(), "Unexpected mathematical import view entry")
    return rows


def mathematical_budget(worker, timeout: int):
    """The historical heartbeat allowance changes no process, memory or disk cap."""
    from dataclasses import asdict
    from research.RHRC.integration.opica_composition.contracts import SearchBudget
    defaults = asdict(SearchBudget())
    configured = asdict(SearchBudget(**(worker.budget or {})))
    values = {key: min(value, configured[key]) for key, value in defaults.items()}
    values.update(heartbeats=1200000, wall_seconds=min(values["wall_seconds"], timeout))
    values["cpu_seconds"] = min(values["cpu_seconds"], values["wall_seconds"])
    return SearchBudget(**values)


def _isolated_compile(worker, output: Path, lib: Path, source: Path, relative_source: str,
                      budget) -> tuple[dict, Path, dict[str, str]]:
    """Only the coordinator installs compiler products into the read-only view."""
    from dataclasses import replace
    from research.RHRC.integration.opica_composition.executor import run_worker
    output.mkdir(parents=True, exist_ok=False)
    copied = output / relative_source
    copied.parent.mkdir(parents=True, exist_ok=True)
    expected_source = sha(_regular(source))
    _copy_regular(source, copied)
    require(sha(_regular(copied)) == expected_source, "Copied mathematical source differs")
    before = _lib_inventory(lib)
    isolated = replace(worker, lean_paths=[str(lib), *worker.lean_paths])
    obj_name = relative_source[:-5] + ".olean"
    native = run_worker(isolated, output, relative_source, obj_name, budget, mathematical_support=True)
    require(_lib_inventory(lib) == before, "Read-only mathematical import view changed during worker")
    require(sha(_regular(copied)) == expected_source and sha(_regular(source)) == expected_source,
            "Mathematical source changed during worker")
    expected = {relative_source, relative_source + ".log"}
    products = {}
    for suffix in (".olean", ".olean.private", ".olean.server", ".ilean"):
        name = relative_source[:-5] + suffix
        path = output / name
        if path.exists() or path.is_symlink():
            products[name] = sha(_regular(path)); expected.add(name)
    for path in output.rglob("*"):
        require(not path.is_symlink() and not path.is_junction(), "Linked mathematical worker output forbidden")
        if path.is_file():
            require(path.relative_to(output).as_posix() in expected,
                    "Unexpected mathematical worker output: " + str(path))
        else:
            require(path.is_dir() and any((output / name).is_relative_to(path) for name in expected),
                    "Unexpected mathematical worker output directory")
    return native, output / (relative_source + ".log"), products


def run_gate(args: argparse.Namespace, *, worker=None) -> dict:
    repo, output, lean = args.repo.resolve(), args.output_dir.resolve(), args.lean.resolve()
    require(repo.is_dir() and lean.is_file(), "Missing checkout or native compiler")
    require(not output.is_relative_to(repo), "Gate outputs must stay outside the checkout")
    output.mkdir(parents=True, exist_ok=True)
    require(not any(output.iterdir()), "Gate output directory must be fresh and empty")
    state: dict = {"schema": "OPICA4_CURRENT_SOURCE_MATH_GATE_V1", "status": "FAIL",
                   "RH": "OPEN", "Step4": "OPEN", "module_records": [],
                   "execution_mode": "PRODUCTION_ISOLATED" if worker is not None and worker.production else "DEVELOPMENT_ONLY"}
    try:
        from research.RHRC.integration.opica_composition.executor import native_resource_failure, worker_failure_reason
        roots = (args.roots or repo / "research/RHRC/integration/opica_round4/ROOTS.json").resolve()
        require(roots.is_file(), "Missing required ROOTS ledger: " + str(roots))
        names, open_rows = root_names(roots)
        paths = [Path(p).resolve() for p in args.lean_paths.split(os.pathsep) if p]
        require(paths and all(p.is_dir() for p in paths), "Missing prepared native import roots")
        if worker is not None:
            from research.RHRC.integration.opica_composition.contracts import WorkerConfig, as_record
            worker = as_record(worker, WorkerConfig)
            require(Path(worker.lean).resolve() == lean and [Path(p).resolve() for p in worker.lean_paths] == paths,
                    "Mathematical worker/compiler import binding differs")
            budget = mathematical_budget(worker, args.timeout)
            state["worker"] = worker.to_dict()
            state["worker_budget"] = budget.to_dict()
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        pin = (repo / "lean-toolchain").read_text(encoding="utf-8").strip().rsplit(":v", 1)[-1]
        require(pin in version, "Compiler does not match the source toolchain pin")
        sources = {m: repo / relative(m) for m in MODULES}
        require(all(p.is_file() for p in sources.values()), "Missing mandatory mathematical module")
        source_hashes = {m: sha(p) for m, p in sources.items()}
        discovered = []
        for m, p in sources.items():
            text = p.read_text(encoding="utf-8")
            require(not re.search(r"(?m)^\s*(?:private\s+)?(?:axiom|constant)\s|\b(?:sorry|admit|sorryAx)\b", text),
                    "Project axiom or placeholder token in " + m)
            discovered += public_declarations(text)
        require(set(discovered) == set(EXPECTED_DECLARATIONS) and len(discovered) == EXPECTED_DECLARATION_COUNT,
                "Public mathematical declaration inventory changed")
        require(len(BASELINE_EXPECTED_DECLARATIONS) == BASELINE_DECLARATION_COUNT and
                len(BASELINE_MODULES) == BASELINE_MODULE_COUNT and
                set(BASELINE_EXPECTED_DECLARATIONS) <= set(discovered), "Historical 98/16 support subset changed")
        retained_support_scope()
        retained_pre_madness_scope()
        retained_pre_frontier_scope()
        pending, dependencies = list(MODULES), {}
        while pending:
            m = pending.pop()
            if m in dependencies:
                continue
            p = repo / relative(m)
            require(p.is_file(), "Missing project dependency source " + m)
            dependencies[m] = {"source_sha256": sha(p), "imports": imports(p)}
            pending.extend(dependencies[m]["imports"])
        parent_objects = {}
        for m, row in dependencies.items():
            if m in MODULES:
                continue
            obj = next((root / relative(m, ".olean") for root in paths
                        if (root / relative(m, ".olean")).is_file()), None)
            require(obj is not None, "Prepared native parent object missing: " + m)
            parent_objects[m] = {"path": str(obj), "sha256": sha(obj),
                                 "source_sha256": row["source_sha256"]}
        lib = output / "lib"
        lib.mkdir()
        # The coordinator copies authenticated parents; a worker receives this
        # cumulative view read-only and never sees writable checkout/package paths.
        parent_artifacts = {}
        for m, row in parent_objects.items():
            for suffix in (".olean", ".olean.private", ".olean.server"):
                source = Path(row["path"]).with_suffix(suffix)
                if source.is_file():
                    target = lib / relative(m, suffix)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    original_hash = _copy_regular(source, target)
                    parent_artifacts[str(source)] = original_hash
        state["parent_artifacts"] = parent_artifacts
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [lib] + paths)),
                   LEAN_NUM_THREADS="2", PYTHONDONTWRITEBYTECODE="1")
        temp = output / "temp"
        temp.mkdir()
        env.update({k: str(temp) for k in ("TEMP", "TMP", "TMPDIR")})
        order, visited = [], set()
        def visit(m: str) -> None:
            if m in visited:
                return
            visited.add(m)
            for child in dependencies[m]["imports"]:
                if child in MODULES:
                    visit(child)
            order.append(m)
        for m in MODULES:
            visit(m)
        for m in order:
            obj = lib / relative(m, ".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            log = output / (m + ".log")
            argv = [str(lean), "-j2", "-DmaxHeartbeats=1200000", "-DrelaxedAutoImplicit=false",
                    relative(m).as_posix(), "-o", str(obj), "-i", str(obj.with_suffix(".ilean"))]
            start = time.monotonic()
            native = None
            if worker is not None:
                native, native_log, products = _isolated_compile(worker, output / "workers" / m, lib,
                    sources[m], relative(m).as_posix(), budget)
                code = native["exit_code"]
                _copy_regular(native_log, log)
                if native_resource_failure(native):
                    state["native_failure"] = {"module": m, "reason": worker_failure_reason(native), "native": native}
                require(not native_resource_failure(native), "Mathematical module worker resource/environment failure: " +
                        m + ": " + worker_failure_reason(native))
                if code == 0:
                    require(relative(m, ".olean").as_posix() in products and relative(m, ".ilean").as_posix() in products,
                            "Mathematical module object/interface output absent: " + m)
                    for name, expected_hash in products.items():
                        target = lib / name
                        require(not target.exists(), "Mathematical module overwrote import object")
                        _copy_regular(output / "workers" / m / name, target)
                        require(sha(_regular(target)) == expected_hash, "Installed mathematical object differs")
                argv = native["command"]
            else:
                with log.open("wb") as stream:
                    direct = subprocess.run(argv, cwd=repo, env=env, stdout=stream,
                                            stderr=subprocess.STDOUT, timeout=args.timeout)
                code = direct.returncode
            text = log.read_text(encoding="utf-8", errors="replace")
            row = {"module": m, "source_sha256": source_hashes[m], "argv": argv,
                   "exit_code": code, "elapsed_ms": int((time.monotonic() - start) * 1000),
                   "log": str(log), "log_sha256": sha(log),
                   "object_sha256": sha(obj) if obj.is_file() and code == 0 else None}
            if native is not None:
                row.update(native=native, worker_output=str(output / "workers" / m), products=products)
            state["module_records"].append(row)
            require(code == 0 and obj.is_file() and "sorryAx" not in text and
                    not re.search(r"(?m)^.*:\d+:\d+: error(?:\(|:)", text), "Lean module failed: " + m)
        validation = output / "Zeta23.OPICARound4.Validation.log"
        text = validation.read_text(encoding="utf-8")
        types = audit_validation(text)
        dump(output / "types-and-axioms.json", types)
        shards, rejected_errors = [], 0
        for shard_id, shard_text in SEMANTIC_MUTATION_SHARDS:
            shard = output / ("RejectedSemanticMutations-" + shard_id + ".lean")
            shard.write_text(shard_text, encoding="utf-8", newline="\n")
            shard_log = output / ("semantic-mutations-" + shard_id + ".log")
            shard_native = None
            if worker is not None:
                shard_native, native_log, shard_products = _isolated_compile(worker,
                    output / "workers" / ("semantic-mutations-" + shard_id), lib, shard,
                    SEMANTIC_MUTATION_SOURCE, budget)
                rejected_code = shard_native["exit_code"]
                _copy_regular(native_log, shard_log)
                if native_resource_failure(shard_native):
                    state["native_failure"] = {"module": "semantic-mutations-" + shard_id,
                        "reason": worker_failure_reason(shard_native), "native": shard_native}
                require(not native_resource_failure(shard_native) and not shard_products,
                        "Semantic mutation worker exhausted resources or emitted an object")
                compiled_name = SEMANTIC_MUTATION_SOURCE
            else:
                with shard_log.open("wb") as stream:
                    rejected_code = subprocess.run([str(lean), "-j2", "-DmaxHeartbeats=1200000",
                        "-DrelaxedAutoImplicit=false", str(shard)], cwd=repo, env=env, stdout=stream,
                        stderr=subprocess.STDOUT, timeout=args.timeout).returncode
                compiled_name = shard.name
            require(rejected_code == 1, "Semantic mutations not rejected as intended")
            binding = semantic_shard_binding(shard_text, shard_log.read_text(encoding="utf-8", errors="replace"),
                                             compiled_name)
            rejected_errors += binding["error_count"]
            shards.append({"id": shard_id, "source": shard.name, "source_sha256": sha(shard),
                           "log": shard_log.name, "log_sha256": sha(shard_log), "exit_code": rejected_code,
                           **binding, **({"native": shard_native} if shard_native is not None else {})})
        require(rejected_errors == SEMANTIC_MUTATION_COUNT == semantic_mutation_shard_scope(),
                "Semantic mutations not rejected as intended")
        for m, p in sources.items():
            require(sha(p) == source_hashes[m], "Owned source changed during gate: " + m)
        for m, row in dependencies.items():
            require(sha(repo / relative(m)) == row["source_sha256"], "Dependency source changed: " + m)
        for m, row in parent_objects.items():
            require(sha(Path(row["path"])) == row["sha256"], "Prepared parent object changed: " + m)
        for path, expected_hash in parent_artifacts.items():
            require(sha(_regular(Path(path))) == expected_hash, "Prepared parent artifact changed: " + path)
        state.update(status="PASS", module_count=len(order), declaration_count=len(types),
                     baseline_module_count=BASELINE_MODULE_COUNT, baseline_declaration_count=BASELINE_DECLARATION_COUNT,
                     semantic_mutation_count=SEMANTIC_MUTATION_COUNT, roots_count=len(names), open_root_rows=open_rows,
                     integration_declaration_count=INTEGRATION_DECLARATION_COUNT,
                     integration_module_count=INTEGRATION_MODULE_COUNT,
                     roots_sha256=sha(roots), roots_path=str(roots), source_hashes=source_hashes,
                     parent_objects=parent_objects, lean=str(lean), lean_sha256=sha(lean), lean_version=version,
                     toolchain_sha256=sha(repo / "lean-toolchain"), manifest_sha256=sha(repo / "lake-manifest.json"),
                     checker_sha256=sha(Path(__file__)), types_and_axioms_sha256=sha(output / "types-and-axioms.json"),
                     mutation={"exit_code": 1, "error_count": SEMANTIC_MUTATION_COUNT,
                               "source_sha256": hashlib.sha256(SEMANTIC_MUTATIONS.encode("utf-8")).hexdigest(),
                               "shard_limit": SEMANTIC_MUTATION_SHARD_LIMIT, "shards": shards},
                     head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
                     committed_tree=subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=repo, text=True).strip(),
                     authority="CURRENT_SOURCE_ISOLATED_NATIVE_SUPPORT" if worker is not None and worker.production
                               else "DEVELOPMENT_NATIVE_SUPPORT_ONLY")
    except Exception as exc:
        state["failure"] = str(exc)
    dump(output / "result.json", state)
    return state

def load_worker_config(path: Path):
    """Read only the trusted coordinator's closed, hash-bound worker record."""
    from research.RHRC.integration.opica_composition.contracts import WorkerConfig
    path = _regular(path); expected = sha(path)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0)
    with os.fdopen(os.open(path, flags), "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode) and not (getattr(before, "st_file_attributes", 0) & 1024),
                "Regular no-reparse worker configuration required")
        raw = stream.read(65537)
        after = os.fstat(stream.fileno())
        require(len(raw) <= 65536 and (before.st_ino, before.st_dev, before.st_size, before.st_mtime_ns) ==
                (after.st_ino, after.st_dev, after.st_size, after.st_mtime_ns), "Worker configuration oversized or changed")
    require(hashlib.sha256(raw).hexdigest() == expected == sha(path), "Worker configuration bytes changed")
    return WorkerConfig.from_bytes(raw), expected


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--lean-paths", required=True)
    parser.add_argument("--roots", type=Path)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--worker-config", type=Path)
    args = parser.parse_args()
    worker, config_hash = load_worker_config(args.worker_config) if args.worker_config else (None, None)
    result = run_gate(args, worker=worker)
    if args.worker_config:
        require(sha(args.worker_config) == config_hash, "Worker configuration changed during gate")
        result["worker_config_sha256"] = config_hash
        dump(args.output_dir / "result.json", result)
    print(json.dumps({k: result.get(k) for k in ("status", "module_count", "declaration_count", "semantic_mutation_count", "failure")}))
    return 0 if result["status"] == "PASS" else 1

if __name__ == "__main__":
    sys.exit(main())
