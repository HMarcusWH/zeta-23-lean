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
EXPECTED_DECLARATIONS = INTEGRATION_EXPECTED_DECLARATIONS + SOURCE_CONSTRAINT_DECLARATIONS
MODULES = INTEGRATION_MODULES + SOURCE_CONSTRAINT_MODULES
EXPECTED_DECLARATION_COUNT = 500
EXPECTED_MODULE_COUNT = 48
# SOURCE_CONSTRAINT_INVENTORY_END
BASELINE_DECLARATION_COUNT = 98
BASELINE_MODULE_COUNT = 16
# SOURCE_CONSTRAINT_MUTATIONS_BEGIN
INTEGRATION_SEMANTIC_MUTATIONS = 'import Zeta23.OPICARound4.Validation.Support\nimport Zeta23.OPICARound4.OddReciprocalSource\nimport Zeta23.OPICARound4.Validation.IntegrationSpectral\nimport Zeta23.OPICARound4.VisibilityRigidity\n\nnoncomputable section\nnamespace Zeta23.OPICARound4.RejectedSemanticMutations\nopen CCM OPICARound3\nopen scoped BigOperators\n\nvariable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]\n  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]\n  [FiniteDimensional ℂ F]\n\n-- Removing the witness-response norm cost must be rejected.\nexample (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)\n    (e : isometricDetectorComplement J)\n    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :\n    ‖regularSchurWitness J T e hb‖ ^ 2 = ‖(e : F)‖ ^ 2 :=\n  regular_witness_norm_sq J T e hb\n\n-- PSD predecessor plus a one-dimensional shell does not assert successor negativity.\nexample (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)\n    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)\n    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1) (w : F) :\n    (∀ N : Submodule ℂ F,\n      (∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) → Module.finrank ℂ N ≤ 1) ∧\n    ∃ N : Submodule ℂ F, Module.finrank ℂ N = 1 ∧\n      ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0 :=\n  one_shell_negative_index_exact J T hP hshell w\n\n-- Omitting the removed canonical output changes the source functional.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)\n    (u : poleNeutralEvenSubspace L K) :\n    cubicDefectFunctional L K u.val =\n      inner ℂ (correctedSourceRow L K) ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) :=\n  correctedSourceRow_native hL K hK u\n\n-- A source equality at K cannot be silently transported to a different M.\nexample {L : ℝ} (hL : 0 < L) (K M : ℕ) (hK : 3 ≤ K) (hM : 3 ≤ M)\n    (lam : ℝ) (hlamK : lam < poleNeutralOddRayleighBottom L K hL hK)\n    (hlamM : lam < poleNeutralOddRayleighBottom L M hL hM)\n    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)\n    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :\n    poleNeutralCorrectedCubicSource L M (poleNeutralEvenShiftedRay hL M hM lam hlamM) = 1 :=\n  poleNeutral_even_eigen_shiftedRay_source_eq_one hL K hK lam hlamK u hu0 hu\n\n-- The response-facing odd test uses the reciprocal input, not the Riesz input.\n-- Scalar aliases retain exact native values while avoiding huge inverse reduction.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)\n    (sourceRiesz sourceReciprocal : ℂ)\n    (_hRiesz : sourceRiesz = poleNeutralCorrectedCubicSource L K\n      ((poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm\n        (poleNeutralCorrectedCubicRieszVector L K)))\n    (hReciprocal : sourceReciprocal = poleNeutralCorrectedCubicSource L K\n      (nativeOddReciprocalInput hL K hK lam hlam)) :\n    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =\n      -star sourceRiesz := by\n  have htrue : poleNeutralCubicPairingFunctional L K\n      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) = -star sourceReciprocal := by\n    rw [hReciprocal]\n    exact native_odd_response_eq_reciprocal_source hL K hK lam hlam\n  exact htrue\n\n-- Omitting the material odd-response minus sign changes the statement.\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)\n    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)\n    (sourceReciprocal : ℂ)\n    (hReciprocal : sourceReciprocal = poleNeutralCorrectedCubicSource L K\n      (nativeOddReciprocalInput hL K hK lam hlam)) :\n    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =\n      star sourceReciprocal := by\n  have htrue : poleNeutralCubicPairingFunctional L K\n      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) = -star sourceReciprocal := by\n    rw [hReciprocal]\n    exact native_odd_response_eq_reciprocal_source hL K hK lam hlam\n  exact htrue\n\n-- Reality of the grouped residue does not give reality of basis-coordinate terms.\nexample :\n    (Validation.repeatedSpectrumCoordinateCoefficient Validation.repeatedSpectrumP₁).im = 0 :=\n  Validation.repeated_spectrum_nonreal_coordinates.2.2.1\n\n-- Full input/output visibility gives nonzero mass, not nonnegative mass.\nexample (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) (hB : B.IsSymmetric)\n    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)\n    (hrank : RankOneIntertwining A B D g f) (β : GroupedSpectrum B)\n    (hin : ¬ GroupedInputInvisible hB g β) (hout : ¬ GroupedOutputInvisible hB D f β) :\n    0 ≤ groupedSignedResidue hB D g f β := by\n  have hnonzero : groupedSignedResidue hB D g f β ≠ 0 := by\n    intro hz\n    rcases (grouped_residue_zero_iff_input_or_output_invisible hA hB D g f hrank β).mp hz with h | h\n    · exact hin h\n    · exact hout h\n  exact hnonzero\n\n-- The signed Pick index is bounded by the negative atom count, not by one.\nexample {ι κ : Type*} [Fintype ι] [Fintype κ]\n    (eigenvalue residue : ι → ℝ) (points : κ → ℂ) (N : Submodule ℂ (κ → ℂ))\n    (hN : ∀ a : N, a ≠ 0 →\n      (∑ j, ∑ k, (a : κ → ℂ) j * signedPickKernel eigenvalue residue\n        (points j) (points k) * star ((a : κ → ℂ) k)).re < 0) :\n    Module.finrank ℂ N ≤ 1 :=\n  finite_signed_pick_negative_subspace_bound eigenvalue residue points N hN\n\n\nend Zeta23.OPICARound4.RejectedSemanticMutations\n'
INTEGRATION_SEMANTIC_MUTATION_COUNT = 9
SOURCE_CONSTRAINT_MUTATIONS = '-- Source constraint mutation: geometry_wrong_even_sign.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :\n    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs\n    nativeSignedPrimeDiscrepancy L K r = nativeArchContinuumRow L K r + 1 :=\n  (actual_even_ground_signed_discrepancy hL K hK hs).2.1\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: geometry_wrong_odd_input.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)\n    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :\n    poleNeutralCorrectedCubicSource L K\n      ((poleNeutralEvenShiftedCanonicalEquiv hL K hK\n        (poleNeutralOddRayleighBottom L K hL hK) hs).symm (poleNeutralCorrectedCubicRieszVector L K)) = -1 :=\n  (actual_odd_ground_reciprocal_discrepancy hL K hK hs).1\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: geometry_omitted_tie.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4.GeometryMutation\nopen CCM OPICARound3\n\nexample {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :\n    NativeStrictEvenGroundConstraints hL K hK ∨ NativeStrictOddGroundConstraints hL K hK :=\n  joint_ground_constraints_of_both_negative hL K hK hboth\n\nend Zeta23.OPICARound4.GeometryMutation\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/WrongSmoothShift.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a)\n    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)\n      (out.retained.state.selection.cutoff - 1)) :\n    inner ℂ v (smoothSourceForcing out) =\n      zetaZeroConfig.W out.originalTrial (out.forcingTest v) -\n        (out.retained.state.selection.eta : ℂ) * EF.weilTest out.originalTrial (out.forcingTest v) 0 :=\n  validation_smooth_source_forcing out v\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/DroppedSchurMassError.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a) :\n    |detectorSchurLoss out - smoothSourceMain out| ≤\n      sourceInverseBudget out * sourceForcingErrorBudget out *\n        (2 * finiteForcingBudget out + sourceForcingErrorBudget out) +\n      sourceEnergyErrorBudget (fixedOriginalSincTrialAperture a) :=\n  detectorSchurLoss_sub_smoothSourceMain_bound out\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: arithmetic/semantic-controls/DroppedFirstCutoffEnergy.lean\nnoncomputable section\nnamespace Zeta23.OPICARound4\nopen CCM ExceptionalZero\nexample {β a : ℝ} {σ : ReversalParity} (out : Step123NativeOutput β σ a)\n    (hK : out.retained.state.selection.cutoff = 3) :\n    detectorSchurLoss out = -out.retained.state.selection.eta :=\n  detectorSchurLoss_at_first out hK\nend Zeta23.OPICARound4\n\n\n-- Source constraint mutation: quartic/mutations/SourceErrorWrongQuantifier.lean\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\n\n-- Incorrect strengthening: one threshold is required to pay every M\n-- simultaneously. The proved threshold is selected after each fixed M.\nexample (δ : ℝ) (hδ : 0 < δ) :\n    ∃ L₀ : ℝ, ∀ (M β : ℝ) (σ : ReversalParity) (a : ℝ)\n      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →\n      |detectorSchurLoss out - smoothSourceMain out| <\n        δ * Real.exp (-M * fixedOriginalSincTrialAperture a) := by\n  exact exists_uniform_source_schur_error_threshold 0 δ hδ\n\n\n-- Source constraint mutation: quartic/mutations/SourceMainWrongSign.lean\nnoncomputable section\nopen Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4\n\n-- The surviving source requirement is a lower bound. Treating it as an\n-- independently proved upper bound would manufacture the missing Step4 law.\nexample :\n    ∃ L₀ : ℝ, ∀ (ρ : zetaZeroConfig.carrier) (β : ℝ)\n      (σ : ReversalParity) (R : ℝ)\n      (g : GeneratedStep123CompleteOutput ρ β σ R), L₀ ≤ R →\n        smoothSourceMain g.generated.native <\n          Real.exp (β * fixedOriginalSincTrialAperture g.generated.sourceData.separation) / 4 := by\n  exact exists_generated_smooth_source_main_lower_threshold\n'
SOURCE_CONSTRAINT_MUTATION_IMPORTS = 'import Zeta23.OPICARound4.JointGroundConstraints\nimport Zeta23.OPICARound4.QuarticErrorReduction\nimport Zeta23.OPICARound4.Validation.DetectorErrors\n'
SEMANTIC_MUTATIONS = SOURCE_CONSTRAINT_MUTATION_IMPORTS + INTEGRATION_SEMANTIC_MUTATIONS + SOURCE_CONSTRAINT_MUTATIONS
SEMANTIC_MUTATION_COUNT = 17
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
        r"(?m)^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|structure)\s+(\w+)", text)
    result = []
    for kind, short in declarations:
        name = namespace.group(1) + "." + short
        result.append(name)
        if kind == "structure":
            result.append(name + ".mk")
    return result

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
            SEMANTIC_MUTATIONS == SOURCE_CONSTRAINT_MUTATION_IMPORTS +
                INTEGRATION_SEMANTIC_MUTATIONS + SOURCE_CONSTRAINT_MUTATIONS and
            len(re.findall(r"(?m)^example\b", SEMANTIC_MUTATIONS)) == SEMANTIC_MUTATION_COUNT,
            "Retained or complete semantic mutation scope changed")
    return {"declarations": INTEGRATION_EXPECTED_DECLARATIONS,
            "modules": INTEGRATION_MODULES, "declaration_count": 397, "module_count": 40,
            "semantic_mutation_count": 9,
            "semantic_mutations_sha256": hashlib.sha256(INTEGRATION_SEMANTIC_MUTATIONS.encode("utf-8")).hexdigest()}

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
        mutation = output / "RejectedSemanticMutations.lean"
        mutation.write_text(SEMANTIC_MUTATIONS, encoding="utf-8", newline="\n")
        mutation_log = output / "semantic-mutations.log"
        mutation_argv = [str(lean), "-j2", "-DmaxHeartbeats=1200000", "-DrelaxedAutoImplicit=false", str(mutation)]
        mutation_native = None
        if worker is not None:
            mutation_native, native_log, mutation_products = _isolated_compile(worker,
                output / "workers" / "semantic-mutations", lib, mutation, mutation.name, budget)
            rejected_code = mutation_native["exit_code"]
            _copy_regular(native_log, mutation_log)
            if native_resource_failure(mutation_native):
                state["native_failure"] = {"module": "semantic-mutations",
                    "reason": worker_failure_reason(mutation_native), "native": mutation_native}
            require(not native_resource_failure(mutation_native) and not mutation_products,
                    "Semantic mutation worker exhausted resources or emitted an object")
        else:
            with mutation_log.open("wb") as stream:
                rejected_code = subprocess.run(mutation_argv, cwd=repo, env=env, stdout=stream,
                                          stderr=subprocess.STDOUT, timeout=args.timeout).returncode
        text = mutation_log.read_text(encoding="utf-8", errors="replace")
        errors = [line for line in text.splitlines() if "error:" in line or "error(" in line]
        require(rejected_code == 1 and len(errors) == SEMANTIC_MUTATION_COUNT and
                all("type mismatch" in line.casefold() for line in errors), "Semantic mutations not rejected as intended")
        require(not any(x in text.casefold() for x in ("unknown module", "unknown identifier", "unknown constant",
                    "file not found", "maximum number of heartbeats", "maximum recursion", "out of memory", "panic")),
                "Semantic mutation failure was environmental rather than a type rejection")
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
                     mutation={"exit_code": rejected_code, "source_sha256": sha(mutation),
                               "log_sha256": sha(mutation_log), "error_count": SEMANTIC_MUTATION_COUNT,
                               **({"native": mutation_native} if mutation_native is not None else {})},
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
