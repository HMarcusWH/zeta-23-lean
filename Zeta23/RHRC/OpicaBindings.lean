import Zeta23.OPICA.Validation
import Zeta23.RHRC.OpicaTypeExprExport
import Zeta23.RHRC.DeclarationDependencyExport
import Zeta23.RHRC.SourceCandidateResolution
import Lean.Util.CollectAxioms

/-! AUDIT_ONLY complete public OPICA environment inventory. No proof authority. -/
open Lean Lean.Elab Command

namespace Zeta23.RHRC

private def opicaKind : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

run_cmd do
  let queries : Array SourceCandidateQuery := #[
    ({ sourceId := "OPICA_L1_UNIT_MUL_SIMPLEPOLE_RESIDUE", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.unit_mul_simplePole_residue", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L1_COMPLETION_REGULARREPRESENTATIVE_ANALYTIC", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.completion_regularRepresentative_analytic", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L1_COMPLETION_ORDER", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.completion_order", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L1_COMPLETION_LEADING_JET", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.completion_leading_jet", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L2_ZERO_IDEAL_EQ_COORDINATE_POWER", moduleName := "Zeta23.OPICA.LocalQuotients", shortName := "Zeta23.OPICA.zero_ideal_eq_coordinate_power", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L2_TRUNCATED_TAYLOR_QUOTIENT_EQUIV", moduleName := "Zeta23.OPICA.LocalQuotients", shortName := "Zeta23.OPICA.truncated_taylor_quotient_equiv", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L2_COMPLETION_QUOTIENT_EQUIV", moduleName := "Zeta23.OPICA.LocalQuotients", shortName := "Zeta23.OPICA.completion_quotient_equiv", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L2_RESIDUAL_CONGR_PRESERVES_RESIDUE", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.residual_congr_preserves_residue", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L2_FINITE_RESIDUAL_PRODUCTS_PRESERVE_RESIDUE", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.finite_residual_products_preserve_residue", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L3_ITERATED_COMPLETION_LEADING_JET", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.iterated_completion_leading_jet", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L3_DOUBLE_COMPLETION_LEIBNIZ_FACTOR", moduleName := "Zeta23.OPICA.LocalObstruction", shortName := "Zeta23.OPICA.double_completion_leibniz_factor", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L4_AFFINE_TRANSPORT_CORRECTED_EQ", moduleName := "Zeta23.OPICA.AffineTransport", shortName := "Zeta23.OPICA.affine_transport_corrected_eq", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L4_AFFINE_TRANSPORT_LEADING_JET", moduleName := "Zeta23.OPICA.AffineTransport", shortName := "Zeta23.OPICA.affine_transport_leading_jet", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L4_ANALYTIC_ADDITION_CAN_CANCEL_COMPLETED_JET", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.analytic_addition_can_cancel_completed_jet", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L5_RESIDUE_CONTINUOUS_OF_CIRCLE_UNIFORM", moduleName := "Zeta23.OPICA.ResidueLimits", shortName := "Zeta23.OPICA.residue_continuous_of_circle_uniform", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_L5_ESCAPING_TAIL_KEEPS_RESIDUE", moduleName := "Zeta23.OPICA.ResidueLimits", shortName := "Zeta23.OPICA.escaping_tail_keeps_residue", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E1_LOG_ONE_ADD_POSPART_SUB_LE", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.log_one_add_posPart_sub_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E1_LOG_ONE_ADD_NORM_SUB_LE", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.log_one_add_norm_sub_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_SUBEXPALONG_ADD", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.subexpAlong_add", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_SUBEXPALONG_MUL", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.subexpAlong_mul", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_SUBEXPALONG_CONST_SMUL", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.subexpAlong_const_smul", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_RATE_CONGR_OF_SUBEXP_ERROR", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.rate_congr_of_subexp_error", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_POSRATE_CONGR_OF_SUBEXP_ERROR", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.posRate_congr_of_subexp_error", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E2_RATE_LIMSUP_LIMINF_CONGR", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.rate_limsup_liminf_congr", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E3_RATE_CONGR_OF_TEMPERED_SCALE", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.rate_congr_of_tempered_scale", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E3_POSRATE_CONGR_OF_POSITIVE_TEMPERED_SCALE", moduleName := "Zeta23.OPICA.EnergyRate", shortName := "Zeta23.OPICA.posRate_congr_of_positive_tempered_scale", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E4_AFFINE_CHAIN_EXPANSION", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.affine_chain_expansion", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E4_AFFINE_CHAIN_BUDGET", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.affine_chain_budget", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E4_RATE_CONGR_OF_ACCUMULATED_BUDGET", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.rate_congr_of_accumulated_budget", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_E5_QUIET_COFINAL_RATE_ZERO", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.quiet_cofinal_rate_zero", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_C1_QUOTIENT_MAP_INJECTIVE_IFF", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.quotient_map_injective_iff", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_C1_FAITHFUL_TRANSFER_COMP", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.faithful_transfer_comp", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_C2_OBSTRUCTION_PATH_NONZERO", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.obstruction_path_nonzero", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_C2_IMPLICATION_PATH_NONZERO", moduleName := "Zeta23.OPICA.Composition", shortName := "Zeta23.OPICA.implication_path_nonzero", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A1_DIVISOR_COUNT_SUBMULTIPLICATIVE", moduleName := "Zeta23.OPICA.DivisorBounds", shortName := "Zeta23.OPICA.divisor_count_submultiplicative", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A1_DIVISOR_COUNT_SQUARE_LE", moduleName := "Zeta23.OPICA.DivisorBounds", shortName := "Zeta23.OPICA.divisor_count_square_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A1_DIVISOR_COUNT_HARMONIC_SUM_LE", moduleName := "Zeta23.OPICA.DivisorBounds", shortName := "Zeta23.OPICA.divisor_count_harmonic_sum_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A1_DIVISOR_COUNT_SQRT_SUM_LE", moduleName := "Zeta23.OPICA.DivisorBounds", shortName := "Zeta23.OPICA.divisor_count_sqrt_sum_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A2_PRIMITIVE_MASK_PARTITION", moduleName := "Zeta23.OPICA.PrimitiveMasks", shortName := "Zeta23.OPICA.primitive_mask_partition", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A2_LOW_PRIMITIVE_BILINEAR_BOUND", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.low_primitive_bilinear_bound", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A2_MASKED_TYPEI_MIXED_BOUND", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.masked_typeI_mixed_bound", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A2_MASKED_TYPEI_SQUARE_BOUND", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.masked_typeI_square_bound", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A2_BALANCED_ENERGY_COMPARISON", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.balanced_energy_comparison", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A3_MASK_REGROUPING_DIFFERENCE", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.mask_regrouping_difference", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_A3_REGROUPED_MASK_RATE_CONGR", moduleName := "Zeta23.OPICA.DivisorMask", shortName := "Zeta23.OPICA.regrouped_mask_rate_congr", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_B1_LAPLACE_HOLOMORPHIC_OF_WEIGHTED_L2", moduleName := "Zeta23.OPICA.WeightedLaplace", shortName := "Zeta23.OPICA.laplace_holomorphic_of_weighted_L2", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_B1_LAPLACE_ITERATEDDERIV_BOUND_OF_WEIGHTED_L2", moduleName := "Zeta23.OPICA.WeightedLaplace", shortName := "Zeta23.OPICA.laplace_iteratedDeriv_bound_of_weighted_L2", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_B1_NO_VISIBLE_POLE_OF_WEIGHTED_L2", moduleName := "Zeta23.OPICA.WeightedLaplace", shortName := "Zeta23.OPICA.no_visible_pole_of_weighted_L2", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_B2_RANGE_DISTANCE_OF_ANNIHILATOR", moduleName := "Zeta23.OPICA.RangeSeparation", shortName := "Zeta23.OPICA.range_distance_of_annihilator", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_B2_NOT_MEM_RANGECLOSURE_OF_ANNIHILATOR", moduleName := "Zeta23.OPICA.RangeSeparation", shortName := "Zeta23.OPICA.not_mem_rangeClosure_of_annihilator", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O1_OBSERVATION_FACTORS_IFF_KER_LE", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.observation_factors_iff_ker_le", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O1_CONTRAST_CANNOT_RECOVER_SUM", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.contrast_cannot_recover_sum", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O2_GRAM_INTEGRAL_POSSEMIDEF", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.gram_integral_posSemidef", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O2_GRAM_INTEGRAL_NOT_RANK_ONE", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.gram_integral_not_rank_one", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O2_SINGLE_VECTOR_BOUND_NOT_OPERATOR_BOUND", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.single_vector_bound_not_operator_bound", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O2_OFFDIAGONAL_MASK_NOT_POSSEMIDEF", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.offDiagonal_mask_not_posSemidef", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O3_INCOMPATIBLE_IFF_LEFT_ANNIHILATOR", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.incompatible_iff_left_annihilator", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O3_RANGE_DISTANCE_EQ_ANNIHILATOR_SUP", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.range_distance_eq_annihilator_sup", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O3_SEVEN_SAMPLES_SIX_COEFFICIENTS_CONSISTENT", moduleName := "Zeta23.OPICA.Counterexamples", shortName := "Zeta23.OPICA.seven_samples_six_coefficients_consistent", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O4_COMPATIBILITY_UNDER_INVERTIBLE_LEFT_MAP", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.compatibility_under_invertible_left_map", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_O4_SOLUTIONS_PRESERVED_UNDER_LEFT_MAP", moduleName := "Zeta23.OPICA.ObservationCompatibility", shortName := "Zeta23.OPICA.solutions_preserved_under_left_map", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H1_SIGNED_SHARP_GAP_SEPARATOR", moduleName := "Zeta23.OPICA.SignedHeatSeparator", shortName := "Zeta23.OPICA.signed_sharp_gap_separator", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H2_SIGNED_GAP_NEGATIVE_MASS_BUDGET", moduleName := "Zeta23.OPICA.SignedHeatSeparator", shortName := "Zeta23.OPICA.signed_gap_negative_mass_budget", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H3_COMMUTATOR_ANTI_INVARIANT", moduleName := "Zeta23.OPICA.Involution", shortName := "Zeta23.OPICA.commutator_anti_invariant", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H3_COMMUTATOR_SELFDUAL_PROJECTION_ZERO", moduleName := "Zeta23.OPICA.Involution", shortName := "Zeta23.OPICA.commutator_selfdual_projection_zero", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H4_FEJER_FLOOR_FORMULA", moduleName := "Zeta23.OPICA.FejerCompletion", shortName := "Zeta23.OPICA.fejer_floor_formula", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H4_FEJER_NATIVECOMPLETION_POINTWISE", moduleName := "Zeta23.OPICA.FejerCompletion", shortName := "Zeta23.OPICA.fejer_nativeCompletion_pointwise", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H4_FEJER_COMPLETION_AFFINE_IDENTITY", moduleName := "Zeta23.OPICA.FejerCompletion", shortName := "Zeta23.OPICA.fejer_completion_affine_identity", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_H4_FEJER_LOGINTEGER_ONESIDEDDERIVATIVES", moduleName := "Zeta23.OPICA.FejerCompletion", shortName := "Zeta23.OPICA.fejer_logInteger_oneSidedDerivatives", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_ORDER", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.native_completed_input_obstruction_order", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_JET", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.native_completed_input_obstruction_jet", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_NE_ZERO", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.native_completed_input_obstruction_ne_zero", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_NATIVE_RANGE_DISTANCE_LOWER", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.native_range_distance_lower", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_STEP123_OUTPUT_OPICA_VIEW_CORRECT", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.step123_output_opica_view_correct", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_STEP123_EACHPHASE_OPICA_CONSUMER", moduleName := "Zeta23.OPICA.NativeJetAdapter", shortName := "Zeta23.OPICA.step123_eachPhase_opica_consumer", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery),
    ({ sourceId := "OPICA_NATIVE_NATIVE_ORIGINAL_DRIVE_LOW_MASK_BOUND", moduleName := "Zeta23.OPICA.NativeArithmeticAdapter", shortName := "Zeta23.OPICA.native_original_drive_low_mask_bound", sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery)]
  -- Resolving all 76 is required even when some other public helpers compile.
  resolveSourceCandidates queries
  let env ← getEnv
  let mathematicalModules : Array String := #[
    "Zeta23.OPICA.LocalData",
    "Zeta23.OPICA.LocalObstruction",
    "Zeta23.OPICA.LocalQuotients",
    "Zeta23.OPICA.ResidueLimits",
    "Zeta23.OPICA.AffineTransport",
    "Zeta23.OPICA.EnergyRate",
    "Zeta23.OPICA.Composition",
    "Zeta23.OPICA.ObservationCompatibility",
    "Zeta23.OPICA.DivisorBounds",
    "Zeta23.OPICA.PrimitiveMasks",
    "Zeta23.OPICA.DivisorMask",
    "Zeta23.OPICA.WeightedLaplace",
    "Zeta23.OPICA.RangeSeparation",
    "Zeta23.OPICA.NativeJetAdapter",
    "Zeta23.OPICA.NativeArithmeticAdapter",
    "Zeta23.OPICA.Involution",
    "Zeta23.OPICA.LocallyFiniteSignedMeasure",
    "Zeta23.OPICA.SincTriangle",
    "Zeta23.OPICA.SignedHeatSeparator",
    "Zeta23.OPICA.FejerCompletion",
    "Zeta23.OPICA.FourierCompatibility",
    "Zeta23.OPICA.Counterexamples",
    "Zeta23.OPICA"]
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let definingModule := env.allImportedModuleNames[index.toNat]!
      if mathematicalModules.contains definingModule.toString && !name.isInternal && !isPrivateName name then
        -- Lean may cache a generated congruence theorem in this module under
        -- the constructor's original namespace. Include it in every audit.
        unless name.toString.startsWith "Zeta23.OPICA." ||
            (name.toString.endsWith ".congr_simp" && opicaKind info == "THEOREM") do
          throwError "Public mathematical declaration escaped OPICA namespace: {name} in {definingModule}"
        names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "OPICA public namespace is empty"
  for name in names do
    let info ← getConstInfo name
    let some index := env.getModuleIdxFor? name
      | throwError "OPICA declaration has no defining imported module: {name}"
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !moduleName.toString.startsWith "Zeta23.OPICA" then
      throwError "OPICA declaration escaped its expected module namespace: {name} in {moduleName}"
    let typeDag ← liftIO <| OpicaTypeExprExport.exportType info.type
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "OPICA unadmitted mathematical axiom: {name} uses {ax}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"OPICA_DECL\t{name}\t{moduleName}\t{opicaKind info}\t{typeDag}\t{axiomText}"
    match info with
    | .inductInfo data =>
      for ctor in data.ctors do
        let ctorInfo ← getConstInfo ctor
        let ctorType ← liftIO <| OpicaTypeExprExport.exportType ctorInfo.type
        liftIO <| IO.println s!"OPICA_CONSTRUCTOR\t{name}\t{ctor}\t{ctorType}"
    | _ => pure ()
  liftIO <| IO.println s!"OPICA_PUBLIC_COUNT\t{names.size}"
  exportDependencies names
  liftIO <| IO.println s!"OPICA_COMPLETE\t{names.size}"

end Zeta23.RHRC
