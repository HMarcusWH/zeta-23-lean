import Zeta23.OPICAFollowup
import Zeta23.OPICAFollowup.AuxiliaryCompletions
import Zeta23.OPICAFollowup.BalancedCoefficients
import Zeta23.OPICAFollowup.BoundaryAmplitude
import Zeta23.OPICAFollowup.CoPoissonJets
import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Zeta23.OPICAFollowup.ConfluentProfiles
import Zeta23.OPICAFollowup.Consumers
import Zeta23.OPICAFollowup.Counterexamples
import Zeta23.OPICAFollowup.DilatedComb
import Zeta23.OPICAFollowup.FiniteSpanSeparation
import Zeta23.OPICAFollowup.FirstCellCost
import Zeta23.OPICAFollowup.ForcedEuler
import Zeta23.OPICAFollowup.ForwardLocalization
import Zeta23.OPICAFollowup.JointObservation
import Zeta23.OPICAFollowup.LogFourierSobolev
import Zeta23.OPICAFollowup.LogSlackBalance
import Zeta23.OPICAFollowup.MaskedNativeRate
import Zeta23.OPICAFollowup.MovingSourceWindowRate
import Zeta23.OPICAFollowup.MultiplicityTail
import Zeta23.OPICAFollowup.NativeExplicitFormula
import Zeta23.OPICAFollowup.NativeFilters
import Zeta23.OPICAFollowup.NativeResolvent
import Zeta23.OPICAFollowup.NativeSourceFamily
import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.OPICAFollowup.NativeTransformationWords
import Zeta23.OPICAFollowup.NativeWindowRate
import Zeta23.OPICAFollowup.NearGapLimits
import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICAFollowup.ProfileEulerMaclaurin
import Zeta23.OPICAFollowup.RenormalizedCoPoisson
import Zeta23.OPICAFollowup.RobustLaurent
import Zeta23.OPICAFollowup.SamplingCompatibility
import Zeta23.OPICAFollowup.SawtoothForce
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.OPICAFollowup.SquareDefect
import Zeta23.OPICAFollowup.UniformSourceBounds
import Zeta23.OPICAFollowup.Validation
import Zeta23.OPICAFollowup.WeightedMixing
import Zeta23.OPICAFollowup.WeightedSpectralMeasure
import Zeta23.OPICAFollowup.ZeroProfiles
import Zeta23.OPICAFollowup.ZetaLeftLineBounds
import Zeta23.OPICAFollowup.Validation
import Zeta23.RHRC.OpicaTypeExprExport
import Lean.Util.FoldConsts
import Zeta23.RHRC.SourceCandidateResolution
import Lean.Util.CollectAxioms
import Lean.Meta.Eqns

/-! AUDIT_ONLY source-bound enumeration of the implemented subset.
The remaining planned roots are absent, never counted as proved. -/
open Lean Lean.Elab Command
namespace Zeta23.RHRC

namespace FollowupDependencyExport
private def moduleOf? (env : Environment) (decl : Name) : Option Name :=
  match env.getModuleIdxFor? decl with
  | none => none
  | some modIdx => some env.allImportedModuleNames[modIdx.toNat]!

private def isProjectLocalModule : Option Name → Bool
  | none => false
  | some modName =>
      let s := modName.toString
      s == "Zeta23" || s.startsWith "Zeta23."

private def kindString : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

private def structuralDependencies : ConstantInfo → Array Name
  | .inductInfo info => (info.ctors ++ info.all).toArray
  | .ctorInfo info => #[info.induct]
  | .recInfo info => info.all.toArray
  | _ => #[]

private def emitDeclaration (env : Environment) (decl : Name) : CommandElabM Unit := do
  let some info := env.find? decl
    | throwError "RHKG dependency export: unknown declaration {decl}"
  let moduleText := match moduleOf? env decl with
    | some modName => modName.toString
    | none => "-"
  let privateOrInternalText := if decl.isInternal || isPrivateName decl then "1" else "0"
  liftIO <| IO.println s!"RHKG_DEP_DECL\t{decl}\t{moduleText}\t{kindString info}\t{privateOrInternalText}"

private def emitChannel
    (source : Name) (deps : NameSet) (channel : String) : CommandElabM Unit := do
  let mut line := s!"RHKG_DEP_CHANNEL\t{source}\t{channel}"
  for dep in deps do
    line := line ++ "\t" ++ dep.toString
  liftIO <| IO.println line

private partial def visit
    (env : Environment) (pending : List Name)
    (visited emitted scheduled : NameHashSet) : CommandElabM Unit := do
  match pending with
  | [] => return
  | decl :: rest =>
      if visited.contains decl then
        visit env rest visited emitted scheduled
      else
        let some info := env.find? decl
          | throwError "RHKG dependency export: unknown declaration {decl}"
        let mut emitted := emitted
        if !(emitted.contains decl) then
          emitDeclaration env decl
          emitted := emitted.insert decl
        -- The receipt records presence-by-channel, not occurrence multiplicity.
        -- NameSet prevents repeated appearances in a large proof term from
        -- creating duplicate protocol edges or duplicate traversal work.
        let typeDeps := info.type.getUsedConstantsAsSet
        let valueDeps := match info.value? (allowOpaque := true) with
          | some value => value.getUsedConstantsAsSet
          | none => ({} : NameSet)
        let structureDeps :=
          (NameSet.ofArray (structuralDependencies info)).filter fun dep => dep != decl

        -- Preserve exact expression-level self references if Lean emits them.
        -- Structural membership self-links are excluded because they are
        -- declaration-family bookkeeping rather than constant use.
        for dep in typeDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep
        for dep in valueDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep
        for dep in structureDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep

        -- Emit at most one protocol record per declaration/channel rather than
        -- one IO.println per edge. The Python side reconstructs the same exact
        -- channel presence relation from the batched records.
        emitChannel decl typeDeps "TYPE"
        emitChannel decl valueDeps "VALUE"
        emitChannel decl structureDeps "STRUCTURE"

        -- A visited set alone does not deduplicate declarations that are
        -- queued many times before their first visit. Track scheduled names
        -- so highly shared dependencies enter the pending list only once.
        let mut next := rest
        let mut scheduled := scheduled
        for dep in typeDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        for dep in valueDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        for dep in structureDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        visit env next (visited.insert decl) emitted scheduled

/--
Emit the local Zeta23 dependency closure rooted at the supplied declarations.
External constants are emitted as boundary nodes but are not recursively expanded.
-/
public def exportDependencies (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut scheduled : NameHashSet := {}
  for root in roots do
    scheduled := scheduled.insert root
  visit env roots.toList {} {} scheduled



end FollowupDependencyExport

private def opicaKind : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

/-- Lean reserves these names for equations of an existing safe definition.
The equation still receives the full public type, axiom and dependency audit. -/
private def reservedEquationOrigin? (env : Environment) (name : Name)
    (info : ConstantInfo) : Option Name := do
  if opicaKind info != "THEOREM" then none else do
    let (origin, suffix) ← Lean.Meta.declFromEqLikeName env name
    if name == Lean.Meta.mkEqLikeNameFor env origin suffix then some origin else none

run_cmd do
  let queries : Array SourceCandidateQuery := #[
    ({ sourceId := "OPICA_FOLLOWUP_SOURCEFAMILY_ZERO_EQ_ORIGINAL", moduleName := "Zeta23.OPICAFollowup.NativeSourceFamily", shortName := "Zeta23.OPICAFollowup.sourceFamily_zero_eq_original", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SOURCEFAMILY_SUPPORT_SMOOTH_MOMENTS", moduleName := "Zeta23.OPICAFollowup.NativeSourceFamily", shortName := "Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SOURCEFAMILY_LAPLACE_IDENTITY", moduleName := "Zeta23.OPICAFollowup.NativeSourceTransforms", shortName := "Zeta23.OPICAFollowup.sourceFamily_laplace_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FORWARDKERNEL_PHYSICAL_LAPLACE", moduleName := "Zeta23.OPICAFollowup.NativeSourceTransforms", shortName := "Zeta23.OPICAFollowup.forwardKernel_physical_laplace", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEPRIMEFIELD_VISIBLEPOLE", moduleName := "Zeta23.OPICAFollowup.NativeSourceTransforms", shortName := "Zeta23.OPICAFollowup.nativePrimeField_visiblePole", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEGENERATOR_TRANSFORM", moduleName := "Zeta23.OPICAFollowup.NativeFilters", shortName := "Zeta23.OPICAFollowup.nativeGenerator_transform", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEGENERATOR_UNIT_OR_COMPLETION", moduleName := "Zeta23.OPICAFollowup.NativeFilters", shortName := "Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEWORD_CORRECTED_TRANSFORM", moduleName := "Zeta23.OPICAFollowup.NativeTransformationWords", shortName := "Zeta23.OPICAFollowup.nativeWord_corrected_transform", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEWORD_ORDER_AND_LEADING", moduleName := "Zeta23.OPICAFollowup.NativeTransformationWords", shortName := "Zeta23.OPICAFollowup.nativeWord_order_and_leading", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEWORD_FIRST_NONZERO_DERIVATIVE", moduleName := "Zeta23.OPICAFollowup.NativeTransformationWords", shortName := "Zeta23.OPICAFollowup.nativeWord_first_nonzero_derivative", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEWORD_FACTOR_COSTS", moduleName := "Zeta23.OPICAFollowup.NativeTransformationWords", shortName := "Zeta23.OPICAFollowup.nativeWord_factor_costs", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NORM_FIRST_LOG_COMPARISON", moduleName := "Zeta23.OPICAFollowup.NormFirstTransfer", shortName := "Zeta23.OPICAFollowup.norm_first_log_comparison", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NORM_FIRST_RATE_TRANSFER", moduleName := "Zeta23.OPICAFollowup.NormFirstTransfer", shortName := "Zeta23.OPICAFollowup.norm_first_rate_transfer", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ENERGY_ALLOCATION_BOUND", moduleName := "Zeta23.OPICAFollowup.NormFirstTransfer", shortName := "Zeta23.OPICAFollowup.energy_allocation_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ENERGY_ALLOCATION_RATE_LOWER", moduleName := "Zeta23.OPICAFollowup.NormFirstTransfer", shortName := "Zeta23.OPICAFollowup.energy_allocation_rate_lower", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_JOINT_RECOVERY_IFF", moduleName := "Zeta23.OPICAFollowup.JointObservation", shortName := "Zeta23.OPICAFollowup.joint_recovery_iff", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_JOINT_RECOVERY_OPTIMAL_NORM", moduleName := "Zeta23.OPICAFollowup.JointObservation", shortName := "Zeta23.OPICAFollowup.joint_recovery_optimal_norm", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_JOINT_RECOVERY_NOISE_BOUND", moduleName := "Zeta23.OPICAFollowup.JointObservation", shortName := "Zeta23.OPICAFollowup.joint_recovery_noise_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_APPROX_COMPATIBILITY_LEFT_NULL", moduleName := "Zeta23.OPICAFollowup.JointObservation", shortName := "Zeta23.OPICAFollowup.approx_compatibility_left_null", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_RECOVERY_SUBEXP_BUDGET", moduleName := "Zeta23.OPICAFollowup.JointObservation", shortName := "Zeta23.OPICAFollowup.recovery_subexp_budget", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LAURENT_COEFFICIENT_ERROR_BOUND", moduleName := "Zeta23.OPICAFollowup.RobustLaurent", shortName := "Zeta23.OPICAFollowup.laurent_coefficient_error_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LAURENT_OBSERVATION_SURVIVES", moduleName := "Zeta23.OPICAFollowup.RobustLaurent", shortName := "Zeta23.OPICAFollowup.laurent_observation_survives", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVEWORD_CONTOUR_CONSUMER", moduleName := "Zeta23.OPICAFollowup.RobustLaurent", shortName := "Zeta23.OPICAFollowup.nativeWord_contour_consumer", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SOURCE_PRODUCT_VERTICAL_BOUND", moduleName := "Zeta23.OPICAFollowup.SourceVerticalBounds", shortName := "Zeta23.OPICAFollowup.source_product_vertical_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZETA_LEFT_LINE_UNIFORM_BOUND", moduleName := "Zeta23.OPICAFollowup.ZetaLeftLineBounds", shortName := "Zeta23.OPICAFollowup.zeta_left_line_uniform_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FORWARDKERNEL_LEFT_CONTOUR_BUDGET", moduleName := "Zeta23.OPICAFollowup.ForwardLocalization", shortName := "Zeta23.OPICAFollowup.forwardKernel_left_contour_budget", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FORWARDKERNEL_DOUBLE_EXP_DECAY", moduleName := "Zeta23.OPICAFollowup.ForwardLocalization", shortName := "Zeta23.OPICAFollowup.forwardKernel_double_exp_decay", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_BINOMIAL_INVERSE_IDENTITY", moduleName := "Zeta23.OPICAFollowup.BalancedCoefficients", shortName := "Zeta23.OPICAFollowup.native_binomial_inverse_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_BALANCED_COEFF_DIVISOR_BOUND", moduleName := "Zeta23.OPICAFollowup.BalancedCoefficients", shortName := "Zeta23.OPICAFollowup.balanced_coeff_divisor_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_SLACK_NATIVE_DECOMPOSITION", moduleName := "Zeta23.OPICAFollowup.LogSlackBalance", shortName := "Zeta23.OPICAFollowup.log_slack_native_decomposition", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_SLACK_TYPEI_ERROR", moduleName := "Zeta23.OPICAFollowup.LogSlackBalance", shortName := "Zeta23.OPICAFollowup.log_slack_typeI_error", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FIXED_TWO_FACTOR_PREPARATION", moduleName := "Zeta23.OPICAFollowup.LogSlackBalance", shortName := "Zeta23.OPICAFollowup.fixed_two_factor_preparation", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_SLACK_BOTH_LOW_MASKS_SUBEXP", moduleName := "Zeta23.OPICAFollowup.MaskedNativeRate", shortName := "Zeta23.OPICAFollowup.log_slack_both_low_masks_subexp", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_SLACK_MASKED_ENERGY_RATE_DIFFERENCE", moduleName := "Zeta23.OPICAFollowup.MaskedNativeRate", shortName := "Zeta23.OPICAFollowup.log_slack_masked_energy_rate_difference", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_ZERO_COUNT_SUMMABILITY", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_zero_count_summability", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SOURCE_EXPLICIT_FORMULA", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_source_explicit_formula", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_ZERO_SUP_BOUNDS", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_zero_sup_bounds", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SOURCE_ORDER_UNIFORM_NORMS", moduleName := "Zeta23.OPICAFollowup.UniformSourceBounds", shortName := "Zeta23.OPICAFollowup.source_order_uniform_norms", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_FIELD_THETA_ENVELOPE", moduleName := "Zeta23.OPICAFollowup.UniformSourceBounds", shortName := "Zeta23.OPICAFollowup.native_field_theta_envelope", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_AUX_COMPLETION_ACTUAL_TRANSFORM", moduleName := "Zeta23.OPICAFollowup.AuxiliaryCompletions", shortName := "Zeta23.OPICAFollowup.aux_completion_actual_transform", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_AUX_COMPLETION_UNIFORM_DECAY", moduleName := "Zeta23.OPICAFollowup.AuxiliaryCompletions", shortName := "Zeta23.OPICAFollowup.aux_completion_uniform_decay", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_AUX_COMPLETION_RATIO_BOUNDS", moduleName := "Zeta23.OPICAFollowup.AuxiliaryCompletions", shortName := "Zeta23.OPICAFollowup.aux_completion_ratio_bounds", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_AUXILIARY_TOP_MOMENT", moduleName := "Zeta23.OPICAFollowup.MultiplicityTail", shortName := "Zeta23.OPICAFollowup.native_auxiliary_top_moment", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LAGUERRE_TAIL_NORM", moduleName := "Zeta23.OPICAFollowup.MultiplicityTail", shortName := "Zeta23.OPICAFollowup.laguerre_tail_norm", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_AUXILIARY_TAIL_RESIDUAL_LOWER", moduleName := "Zeta23.OPICAFollowup.MultiplicityTail", shortName := "Zeta23.OPICAFollowup.native_auxiliary_tail_residual_lower", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_TERMINAL_MEMORY_LOWER", moduleName := "Zeta23.OPICAFollowup.MultiplicityTail", shortName := "Zeta23.OPICAFollowup.native_terminal_memory_lower", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_FIXED_SOURCE_WINDOW_RATE", moduleName := "Zeta23.OPICAFollowup.NativeWindowRate", shortName := "Zeta23.OPICAFollowup.native_fixed_source_window_rate", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SLOW_SOURCE_WINDOW_RATE", moduleName := "Zeta23.OPICAFollowup.MovingSourceWindowRate", shortName := "Zeta23.OPICAFollowup.native_slow_source_window_rate", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_COMPLEX_LOCAL_MEASURE_EMBEDDING_FAITHFUL", moduleName := "Zeta23.OPICAFollowup.ComplexLocalMeasures", shortName := "Zeta23.OPICAFollowup.complex_local_measure_embedding_faithful", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_DILATED_COMB_FOURIER", moduleName := "Zeta23.OPICAFollowup.DilatedComb", shortName := "Zeta23.OPICAFollowup.dilated_comb_fourier", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_WEIGHTED_MIXTURE_EXISTS_FOURIER", moduleName := "Zeta23.OPICAFollowup.WeightedMixing", shortName := "Zeta23.OPICAFollowup.weighted_mixture_exists_fourier", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_WEIGHTED_MOBIUS_INVERSE", moduleName := "Zeta23.OPICAFollowup.WeightedMixing", shortName := "Zeta23.OPICAFollowup.weighted_mobius_inverse", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_WEIGHTED_MIXTURE_SHARP_GAP", moduleName := "Zeta23.OPICAFollowup.WeightedMixing", shortName := "Zeta23.OPICAFollowup.weighted_mixture_sharp_gap", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_WEIGHTED_GAP_LEAKAGE", moduleName := "Zeta23.OPICAFollowup.WeightedMixing", shortName := "Zeta23.OPICAFollowup.weighted_gap_leakage", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NEAR_GAP_MASS_BOUND", moduleName := "Zeta23.OPICAFollowup.NearGapLimits", shortName := "Zeta23.OPICAFollowup.near_gap_mass_bound", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NEAR_GAP_CONTROLLED_LIMIT_ZERO", moduleName := "Zeta23.OPICAFollowup.NearGapLimits", shortName := "Zeta23.OPICAFollowup.near_gap_controlled_limit_zero", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_DILATION_NEAR_GAP_FAMILY", moduleName := "Zeta23.OPICAFollowup.NearGapLimits", shortName := "Zeta23.OPICAFollowup.dilation_near_gap_family", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_DILATION_NORMALIZED_LIMIT_NOT_MEASURE", moduleName := "Zeta23.OPICAFollowup.NearGapLimits", shortName := "Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_RENORMALIZED_COPOISSON_TEMPERED_FAMILY", moduleName := "Zeta23.OPICAFollowup.RenormalizedCoPoisson", shortName := "Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_RENORMALIZED_COPOISSON_ORDER_ZERO", moduleName := "Zeta23.OPICAFollowup.RenormalizedCoPoisson", shortName := "Zeta23.OPICAFollowup.renormalized_copoisson_order_zero", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_MEASURE_EXACT_PROPERTIES", moduleName := "Zeta23.OPICAFollowup.RenormalizedCoPoisson", shortName := "Zeta23.OPICAFollowup.zero_measure_exact_properties", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_MEASURE_FIRST_CELL_SIGN", moduleName := "Zeta23.OPICAFollowup.RenormalizedCoPoisson", shortName := "Zeta23.OPICAFollowup.zero_measure_first_cell_sign", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FINITE_SUM_EULER_MACLAURIN_UNIFORM", moduleName := "Zeta23.OPICAFollowup.ProfileEulerMaclaurin", shortName := "Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_PROFILE_REGULAR_SELFDUAL", moduleName := "Zeta23.OPICAFollowup.ZeroProfiles", shortName := "Zeta23.OPICAFollowup.zero_profile_regular_selfdual", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_PROFILE_TAIL_AND_JUMPS", moduleName := "Zeta23.OPICAFollowup.ZeroProfiles", shortName := "Zeta23.OPICAFollowup.zero_profile_tail_and_jumps", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_UNITARY_FORM_IDENTITY", moduleName := "Zeta23.OPICAFollowup.LogFourierSobolev", shortName := "Zeta23.OPICAFollowup.log_unitary_form_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_LOG_FOURIER_PLANCHEREL", moduleName := "Zeta23.OPICAFollowup.LogFourierSobolev", shortName := "Zeta23.OPICAFollowup.log_fourier_plancherel", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_PROFILE_FORCED_EULER", moduleName := "Zeta23.OPICAFollowup.ForcedEuler", shortName := "Zeta23.OPICAFollowup.zero_profile_forced_euler", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ZERO_PROFILE_NOT_HOMOGENEOUS_OPERATOR_VECTOR", moduleName := "Zeta23.OPICAFollowup.ForcedEuler", shortName := "Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SAMPLING_GRAM_IDENTITY", moduleName := "Zeta23.OPICAFollowup.SamplingCompatibility", shortName := "Zeta23.OPICAFollowup.native_sampling_gram_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SAMPLING_FORM_POSITIVE", moduleName := "Zeta23.OPICAFollowup.SamplingCompatibility", shortName := "Zeta23.OPICAFollowup.native_sampling_form_positive", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_COPOISSON_ZERO_JETS_MEASURES", moduleName := "Zeta23.OPICAFollowup.CoPoissonJets", shortName := "Zeta23.OPICAFollowup.copoisson_zero_jets_measures", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_PROFILE_JET_CONFLUENT_DETERMINANT", moduleName := "Zeta23.OPICAFollowup.ConfluentProfiles", shortName := "Zeta23.OPICAFollowup.profile_jet_confluent_determinant", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FINITE_ZERO_JET_INDEPENDENT", moduleName := "Zeta23.OPICAFollowup.ConfluentProfiles", shortName := "Zeta23.OPICAFollowup.finite_zero_jet_independent", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FINITE_ZERO_SPAN_POSITIVE_ONLY_ZERO", moduleName := "Zeta23.OPICAFollowup.FiniteSpanSeparation", shortName := "Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FIXED_BASIS_NEGATIVE_MASS_BUDGET", moduleName := "Zeta23.OPICAFollowup.FiniteSpanSeparation", shortName := "Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FIRST_CELL_NEGATIVE_MASS_COST", moduleName := "Zeta23.OPICAFollowup.FirstCellCost", shortName := "Zeta23.OPICAFollowup.first_cell_negative_mass_cost", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SQUARE_FOURIER_DEFECT", moduleName := "Zeta23.OPICAFollowup.SquareDefect", shortName := "Zeta23.OPICAFollowup.square_fourier_defect", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SQUARE_DEFECT_ORIGIN_POSITIVE", moduleName := "Zeta23.OPICAFollowup.SquareDefect", shortName := "Zeta23.OPICAFollowup.square_defect_origin_positive", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SQUARE_NO_LATTICE_REPAIR", moduleName := "Zeta23.OPICAFollowup.SquareDefect", shortName := "Zeta23.OPICAFollowup.square_no_lattice_repair", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SQUARE_SELFDUAL_PROJECTION_FILLS_GAP", moduleName := "Zeta23.OPICAFollowup.SquareDefect", shortName := "Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SAWTOOTH_INTEGRABLE_FORCE_IDENTITY", moduleName := "Zeta23.OPICAFollowup.SawtoothForce", shortName := "Zeta23.OPICAFollowup.sawtooth_integrable_force_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SAWTOOTH_ACTUAL_MELLIN_FOURIER", moduleName := "Zeta23.OPICAFollowup.SawtoothForce", shortName := "Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SAWTOOTH_NORM_WEIGHTED_ZETA_MOMENT", moduleName := "Zeta23.OPICAFollowup.SawtoothForce", shortName := "Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ARITHMETIC_STIELTJES_HOLOMORPHIC", moduleName := "Zeta23.OPICAFollowup.WeightedSpectralMeasure", shortName := "Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ARITHMETIC_STIELTJES_SIGN_BUDGET", moduleName := "Zeta23.OPICAFollowup.WeightedSpectralMeasure", shortName := "Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_FORCED_RESOLVENT_UNIQUE", moduleName := "Zeta23.OPICAFollowup.NativeResolvent", shortName := "Zeta23.OPICAFollowup.native_forced_resolvent_unique", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SAMPLE_STIELTJES_IDENTITY", moduleName := "Zeta23.OPICAFollowup.NativeResolvent", shortName := "Zeta23.OPICAFollowup.native_sample_stieltjes_identity", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_PROFILE_SPECTRAL_NORMS", moduleName := "Zeta23.OPICAFollowup.NativeResolvent", shortName := "Zeta23.OPICAFollowup.native_profile_spectral_norms", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_GENERIC_FORCED_PROFILE_UNIQUE", moduleName := "Zeta23.OPICAFollowup.BoundaryAmplitude", shortName := "Zeta23.OPICAFollowup.generic_forced_profile_unique", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_GENERIC_BOUNDARY_AMPLITUDE", moduleName := "Zeta23.OPICAFollowup.BoundaryAmplitude", shortName := "Zeta23.OPICAFollowup.generic_boundary_amplitude", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_COUPLED_GRAM_COLLISION_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.coupled_gram_collision_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NORM_FIRST_STRICTLY_WEAKER_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.norm_first_strictly_weaker_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_HISTORY_RECOVERY_COST_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.history_recovery_cost_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FORCED_POSITIVE_GRAM_NONREAL_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FIXED_TWO_FACTOR_MASK_RATE_THETA", moduleName := "Zeta23.OPICAFollowup.Consumers", shortName := "Zeta23.OPICAFollowup.fixed_two_factor_mask_rate_theta", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_QUIET_BALANCED_OBSERVATION_IMPLIES_NATIVE_CUT", moduleName := "Zeta23.OPICAFollowup.Consumers", shortName := "Zeta23.OPICAFollowup.quiet_balanced_observation_implies_native_cut", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_STEP123_WORD_JET_CONSUMER", moduleName := "Zeta23.OPICAFollowup.Consumers", shortName := "Zeta23.OPICAFollowup.step123_word_jet_consumer", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ACTUAL_ZERO_MEASURE_SPAN_CONSUMER", moduleName := "Zeta23.OPICAFollowup.Consumers", shortName := "Zeta23.OPICAFollowup.actual_zero_measure_span_consumer", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_ACTUAL_FORCE_SAMPLING_CONSUMER", moduleName := "Zeta23.OPICAFollowup.Consumers", shortName := "Zeta23.OPICAFollowup.actual_force_sampling_consumer", sourceKind := "THEOREM" } : SourceCandidateQuery)]
  resolveSourceCandidates queries
  let env ← getEnv
  let mathematicalModules : Array String := #[
    "Zeta23.OPICAFollowup",
    "Zeta23.OPICAFollowup.AuxiliaryCompletions",
    "Zeta23.OPICAFollowup.BalancedCoefficients",
    "Zeta23.OPICAFollowup.BoundaryAmplitude",
    "Zeta23.OPICAFollowup.CoPoissonJets",
    "Zeta23.OPICAFollowup.ComplexLocalMeasures",
    "Zeta23.OPICAFollowup.ConfluentProfiles",
    "Zeta23.OPICAFollowup.Consumers",
    "Zeta23.OPICAFollowup.Counterexamples",
    "Zeta23.OPICAFollowup.DilatedComb",
    "Zeta23.OPICAFollowup.FiniteSpanSeparation",
    "Zeta23.OPICAFollowup.FirstCellCost",
    "Zeta23.OPICAFollowup.ForcedEuler",
    "Zeta23.OPICAFollowup.ForwardLocalization",
    "Zeta23.OPICAFollowup.JointObservation",
    "Zeta23.OPICAFollowup.LogFourierSobolev",
    "Zeta23.OPICAFollowup.LogSlackBalance",
    "Zeta23.OPICAFollowup.MaskedNativeRate",
    "Zeta23.OPICAFollowup.MovingSourceWindowRate",
    "Zeta23.OPICAFollowup.MultiplicityTail",
    "Zeta23.OPICAFollowup.NativeExplicitFormula",
    "Zeta23.OPICAFollowup.NativeFilters",
    "Zeta23.OPICAFollowup.NativeResolvent",
    "Zeta23.OPICAFollowup.NativeSourceFamily",
    "Zeta23.OPICAFollowup.NativeSourceTransforms",
    "Zeta23.OPICAFollowup.NativeTransformationWords",
    "Zeta23.OPICAFollowup.NativeWindowRate",
    "Zeta23.OPICAFollowup.NearGapLimits",
    "Zeta23.OPICAFollowup.NormFirstTransfer",
    "Zeta23.OPICAFollowup.ProfileEulerMaclaurin",
    "Zeta23.OPICAFollowup.RenormalizedCoPoisson",
    "Zeta23.OPICAFollowup.RobustLaurent",
    "Zeta23.OPICAFollowup.SamplingCompatibility",
    "Zeta23.OPICAFollowup.SawtoothForce",
    "Zeta23.OPICAFollowup.SourceVerticalBounds",
    "Zeta23.OPICAFollowup.SquareDefect",
    "Zeta23.OPICAFollowup.UniformSourceBounds",
    "Zeta23.OPICAFollowup.Validation",
    "Zeta23.OPICAFollowup.WeightedMixing",
    "Zeta23.OPICAFollowup.WeightedSpectralMeasure",
    "Zeta23.OPICAFollowup.ZeroProfiles",
    "Zeta23.OPICAFollowup.ZetaLeftLineBounds"]
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let definingModule := env.allImportedModuleNames[index.toNat]!
      if mathematicalModules.contains definingModule.toString && !name.isInternal && !isPrivateName name then
        -- Lean may cache generated equations or congruence theorems under the
        -- reused definition's original namespace. Include them in every audit.
        unless name.toString.startsWith "Zeta23.OPICAFollowup." ||
            (name.toString.endsWith ".congr_simp" && opicaKind info == "THEOREM") ||
            (reservedEquationOrigin? env name info).isSome do
          throwError "Public mathematical declaration escaped OPICA namespace: {name} in {definingModule}"
        names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "OPICA public namespace is empty"
  for name in names do
    let info ← getConstInfo name
    let some index := env.getModuleIdxFor? name
      | throwError "OPICA declaration has no defining imported module: {name}"
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !moduleName.toString.startsWith "Zeta23.OPICAFollowup" then
      throwError "OPICA declaration escaped its expected module namespace: {name} in {moduleName}"
    let typeDag ← liftIO <| OpicaTypeExprExport.exportType info.type
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "OPICA unadmitted mathematical axiom: {name} uses {ax}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    if let some origin := reservedEquationOrigin? env name info then
      liftIO <| IO.println s!"OPICA_FOLLOWUP_GENERATED_EQUATION\t{name}\t{origin}"
    liftIO <| IO.println s!"OPICA_FOLLOWUP_DECL\t{name}\t{moduleName}\t{opicaKind info}\t{typeDag}\t{axiomText}"
    match info with
    | .inductInfo data =>
      for ctor in data.ctors do
        let ctorInfo ← getConstInfo ctor
        let ctorType ← liftIO <| OpicaTypeExprExport.exportType ctorInfo.type
        liftIO <| IO.println s!"OPICA_FOLLOWUP_CONSTRUCTOR\t{name}\t{ctor}\t{ctorType}"
    | _ => pure ()
  liftIO <| IO.println s!"OPICA_FOLLOWUP_PUBLIC_COUNT\t{names.size}"
  FollowupDependencyExport.exportDependencies names
  liftIO <| IO.println s!"OPICA_FOLLOWUP_COMPLETE\t{names.size}"

end Zeta23.RHRC
