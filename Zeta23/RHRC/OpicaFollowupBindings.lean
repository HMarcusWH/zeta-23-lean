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
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_ZERO_COUNT_SUMMABILITY", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_zero_count_summability", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_SOURCE_EXPLICIT_FORMULA", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_source_explicit_formula", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_ZERO_SUP_BOUNDS", moduleName := "Zeta23.OPICAFollowup.NativeExplicitFormula", shortName := "Zeta23.OPICAFollowup.native_zero_sup_bounds", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_SOURCE_ORDER_UNIFORM_NORMS", moduleName := "Zeta23.OPICAFollowup.UniformSourceBounds", shortName := "Zeta23.OPICAFollowup.source_order_uniform_norms", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NATIVE_FIELD_THETA_ENVELOPE", moduleName := "Zeta23.OPICAFollowup.UniformSourceBounds", shortName := "Zeta23.OPICAFollowup.native_field_theta_envelope", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_COUPLED_GRAM_COLLISION_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.coupled_gram_collision_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_NORM_FIRST_STRICTLY_WEAKER_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.norm_first_strictly_weaker_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_HISTORY_RECOVERY_COST_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.history_recovery_cost_control", sourceKind := "THEOREM" } : SourceCandidateQuery),
    ({ sourceId := "OPICA_FOLLOWUP_FORCED_POSITIVE_GRAM_NONREAL_CONTROL", moduleName := "Zeta23.OPICAFollowup.Counterexamples", shortName := "Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control", sourceKind := "THEOREM" } : SourceCandidateQuery)]
  resolveSourceCandidates queries
  let env ← getEnv
  let mathematicalModules : Array String := #[
    "Zeta23.OPICAFollowup.BalancedCoefficients",
    "Zeta23.OPICAFollowup.Counterexamples",
    "Zeta23.OPICAFollowup.ForwardLocalization",
    "Zeta23.OPICAFollowup.JointObservation",
    "Zeta23.OPICAFollowup.NativeExplicitFormula",
    "Zeta23.OPICAFollowup.NativeFilters",
    "Zeta23.OPICAFollowup.NativeSourceFamily",
    "Zeta23.OPICAFollowup.NativeSourceTransforms",
    "Zeta23.OPICAFollowup.NativeTransformationWords",
    "Zeta23.OPICAFollowup.NormFirstTransfer",
    "Zeta23.OPICAFollowup.RobustLaurent",
    "Zeta23.OPICAFollowup.SourceVerticalBounds",
    "Zeta23.OPICAFollowup.UniformSourceBounds",
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
