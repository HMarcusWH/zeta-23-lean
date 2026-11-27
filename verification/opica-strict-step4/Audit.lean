import Zeta23.RHReference.CompactEnergyAdapter
import Zeta23.OPICANativeTerminal.AuditCore

/-! Strict candidate proof and source-origin checks. Verification only. -/

open Lean Elab Command
open Zeta23.RHReference
open Zeta23.OPICATerminal

namespace OPICAStrictAudit

private def donorModules : List String :=
  ["Zeta23.OPICATerminal.Analytic.CharFamily",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.GchiConj",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.GchiGrowth",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.IteratedDerivLaplace",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LFunctionConj",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauCauchy",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauCoeff",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauDichotomy",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauFinite",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauGrowthContra",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauKernelMax",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauNearest",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauPoleAsym",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LandauPoleReLe",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.LogDerivLocal",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.MellinRamp",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.WindowHypUOfWindowHyp",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.kernelIntegral",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.landauTails",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.landauWindow",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.landauWindowIneq",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.measurableGchi",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.mellinGchiModOne",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.mellinGchiOfNeOne",
   "Zeta23.OPICATerminal.Analytic.LandauTheorems.poleData",
   "Zeta23.OPICATerminal.Analytic.LandauZeroFreeCriterion",
   "Zeta23.OPICATerminal.Common",
   "Zeta23.OPICATerminal.DisplacementGrowth",
   "Zeta23.OPICATerminal.Energy",
   "Zeta23.OPICATerminal.LiteralEnergyGrowth",
   "Zeta23.OPICATerminal.PowerDetectorSupply",
   "Zeta23.OPICATerminal.SourceNormalization"]

private def originAllowed (origin : String) (nativeOnly : Bool) : Bool :=
  if origin.startsWith "Zeta23.OPICATerminal." then donorModules.contains origin
  else if origin.startsWith "Zeta23.OPICANativeTerminal." then false
  else OPICANativeTerminalAudit.permittedOrigin origin nativeOnly false false

private def refs (xs : List Name) : Json :=
  Json.arr (xs.map Name.toString |>.toArray.qsort (· < ·) |>.map Json.str)

private def audit (root : Name) (required direct : List Name)
    (nativeOnly exactRH writeEdges : Bool) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless OPICANativeTerminalAudit.allowedAxiom ax do
      throwError "forbidden strict axiom {root} -> {ax}"
  let members ← liftTermElabM (OPICANativeTerminalAudit.closure root)
  for n in required do
    unless members.contains n do throwError "strict dependency missing {root} -> {n}"
  let env := (← getEnv).setExporting false
  let some c := env.find? root | throwError "strict root missing {root}"
  let some value := c.value? (allowOpaque := true) | throwError "strict root value missing {root}"
  let directNames := value.getUsedConstantsAsSet
  for n in direct do
    unless directNames.contains n do throwError "strict direct proof edge missing {root} -> {n}"
  if exactRH then
    unless c.type == mkConst ``RiemannHypothesis do
      throwError "strict target must be exactly stock Mathlib RiemannHypothesis"
  let some dirString ← liftIO (IO.getEnv "OPICA_STRICT_AUDIT_DIR") |
    throwError "strict audit output directory missing"
  let dir : System.FilePath := dirString
  liftIO <| IO.FS.createDirAll dir
  let handle ← if writeEdges then
    some <$> liftIO (IO.FS.Handle.mk (dir / (root.toString ++ ".edges.jsonl")) .write)
    else pure none
  let mut audited : Array Json := #[]
  for n in members.qsort (fun a b => a.toString < b.toString) do
    if OPICANativeTerminalAudit.bannedName n.toString then
      throwError "forbidden endpoint in strict proof {root} -> {n}"
    let some ci := env.find? n | throwError "strict dependency missing {n}"
    if let .axiomInfo _ := ci then
      unless OPICANativeTerminalAudit.allowedAxiom n do
        throwError "forbidden structural axiom {n}"
    if n != root && ci.type == mkConst ``RiemannHypothesis then
      throwError "unconditional RH dependency {n}"
    let some idx := env.getModuleIdxFor? n | throwError "strict dependency origin missing {n}"
    let some dependencyModuleName := env.header.moduleNames[idx.toNat]? | throwError "bad origin {n}"
    unless originAllowed dependencyModuleName.toString nativeOnly do
      throwError "forbidden strict proof origin {dependencyModuleName}: {n}"
    audited := audited.push (Json.mkObj [("name", Json.str n.toString), ("module", Json.str dependencyModuleName.toString)])
    if let some f := handle then
      let valueRefs := (ci.value? (allowOpaque := true)).map (fun e => e.getUsedConstantsAsSet.toList)
      let row := Json.mkObj [("name", Json.str n.toString), ("module", Json.str dependencyModuleName.toString),
        ("type_refs", refs ci.type.getUsedConstantsAsSet.toList),
        ("value_refs", refs (valueRefs.getD [])),
        ("structural_refs", refs (OPICANativeTerminalAudit.structural ci))]
      liftIO <| f.putStrLn row.compress
  if let some f := handle then liftIO f.flush
  let pp ← liftTermElabM (Meta.ppExpr c.type)
  let output := Json.mkObj [("root", Json.str root.toString), ("type", Json.str pp.pretty),
    ("type_expr", Json.str (reprStr c.type)), ("axioms", refs axs.toList),
    ("dependencies", Json.arr audited), ("required", refs required), ("direct", refs direct),
    ("native_only", toJson nativeOnly), ("exact_rh", toJson exactRH),
    ("has_edges", toJson writeEdges), ("count", toJson audited.size)]
  liftIO <| IO.FS.writeFile (dir / (root.toString ++ ".json")) (output.compress ++ "\n")
  logInfo m!"STRICT_ROOT_PASS {root} {audited.size}"

set_option maxHeartbeats 0 in
run_cmd
  audit ``bothParityPowerComparison_proved
    [``eventual_literalGEnergy_ge_rpow, ``Deduction.landau_window, ``Deduction.poleData]
    [] true false false
  audit ``native_literal_ramp_fixed_gap_transfer
    [``literalRamp_fixed_gap_transfer, ``rightLinePerron_eq_native_sum,
     ``riemannZeta_fixedGap_vertical_logDerivative_bound,
     ``literalPerron_horizontal_decay_of_fixedGap]
    [``literalRamp_fixed_gap_transfer] true false false
  audit ``riemannHypothesis_of_c1_through_generated_pair
    [``generated_pair_excludes_c1, ``generated_pair_eventually_refutes_slice_bounds,
     ``Zeta23.ExceptionalZero.exists_generatedStep123CompleteOutput]
    [``generated_pair_excludes_c1] true false false
  audit ``riemannHypothesis_compact_literal_ramp_candidate
    [``Zeta23Arithmetic.Principal.principal_fixed_strip, ``eventually_primeError_le_rpow,
     ``bothParityPowerComparison_proved, ``eventual_literalGEnergy_ge_rpow,
     ``Deduction.landau_window, ``Deduction.poleData,
     ``native_literal_ramp_fixed_gap_transfer, ``literalRamp_fixed_gap_transfer,
     ``rightLinePerron_eq_native_sum, ``fixedGap_native_literalG_power_bound,
     ``riemannZeta_fixedGap_vertical_logDerivative_bound,
     ``literalPerron_horizontal_decay_of_fixedGap, ``literal_energy_eventually_le,
     ``eventually_scaled_energy_small, ``c1_of_fixed_energy_upper,
     ``compact_energy_reference_of_fixed_strip, ``riemannHypothesis_of_c1_through_generated_pair,
     ``generated_pair_excludes_c1, ``generated_pair_eventually_refutes_slice_bounds]
    [``Zeta23Arithmetic.Principal.principal_fixed_strip, ``bothParityPowerComparison_proved,
     ``native_literal_ramp_fixed_gap_transfer, ``compact_energy_reference_of_fixed_strip]
    false true true

end OPICAStrictAudit
