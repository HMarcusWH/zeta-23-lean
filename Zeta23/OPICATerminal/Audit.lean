import Lean

open Lean Elab Command
namespace Zeta23.OPICATerminal.Audit

def structuralDependencies : ConstantInfo → List Name
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all
  | _ => []

/-- Walk theorem values, opaque values, definitions, types and inductive links,
    not merely imported module names or pretty-printed theorem statements. -/
def closure (root : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let mut seen : NameSet := {}
  let mut pending := #[root]
  seen := seen.insert root
  let mut i := 0
  while i < pending.size do
    let n := pending[i]!
    i := i+1
    let some info := env.find? n
      | throwError "missing declaration in dependency closure: {n}"
    let mut used := info.type.getUsedConstantsAsSet
    match info.value? (allowOpaque := true) with
    | some v => used := used.merge v.getUsedConstantsAsSet
    | none =>
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        throwError "uninspectable declaration value in dependency closure: {n}"
      | _ => pure ()
    for d in used.toList ++ structuralDependencies info do
      unless seen.contains d do
        seen := seen.insert d
        pending := pending.push d
  return pending

def banned (s : String) : Bool :=
  s.startsWith "UpperTheory.FinalTheorems." ||
  s.startsWith "UpperTheory.riemannHypothesis_of_everyCharacter" ||
  s.startsWith "UpperTheory.zeta_ne_zero_of_everyCharacter" ||
  s.startsWith "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_" ||
  s.endsWith "_of_riemannHypothesis" ||
  ["UpperTheory.Top.zeroFreeAll_of_topG",
   "UpperTheory.Top.zero_free_all_of_green_v_win",
   "UpperTheory.Top.every_character_of_green_v_win",
   "UpperTheory.Top.plugWin", "UpperTheory.Top.plugAll",
   "UpperTheory.Lit.everyE₂",
   "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
   "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
   "Zeta23.OPICARound4.ArithmeticFrontier.momentSliceLowerBounds_zero_of_riemannHypothesis",
   "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_riemannHypothesis",
   "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_bounds"].contains s

/-- Positive module-origin allowlist for native roots. Original analytic modules
    are precisely the 27 proof-body-identical sources in the pinned manifest,
    not a blanket allowance for the original arithmetic repository. -/
def originalAnalyticModules : List String :=
  ["Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleAsym",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauTails",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauKernelMax",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindowIneq",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleReLe",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCoeff",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauNearest",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauGrowthContra",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.kernelIntegral",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.IteratedDerivLaplace",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.measurableGchi",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiGrowth",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiConj",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp"]

def inModuleFamily (m pfx : String) : Bool :=
  m == pfx || m.startsWith (pfx ++ ".")

def nativeOriginAllowed (m : String) : Bool :=
  originalAnalyticModules.contains m ||
    ["Zeta23", "Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop",
     "Qq", "ProofWidgets", "Plausible", "ImportGraph", "Cli", "Lake",
     "LeanSearchClient"].any (fun pfx => inModuleFamily m pfx)

def forbiddenOrigin (m : String) : Bool :=
  ["Main", "Statements", "Challenge", "Solution",
   "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion",
   "Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter"].contains m

def supplierName (s : String) : Bool :=
  ["UpperTheory", "Formalism", "GlobalTheory", "PositivityTheory", "ReciprocityTheory",
   "OPICATerminalSupplier", "OPICAR2Original", "SelfIntersectionVolumeEstimates"].any
    (fun pfx => inModuleFamily s pfx)

def audit (root : Name) (required : List Name) (nativeOnly : Bool)
    (excluded : List Name := []) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "terminal root {root} has forbidden axiom {ax}"
  let deps ← liftTermElabM (closure root)
  let env := (← getEnv).setExporting false
  let mut rows : Array Json := #[]
  for n in deps do
    let s := n.toString
    if s == "sorryAx" || banned s || excluded.contains n then
      throwError "forbidden terminal dependency: {root} -> {n}"
    let some decl := env.find? n
      | throwError "missing audited declaration: {root} -> {n}"
    if let .axiomInfo _ := decl then
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
        throwError "forbidden axiom in structural closure: {root} -> {n}"
    let some idx := env.getModuleIdxFor? n
      | throwError "unknown imported declaration origin: {root} -> {n}"
    let some moduleName := env.header.moduleNames[idx.toNat]?
      | throwError "invalid declaration origin index: {root} -> {n}"
    let m := moduleName.toString
    if forbiddenOrigin m then
      throwError "forbidden origin module in {root}: {n} from {m}"
    if nativeOnly && (supplierName s || !nativeOriginAllowed m) then
      throwError "supplier contamination in {root}: {n} from {m}"
    rows := rows.push (Json.mkObj [("name", Json.str s), ("module", Json.str m)])
  for n in required do
    unless deps.contains n do
      throwError "required proof dependency absent: {root} -> {n}"
  let some rootInfo := env.find? root
    | throwError "missing root type: {root}"
  let typeConst := match rootInfo.type with
    | .const nm [] => nm.toString
    | _ => ""
  if ["Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied",
      "Zeta23.OPICATerminal.riemannHypothesis_step4_direct_crosscheck"].contains root.toString then
    unless rootInfo.type == mkConst (Name.mkSimple "RiemannHypothesis") do
      throwError "terminal root is not the exact stock RiemannHypothesis constant: {root}"
  let rootType ← liftTermElabM (Meta.ppExpr rootInfo.type)
  let receipt := Json.mkObj [
    ("schema", Json.str "OPICA_TERMINAL_DECLARATION_AUDIT_V2"),
    ("root", Json.str root.toString),
    ("root_type", Json.str (toString rootType)),
    ("root_type_expr", Json.str (reprStr rootInfo.type)),
    ("root_type_const", Json.str typeConst),
    ("axioms", Json.arr (axs.map (fun n => Json.str n.toString))),
    ("required", Json.arr (required.toArray.map (fun n => Json.str n.toString))),
    ("excluded", Json.arr (excluded.toArray.map (fun n => Json.str n.toString))),
    ("native_only", toJson nativeOnly),
    ("constants", toJson deps.size),
    ("dependencies", Json.arr rows)]
  if let some dir ← liftIO (IO.getEnv "OPICA_TERMINAL_AUDIT_DIR") then
    let path : System.FilePath := dir
    liftIO <| IO.FS.createDirAll path
    liftIO <| IO.FS.writeFile (path / (root.toString ++ ".json")) (receipt.compress ++ "\n")
  liftIO <| IO.println s!"OPICA_TERMINAL_DEPENDENCY_AUDIT {root} constants={deps.size} nativeOnly={nativeOnly}"

end Zeta23.OPICATerminal.Audit
