import Lean

/-! Verification-only dependency inspection. Never imported by a proof root.

The original source contains mixed modules: a module may define the arithmetic
interface and also an unused zero-exclusion endpoint. We inspect declaration
types, proof values, opaque values, constructors, and recursor rules. Imports
alone are not treated as proof dependencies.
-/

open Lean Elab Command

namespace DirectWindowAudit

inductive Role where
  | supplier | native | terminal | fixture
  deriving BEq

def structural (c : ConstantInfo) : List Name :=
  match c with
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all ++ i.rules.flatMap
      (fun r => r.ctor :: r.rhs.getUsedConstantsAsSet.toList)
  | _ => []

def closure (root : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let mut seen : NameSet := {}
  seen := seen.insert root
  let mut todo := #[root]
  let mut i := 0
  while i < todo.size do
    let n := todo[i]!
    i := i + 1
    let some c := env.find? n | throwError "missing proof dependency {n}"
    let mut used := c.type.getUsedConstantsAsSet
    match c.value? (allowOpaque := true) with
    | some v => used := used.merge v.getUsedConstantsAsSet
    | none =>
      match c with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => throwError "uninspectable proof value {n}"
      | _ => pure ()
    for d in used.toList ++ structural c do
      unless seen.contains d do
        seen := seen.insert d
        todo := todo.push d
  return todo

def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

def bannedName (s : String) : Bool :=
  ["sorryAx", "riemannHypothesis", "riemannZeta_eq_zero_re",
   "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
   "LFunction_eq_zero_re_of_isPrimitive", "New.grh", "New.zeros_on_line",
   "New.zeta_zeros_on_line", "UpperTheory.Top.zeroFreeAll_of_topG",
   "UpperTheory.Top.zero_free_all_of_green_v_win",
   "UpperTheory.Top.every_character_of_green_v_win",
   "UpperTheory.Top.plugAll", "UpperTheory.Top.plugWin",
   "UpperTheory.Comparison₂.formB", "Formalism.HC.level_of_tiedWin",
   "Formalism.HC.level_of_tiedAll", "Formalism.HC.zeroFreeOn_of_tiedWin",
   "Formalism.HC.zeroFreeOn_of_tiedWin_cyc", "Formalism.HC.zeroFreeOn_of_tiedAll",
   "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds",
   "Zeta23.RHReference.riemannHypothesis_compact_literal_ramp_candidate"].contains s ||
  s.startsWith "UpperTheory.FinalTheorems." ||
  s.startsWith "Zeta23Arithmetic." ||
  s.startsWith "Zeta23.RHReference.Perron." ||
  s.startsWith "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_"

def originalOrigin (s : String) : Bool :=
  ["BuildAid", "CompanionTheory", "Development", "Formalism", "GroundTheory",
   "Lemmata", "PositivityTheory", "ReciprocityTheory", "Supplements"].any
    (fun p => s == p || s.startsWith (p ++ "."))

def analyticOrigin (s : String) : Bool :=
  ["Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiConj",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiGrowth",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.IteratedDerivLaplace",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCoeff",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauGrowthContra",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauKernelMax",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauNearest",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleAsym",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleReLe",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.kernelIntegral",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauTails",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindowIneq",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.measurableGchi",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData",
   "Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion"].contains s

def permittedOrigin (s : String) (role : Role) : Bool :=
  let external := ["Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli", "Lake"].any
      (fun p => s == p || s.startsWith (p ++ "."))
  let native := s.startsWith "Zeta23." &&
    !s.startsWith "Zeta23.OPICANativeTerminal." &&
    !s.startsWith "Zeta23.RHReference.Perron." &&
    !["Zeta23.RHReference.CompactEnergyAdapter", "Zeta23.RHReference.CompactEnergyClosure"].contains s
  let supplier := s.startsWith "Zeta23WindowArithmetic."
  external ||
    (role == .supplier && (supplier || originalOrigin s)) ||
    (role == .native && (native || analyticOrigin s)) ||
    (role == .terminal && (native || supplier || originalOrigin s)) ||
    (role == .fixture && s == "DirectWindowAudit.SmokeFixtures")

def refs (xs : List Name) : Json :=
  Json.arr (xs.map Name.toString |>.toArray.qsort (· < ·) |>.map Json.str)

def audit (root : Name) (role : Role) (required direct : List Name)
    (expectedType : Option Name := none) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless allowedAxiom ax do throwError "forbidden axiom {root} -> {ax}"
  let members ← liftTermElabM (closure root)
  for n in required do
    unless members.contains n do throwError "required dependency missing {root} -> {n}"
  let env := (← getEnv).setExporting false
  let some c := env.find? root | throwError "missing proof root {root}"
  let some value := c.value? (allowOpaque := true) | throwError "missing root proof value {root}"
  for n in direct do
    unless value.getUsedConstantsAsSet.contains n do
      throwError "required direct proof edge missing {root} -> {n}"
  if let some expected := expectedType then
    unless c.type == mkConst expected do throwError "wrong exact root type {root}; expected {expected}"
  let some out ← liftIO (IO.getEnv "DIRECT_WINDOW_AUDIT_DIR") |
    throwError "DIRECT_WINDOW_AUDIT_DIR must name a fresh output directory"
  let dir : System.FilePath := out
  liftIO <| IO.FS.createDirAll dir
  let edges ← liftIO <| IO.FS.Handle.mk (dir / (root.toString ++ ".edges.jsonl")) .write
  for n in members.qsort (fun a b => a.toString < b.toString) do
    if bannedName n.toString then throwError "forbidden endpoint {root} -> {n}"
    let some ci := env.find? n | throwError "missing dependency {n}"
    if let .axiomInfo _ := ci then
      unless allowedAxiom n do throwError "forbidden structural axiom {n}"
    -- Definitional aliases of the stock target are rejected as well. This is not
    -- an automatic decision procedure for all logically equivalent RH statements.
    if n != root && env.contains (Name.mkSimple "RiemannHypothesis") then
      let isRH ← liftTermElabM <| Meta.isDefEq ci.type (mkConst (Name.mkSimple "RiemannHypothesis"))
      if isRH then throwError "unconditional RH dependency {n}"
    let some idx := env.getModuleIdxFor? n | throwError "missing origin {n}"
    let some origin := env.header.moduleNames[idx.toNat]? | throwError "invalid origin {n}"
    unless permittedOrigin origin.toString role do throwError "forbidden origin {origin}: {n}"
    let vv := (ci.value? (allowOpaque := true)).map (fun e => e.getUsedConstantsAsSet.toList)
    let row := Json.mkObj [("name", Json.str n.toString), ("module", Json.str origin.toString),
      ("type_refs", refs ci.type.getUsedConstantsAsSet.toList),
      ("value_refs", refs (vv.getD [])), ("structural_refs", refs (structural ci))]
    liftIO <| edges.putStrLn row.compress
  liftIO edges.flush
  let pp ← liftTermElabM (Meta.ppExpr c.type)
  let roleName := match role with
    | .supplier => "supplier" | .native => "native" | .terminal => "terminal" | .fixture => "fixture"
  let result := Json.mkObj [("schema", Json.str "DIRECT_WINDOW_AUDIT_V1"),
    ("root", Json.str root.toString), ("role", Json.str roleName),
    ("type", Json.str pp.pretty), ("type_expr", Json.str (reprStr c.type)),
    ("axioms", refs axs.toList), ("required", refs required), ("direct", refs direct),
    ("count", toJson members.size), ("complete_structural_edges", Json.bool true)]
  liftIO <| IO.FS.writeFile (dir / (root.toString ++ ".json")) (result.compress ++ "\n")
  logInfo m!"DIRECT_WINDOW_ROOT_PASS {roleName} {root} {members.size}"

end DirectWindowAudit
