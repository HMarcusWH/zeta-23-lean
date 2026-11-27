import Lean

/-! Verification-only code, never imported by the terminal proof. -/
open Lean Elab Command
namespace OPICANativeTerminalAudit

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
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        throwError "uninspectable value {n}"
      | _ => pure ()
    for d in used.toList ++ structural c do
      unless seen.contains d do
        seen := seen.insert d
        todo := todo.push d
  return todo

def bannedName (s : String) : Bool :=
  ["New.grh", "New.zeros_on_line", "New.zeta_zeros_on_line",
   "riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
   "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive", "sorryAx"].contains s ||
  s.endsWith "_of_riemannHypothesis" ||
  s.startsWith "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_" ||
  s.startsWith "UpperTheory." || s.startsWith "OPICATerminalSupplier."

def bannedModule (s : String) : Bool :=
  ["Main","Statements","Challenge","New.Main","New.Reduction.OneSidedBound","Solution"].contains s ||
  ["Zeta23Arithmetic.New.Main", "Zeta23Arithmetic.Statements", "Zeta23Arithmetic.Main",
    "Zeta23Arithmetic.Challenge", "Zeta23Arithmetic.New.Reduction.OneSidedBound"].contains s ||
  s.startsWith "Zeta23.OPICATerminal." || s.startsWith "Development." ||
  s == "Zeta23.OPICANativeTerminal.AuditCore" ||
  s.startsWith "Challenge." || s.startsWith "Solution." ||
  s == "Lib" || s.startsWith "Lib." || s == "New" || s.startsWith "New."

def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

def supplierOrigin (m : String) : Bool :=
  m == "Zeta23Arithmetic" || m.startsWith "Zeta23Arithmetic."

def nativeOrigin (m : String) : Bool :=
  m == "Zeta23" || m.startsWith "Zeta23."

def permittedOrigin (m : String) (nativeOnly arithmeticOnly allowSmokeFixtures : Bool) : Bool :=
  !bannedModule m &&
  (!nativeOnly || !supplierOrigin m) &&
  (!arithmeticOnly || !nativeOrigin m) &&
  ((allowSmokeFixtures && m == "AuditSmokeFixtures") ||
    ["Zeta23", "Zeta23Arithmetic", "Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop",
      "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli", "Lake"].any
        (fun p => m == p || m.startsWith (p ++ ".")))

def audit (root : Name) (required : List Name) (nativeOnly : Bool := false)
    (expectedType : Option Name := none) (withEdges : Bool := false)
    (arithmeticOnly : Bool := false) (allowSmokeFixtures : Bool := false) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless allowedAxiom ax do throwError "forbidden axiom {root} -> {ax}"
  let deps ← liftTermElabM (closure root)
  let env := (← getEnv).setExporting false
  let some outputDir ← liftIO (IO.getEnv "OPICA_NATIVE_TERMINAL_AUDIT_DIR") |
    throwError "audit output required"
  let dir : System.FilePath := outputDir
  liftIO <| IO.FS.createDirAll dir
  let edgeHandle ← if withEdges then
    some <$> liftIO (IO.FS.Handle.mk (dir / (root.toString ++ ".edges.jsonl")) .write)
    else pure none
  let mut rows : Array Json := #[]
  for n in deps do
    if bannedName n.toString then throwError "forbidden endpoint {root} -> {n}"
    let some c := env.find? n | throwError "missing member {n}"
    if let .axiomInfo _ := c then
      unless allowedAxiom n do throwError "forbidden structural axiom {n}"
    let some idx := env.getModuleIdxFor? n | throwError "missing module index {n}"
    let some moduleOriginName := env.header.moduleNames[idx.toNat]? | throwError "bad origin {n}"
    let m := moduleOriginName.toString
    unless permittedOrigin m nativeOnly arithmeticOnly allowSmokeFixtures do
      throwError "forbidden module origin {m}: {n}"
    rows := rows.push (Json.mkObj [("name", Json.str n.toString), ("module", Json.str m)])
    if let some handle := edgeHandle then
      let tv := c.type.getUsedConstantsAsSet
      let vv := (c.value? (allowOpaque := true)).map (fun e => e.getUsedConstantsAsSet) |>.getD ({} : NameSet)
      let names (xs : List Name) := Json.arr (xs.toArray.map (fun nm => Json.str nm.toString))
      let edge := Json.mkObj [("name", Json.str n.toString), ("module", Json.str m),
        ("type_refs", names tv.toList), ("value_refs", names vv.toList),
        ("structural_refs", names (structural c))]
      liftIO <| handle.putStrLn edge.compress
  if let some handle := edgeHandle then liftIO handle.flush
  for n in required do
    unless deps.contains n do throwError "required proof dependency missing {root} -> {n}"
  let some c := env.find? root | throwError "missing root type {root}"
  if let some expected := expectedType then
    unless c.type == mkConst expected do throwError "wrong literal root type {root}, expected {expected}"
  let pp ← liftTermElabM (Meta.ppExpr c.type)
  let receipt := Json.mkObj [("root", Json.str root.toString),
    ("type", Json.str (toString pp)), ("type_expr", Json.str (reprStr c.type)),
    ("axioms", Json.arr (axs.map (fun n => Json.str n.toString))),
    ("dependencies", Json.arr rows), ("required", Json.arr (required.toArray.map (fun n => Json.str n.toString))),
    ("native_only", toJson nativeOnly), ("arithmetic_only", toJson arithmeticOnly),
    ("smoke_fixture", toJson allowSmokeFixtures), ("with_edges", toJson withEdges), ("count", toJson deps.size)]
  liftIO <| IO.FS.createDirAll dir
  liftIO <| IO.FS.writeFile (dir / (root.toString ++ ".json")) (receipt.compress ++ "\n")
  liftIO <| IO.println s!"NATIVE_TERMINAL_ROOT_PASS {root} {deps.size}"

end OPICANativeTerminalAudit
