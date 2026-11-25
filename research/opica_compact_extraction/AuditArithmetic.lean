import New.ArithmeticOnly
import Lean

/-!
Source extraction research only. No RH/GRH endpoint imported. Separate from native #317.
Compiler type/value/inductive dependency export; not an independent checker.
-/
open Lean Elab Command Filter
namespace OPICACompactAudit

-- Independent literal contract checks, not just names.
example (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) :=
  eventually_primeError_le_rpow P h

example {P : Parameters} {D : Data P} :
    D.m * D.remainder ≤ D.logB ^ 2 * D.budget :=
  star_inequality

def structural (c : ConstantInfo) : List Name :=
  match c with
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all
  | _ => []

def dependencies (c : ConstantInfo) : CoreM (NameSet × NameSet × List Name) := do
  let t := c.type.getUsedConstantsAsSet
  let v ← match c.value? (allowOpaque := true) with
    | some e => pure e.getUsedConstantsAsSet
    | none =>
      match c with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        throwError "uninspectable value: {c.name}"
      | _ => pure ({} : NameSet)
  return (t, v, structural c)

def bannedName (s : String) : Bool :=
  ["New.grh", "New.zeros_on_line", "New.zeta_zeros_on_line",
   "riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
   "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive", "sorryAx"].contains s ||
  s.endsWith "_of_riemannHypothesis" || s.endsWith ".riemannHypothesis"

def bannedModule (s : String) : Bool :=
  ["Main", "Statements", "Challenge", "New.Main", "New.Reduction.OneSidedBound"].contains s

def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

def closure (root : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let mut seen : NameSet := {}
  seen := seen.insert root
  let mut pending := #[root]
  let mut i := 0
  while i < pending.size do
    let n := pending[i]!
    i := i + 1
    let some c := env.find? n | throwError "missing declaration: {n}"
    let (t,v,s) ← dependencies c
    for d in (t.merge v).toList ++ s do
      unless seen.contains d do
        seen := seen.insert d
        pending := pending.push d
  return pending

def names (xs : List Name) : Json :=
  Json.arr (xs.toArray.map (fun n => Json.str n.toString))

def audit : CommandElabM Unit := do
  let roots : List Name :=
    [``star_inequality, ``eventually_primeError_le_rpow,
     ``entireL_ne_zero_of_primeError_le, ``Data.short_forms,
     ``Data.enough_forms, ``Data.integral_forms_long,
     ``Data.exists_family_covolumeSq_le, ``exists_isFitFamily,
     ``denominatorLe_rowBudget, ``ribet_columns,
     ``exists_ribet_element_cramer, ``exists_corepresenting_coords,
     ``exists_isPencil, ``exists_mFoldTwist_selmerLengthLe,
     ``sphericalCompat_std]
  let env := (← getEnv).setExporting false
  let some out ← liftIO (IO.getEnv "OPICA_COMPACT_AUDIT_DIR") |
    throwError "OPICA_COMPACT_AUDIT_DIR is required"
  let dir : System.FilePath := out
  liftIO <| IO.FS.createDirAll dir
  let mut all : NameSet := {}
  let mut inventory : Array Json := #[]
  for root in roots do
    let axs ← Lean.collectAxioms root
    for ax in axs do
      unless allowedAxiom ax do throwError "forbidden axiom: {root} -> {ax}"
    let ns ← liftTermElabM (closure root)
    for n in ns do
      if bannedName n.toString then throwError "forbidden endpoint: {root} -> {n}"
      all := all.insert n
    let some c := env.find? root | throwError "missing root: {root}"
    let pp ← liftTermElabM (Meta.ppExpr c.type)
    let receipt := Json.mkObj [
      ("root", Json.str root.toString), ("type", Json.str (toString pp)),
      ("type_expr", Json.str (reprStr c.type)),
      ("axioms", names axs.toList), ("closure_count", toJson ns.size),
      ("closure", names ns.toList)]
    liftIO <| IO.FS.writeFile (dir / (root.toString ++ ".json")) (receipt.compress ++ "\n")
    inventory := inventory.push (Json.mkObj [("root", Json.str root.toString),
      ("count", toJson ns.size)])
    liftIO <| IO.println s!"COMPACT_ROOT_CLOSURE {root} {ns.size}"
  let h ← liftIO <| IO.FS.Handle.mk (dir / "declaration_edges.jsonl") .write
  for n in all.toList do
    let some c := env.find? n | throwError "missing union member {n}"
    if let .axiomInfo _ := c then
      unless allowedAxiom n do throwError "forbidden structural axiom {n}"
    let some idx := env.getModuleIdxFor? n | throwError "missing origin {n}"
    let some origin := env.header.moduleNames[idx.toNat]? | throwError "bad origin index {n}"
    if bannedModule origin.toString then throwError "forbidden origin {origin}: {n}"
    let (t,v,s) ← liftTermElabM (dependencies c)
    let row := Json.mkObj [
      ("name", Json.str n.toString), ("origin", Json.str origin.toString),
      ("type_refs", names t.toList), ("value_refs", names v.toList),
      ("structural_refs", names s)]
    liftIO <| h.putStrLn row.compress
  liftIO <| h.flush
  let summary := Json.mkObj [("schema", Json.str "OPICA_COMPACT_ARITHMETIC_GRAPH_V1"),
    ("roots", Json.arr inventory), ("union_count", toJson all.toList.length),
    ("claim", Json.str "RH_OPEN"), ("native_integration", Json.str "NOT_RUN"),
    ("independent_checker", Json.str "NOT_RUN")]
  liftIO <| IO.FS.writeFile (dir / "SUMMARY.json") (summary.compress ++ "\n")
  liftIO <| IO.println s!"COMPACT_ARITHMETIC_GRAPH_PASS union={all.toList.length}"

end OPICACompactAudit

set_option maxHeartbeats 0 in
run_cmd do
  OPICACompactAudit.audit
