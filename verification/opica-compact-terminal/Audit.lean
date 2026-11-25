import Zeta23.OPICACompactTerminal.Terminal
import Lean

open Lean Elab Command Filter
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICACompactTerminal

namespace OPICACompactTerminalAudit

-- Explicit expected types, not a proof by name.
example : CofinalMomentSliceVanishingErrorBounds := step4C1_compact_arithmetic
example : RiemannHypothesis := riemannHypothesis_step4_compact_arithmetic
example (L : ℝ) (hL : 0 < L) :
    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 ∧
    OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 :=
  both_parity_zero_floor_arithmetic L hL

def structural (c : ConstantInfo) : List Name :=
  match c with
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all
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
  s.startsWith "Zeta23.OPICATerminal." || s.startsWith "Development."

def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

def audit (root : Name) (required : List Name) (nativeOnly : Bool := false) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless allowedAxiom ax do throwError "forbidden axiom {root} -> {ax}"
  let deps ← liftTermElabM (closure root)
  let env := (← getEnv).setExporting false
  let mut rows : Array Json := #[]
  for n in deps do
    if bannedName n.toString then throwError "forbidden endpoint {root} -> {n}"
    let some c := env.find? n | throwError "missing member {n}"
    if let .axiomInfo _ := c then
      unless allowedAxiom n do throwError "forbidden structural axiom {n}"
    let some idx := env.getModuleIdxFor? n | throwError "missing module index {n}"
    let some origin := env.header.moduleNames[idx.toNat]? | throwError "bad origin {n}"
    let m := origin.toString
    if bannedModule m then throwError "forbidden origin {m}: {n}"
    if nativeOnly && (m == "Lib" || m.startsWith "Lib." || m == "New" || m.startsWith "New.") then
      throwError "supplier contamination {n}"
    rows := rows.push (Json.mkObj [("name", Json.str n.toString), ("module", Json.str m)])
  for n in required do
    unless deps.contains n do throwError "required proof dependency missing {root} -> {n}"
  let some c := env.find? root | throwError "missing root type {root}"
  if root == ``riemannHypothesis_step4_compact_arithmetic then
    unless c.type == mkConst (Name.mkSimple "RiemannHypothesis") do
      throwError "not exact stock RiemannHypothesis"
  if root == ``step4C1_compact_arithmetic then
    unless c.type == mkConst ``CofinalMomentSliceVanishingErrorBounds do
      throwError "not literal native C1"
  let pp ← liftTermElabM (Meta.ppExpr c.type)
  let some out ← liftIO (IO.getEnv "OPICA_COMPACT_TERMINAL_AUDIT_DIR") |
    throwError "audit output required"
  let dir : System.FilePath := out
  let receipt := Json.mkObj [("root", Json.str root.toString),
    ("type", Json.str (toString pp)), ("type_expr", Json.str (reprStr c.type)),
    ("axioms", Json.arr (axs.map (fun n => Json.str n.toString))),
    ("dependencies", Json.arr rows), ("required", Json.arr (required.toArray.map (fun n => Json.str n.toString))),
    ("native_only", toJson nativeOnly), ("count", toJson deps.size)]
  liftIO <| IO.FS.createDirAll dir
  liftIO <| IO.FS.writeFile (dir / (root.toString ++ ".json")) (receipt.compress ++ "\n")
  liftIO <| IO.println s!"COMPACT_TERMINAL_ROOT_PASS {root} {deps.size}"

end OPICACompactTerminalAudit

set_option maxHeartbeats 0 in
run_cmd do
  unless OPICACompactTerminalAudit.bannedName "New.grh" &&
    OPICACompactTerminalAudit.bannedName "sorryAx" &&
    OPICACompactTerminalAudit.bannedModule "New.Main" &&
    !OPICACompactTerminalAudit.bannedName "OPICACompactSupplier.principal_fixed_strip" do
    throwError "endpoint policy controls failed"
  OPICACompactTerminalAudit.audit ``riemannHypothesis_of_cofinal_moment_slice_bounds [] true
  OPICACompactTerminalAudit.audit ``evenMomentSliceLowerBound_zero_of_critical_line [] true
  OPICACompactTerminalAudit.audit ``oddMomentSliceLowerBound_zero_of_critical_line [] true
  OPICACompactTerminalAudit.audit ``OPICACompactSupplier.principal_weighted_upper
    [``eventually_primeError_le_rpow]
  OPICACompactTerminalAudit.audit ``OPICACompactSupplier.principal_fixed_strip
    [``OPICACompactSupplier.principal_weighted_upper,
     ``entireL_ne_zero_of_primeError_le,
     ``exists_entireL_quadTwist_ne_zero]
  OPICACompactTerminalAudit.audit ``step4C1_compact_arithmetic
    [``both_parity_zero_floor_arithmetic,
     ``OPICACompactSupplier.principal_fixed_strip,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line]
  OPICACompactTerminalAudit.audit ``riemannHypothesis_step4_compact_arithmetic
    [``step4C1_compact_arithmetic,
     ``riemannHypothesis_of_cofinal_moment_slice_bounds,
     ``eventually_primeError_le_rpow,
     ``entireL_ne_zero_of_primeError_le,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line]
