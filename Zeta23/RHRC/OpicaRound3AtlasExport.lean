import Lean.Elab.Command
import Lean.Meta
import Lean.PrivateName
import Lean.Util.FoldConsts
import Zeta23.RHRC.OpicaTypeExprExport

/-! AUDIT_ONLY. Read the actual elaborated type and outer telescope. A constant
in a proof term is never reported as a hypothesis. No mathematical module may
import this exporter, and the emitted inventory creates no new theorem. -/

open Lean Lean.Elab Command

namespace Zeta23.RHRC.OpicaRound3AtlasExport

structure Query where
  declaration : String
  moduleName : String

private def kind : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

private def binderKind : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def strings (xs : List String) : Json :=
  .arr ((xs.mergeSort (· < ·)).toArray.map Json.str)

private def constants (e : Expr) : Json :=
  strings (e.getUsedConstantsAsSet.toList.map Name.toString)

private def structural : ConstantInfo → List Name
  | .inductInfo info => info.ctors ++ info.all
  | .ctorInfo info => [info.induct]
  | .recInfo info => info.all
  | _ => []

private def pretty (e : Expr) : MetaM String := do
  return (← Lean.PrettyPrinter.ppExpr e).pretty (width := 1000000)

-- Only metadata is removed from the outer telescope. No definition is unfolded;
-- the full original type, including its metadata, is exported unchanged below.
private partial def outerType (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE n d b bi => .forallE n d (outerType b) bi
  | body => body

/-- Exact named declarations only; unknown, private and wrong-origin queries fail. -/
def exportAtlas (queries : Array Query) : CommandElabM Unit := do
  if queries.isEmpty || queries.size > 1024 then
    throwError "atlas query population outside finite budget"
  let env ← getEnv
  let mut seen : NameSet := {}
  for query in queries do
    let name := query.declaration.toName
    if seen.contains name then throwError "duplicate atlas declaration {name}"
    seen := seen.insert name
    if name.isInternal || isPrivateName name then throwError "private atlas declaration {name}"
    let info ← getConstInfo name
    let some index := env.getModuleIdxFor? name
      | throwError "atlas declaration has no imported origin {name}"
    let moduleName := env.allImportedModuleNames[index.toNat]!.toString
    unless moduleName == query.moduleName do throwError "atlas origin differs for {name}"
    let dagText ← liftIO <| OpicaTypeExprExport.exportType info.type
    let dag ← match Json.parse dagText with
      | .ok value => pure value
      | .error message => throwError "atlas type codec JSON failure: {message}"
    let (typeText, binders, conclusion) ← liftTermElabM do
      let typeText ← pretty info.type
      Meta.forallTelescope (outerType info.type) fun xs result => do
        let mut rows := #[]
        for i in [:xs.size] do
          let localDecl ← xs[i]!.fvarId!.getDecl
          let proposition ← Meta.isProp localDecl.type
          let className ← Meta.isClass? localDecl.type
          rows := rows.push <| Json.mkObj [
            ("position", toJson i), ("name", .str localDecl.userName.toString),
            ("binder_info", .str (binderKind localDecl.binderInfo)),
            ("domain_text", .str (← pretty localDecl.type)),
            ("domain_is_prop", .bool proposition),
            ("typeclass_binder", .bool (localDecl.binderInfo == .instImplicit)),
            ("class_name", match className with | some n => .str n.toString | none => .null)]
        return (typeText, rows, ← pretty result)
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "atlas declaration has an unadmitted axiom: {name} uses {ax}"
    let row := Json.mkObj [
      ("schema", .str "OPICA3_ATLAS_COMPILER_ROW_V1"),
      ("declaration", .str name.toString), ("module", .str moduleName),
      ("kind", .str (kind info)), ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_text", .str typeText), ("type_expression", dag),
      ("outer_telescope", .arr binders), ("conclusion_text", .str conclusion),
      ("type_constants", constants info.type),
      ("value_constants", match info.value? (allowOpaque := true) with
        | some value => constants value | none => .arr #[]),
      ("structure_constants", strings ((structural info).filter (· != name) |>.map Name.toString)),
      ("axioms", strings (axioms.toList.map Name.toString))]
    let payload := row.compress
    if payload.utf8ByteSize > 8388608 then throwError "atlas row exceeds byte budget"
    liftIO <| IO.println ("OPICA3_ATLAS\t" ++ payload)

end Zeta23.RHRC.OpicaRound3AtlasExport
