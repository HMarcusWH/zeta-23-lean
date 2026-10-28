import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Zeta23.RHRC.OpicaTypeExprExport

open Lean Elab Command Meta
namespace Zeta23.RHRC.OpicaComposition

def expectedTarget (n : Name) (kind : String) : MetaM Expr := do
  let info ← getConstInfo n
  let target ← if kind == "type" then pure info.type else if kind == "value" then
    match info.value? (allowOpaque := false) with
    | some value => pure value
    | none => throwError "target must have a transparent evaluator-owned definition"
    else throwError "unknown target kind"
  if target.hasMVar || target.hasFVar || target.hasLooseBVars then throwError "target is open"
  unless ← isProp target do throwError "target is not a proposition"
  return target

def exportTarget (n : Name) (kind : String) : CommandElabM Unit := do
  let target ← liftTermElabM <| expectedTarget n kind
  let text ← liftIO <| OpicaTypeExprExport.exportType target
  liftIO <| IO.println ("OPICA_TARGET\t" ++ text)

def dependencyClosure (name : Name) : CoreM (Array Name) := do
  let mut seen : NameSet := {}
  let mut discovered : NameSet := {}
  discovered := discovered.insert name
  let mut todo := #[name]
  let mut index := 0
  while index < todo.size do
    if todo.size > 100000 then throwError "RESOURCE_EXHAUSTED: dependency closure"
    let n := todo[index]!
    index := index + 1
    if seen.contains n then continue
    seen := seen.insert n
    let info ← getConstInfo n
    let mut uses := info.type.getUsedConstantsAsSet
    if let some v := info.value? (allowOpaque := true) then
      uses := uses.merge v.getUsedConstantsAsSet
    for used in uses.toList do
      unless discovered.contains used do
        discovered := discovered.insert used
        todo := todo.push used
  return seen.toList.toArray

def auditDeclaration (name : Name) (target : Expr) (allowed forbidden : Array String)
    (marker : String) : CommandElabM Unit := do
  let info ← getConstInfo name
  liftTermElabM do
    check (mkConst name (info.levelParams.map Level.param))
    unless ← isDefEq info.type target do throwError "independent exact target check failed"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless allowed.contains ax.toString do throwError "unapproved transitive axiom {ax}"
  let closure ← liftTermElabM <| dependencyClosure name
  for n in closure do
    if forbidden.contains n.toString ||
        n.toString.startsWith "Zeta23.RHRC.OpicaComposition.Validation." ||
        n.toString.startsWith "Zeta23.OPICARound3.Validation." then
      throwError "hidden forbidden answer dependency {n}"
  let dagText ← liftIO <| OpicaTypeExprExport.exportType info.type
  let termText ← match info.value? (allowOpaque := true) with
    | some value => liftIO <| OpicaTypeExprExport.exportType value
    | none => throwError "result has no proof value"
  let dag ← ofExcept <| Json.parse dagText
  let term ← ofExcept <| Json.parse termText
  let (context, objects) ← liftTermElabM do
    forallTelescope target fun xs _ => do
      let mut rows := #[]
      let mut objects := #[]
      let some proof := info.value? (allowOpaque := true) | throwError "result proof absent"
      let openedProof := (mkAppN proof xs).headBeta
      for i in [:xs.size] do
        let binder ← xs[i]!.fvarId!.getDecl
        let domain ← mkForallFVars (xs.extract 0 i) binder.type
        let domainText ← liftM (m := IO) (n := TermElabM) <| OpicaTypeExprExport.exportType domain
        let binderInfo := match binder.binderInfo with
          | .default => "default" | .implicit => "implicit"
          | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"
        rows := rows.push <| Json.mkObj [
          ("slot", toJson i), ("name", .str binder.userName.toString),
          ("binder_info", .str binderInfo),
          ("is_prop", .bool (← isProp binder.type)),
          ("used_in_proof", .bool (openedProof.containsFVar xs[i]!.fvarId!)),
          ("is_typeclass", .bool (binder.binderInfo == .instImplicit)),
          ("domain_expression", ← ofExcept <| Json.parse domainText)]
        let localTerm ← mkLambdaFVars (xs.extract 0 (i+1)) xs[i]!
        let localType ← inferType localTerm
        let termText ← liftM (m := IO) (n := TermElabM) <| OpicaTypeExprExport.exportType localTerm
        let typeText ← liftM (m := IO) (n := TermElabM) <| OpicaTypeExprExport.exportType localType
        objects := objects.push <| Json.mkObj [
          ("object_kind", .str "AUTHORIZED_LOCAL"), ("scope_index", toJson (i+1)),
          ("term_expression", ← ofExcept <| Json.parse termText),
          ("type_expression", ← ofExcept <| Json.parse typeText)]
      return (rows, objects)
  let objects := objects.push <| Json.mkObj [
    ("object_kind", .str "DEPENDENT_PROOF_PACKET"), ("scope_index", toJson context.size),
    ("term_expression", term), ("type_expression", dag)]
  let row := Json.mkObj [
    ("schema", .str "OPICA_NATIVE_CHECK_V1"), ("declaration", .str name.toString),
    ("type_expression", dag), ("term_expression", term), ("context", .arr context),
    ("object_bindings", .arr objects),
    ("axioms", toJson (axioms.toList.map Name.toString |>.mergeSort (· < ·))),
    ("constants", toJson (closure.toList.map Name.toString |>.mergeSort (· < ·)))]
  liftIO <| IO.println (marker ++ "\t" ++ row.compress)

end Zeta23.RHRC.OpicaComposition
