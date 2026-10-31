import Lean

/-! Trusted finite JSON proof-plan parser. No Lean syntax is parsed from a plan. -/
open Lean
namespace Zeta23.RHRC.OpicaComposition

inductive Plan where
  | const (id : String)
  | local (slot : Nat)
  | app (fn : Plan) (args : Array Plan)
  | lam (body : Plan)
  | letE (value body : Plan)
  | project (id : String) (value : Plan)
  | cases (value : Plan) (branches : Array Plan)
  | transport (id : String) (args : Array Plan)
  deriving Inhabited

def keys (j : Json) (expected : List String) : Except String Unit := do
  let obj ← j.getObj?
  if (obj.toList.map Prod.fst |>.mergeSort (· < ·)) != expected.mergeSort (· < ·) then
    throw "closed protocol field set differs"

private def field (j : Json) (n : String) : Except String Json := j.getObjVal? n
private def txt (j : Json) (n : String) : Except String String := do (← field j n).getStr?
private def arr (j : Json) (n : String) : Except String (Array Json) := do (← field j n).getArr?

def parsePlan (j : Json) (fuel : Nat := 64) : Except String Plan := do
  match fuel with
  | 0 => throw "plan depth exhausted"
  | fuel + 1 =>
    let tag ← txt j "tag"
    match tag with
    | "const" => keys j ["tag", "constant_id"]; return .const (← txt j "constant_id")
    | "local" => keys j ["tag", "binder_slot"]; return .local (← (← field j "binder_slot").getNat?)
    | "app" =>
      keys j ["tag", "function", "arguments"]
      return .app (← parsePlan (← field j "function") fuel)
        (← (← arr j "arguments").mapM (fun x => parsePlan x fuel))
    | "lambda" => keys j ["tag", "body"]; return .lam (← parsePlan (← field j "body") fuel)
    | "let" =>
      keys j ["tag", "value", "body"]
      return .letE (← parsePlan (← field j "value") fuel) (← parsePlan (← field j "body") fuel)
    | "project" =>
      keys j ["tag", "constant_id", "value"]
      return .project (← txt j "constant_id") (← parsePlan (← field j "value") fuel)
    | "cases" =>
      keys j ["tag", "value", "branches"]
      return .cases (← parsePlan (← field j "value") fuel)
        (← (← arr j "branches").mapM (fun x => parsePlan x fuel))
    | "transport" =>
      keys j ["tag", "constant_id", "arguments"]
      return .transport (← txt j "constant_id")
        (← (← arr j "arguments").mapM (fun x => parsePlan x fuel))
    | _ => throw "unknown restricted grammar tag"

structure ApprovedConstant where
  id : String
  declaration : Name
  moduleName : Name
  role : String

def parseConstants (j : Json) : Except String (Array ApprovedConstant) := do
  (← j.getArr?).mapM fun x => do
    keys x ["id", "declaration", "module", "role"]
    let id ← txt x "id"
    let declaration ← txt x "declaration"
    let moduleName ← txt x "module"
    let role ← txt x "role"
    return {id, declaration := declaration.toName, moduleName := moduleName.toName, role}

end Zeta23.RHRC.OpicaComposition
