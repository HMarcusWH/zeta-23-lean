import Lean.Meta
import Lean.Util.FoldConsts
import Zeta23.RHRC.OpicaComposition.Protocol

open Lean Meta
namespace Zeta23.RHRC.OpicaComposition

private def resolve (table : Array ApprovedConstant) (id : String) (role := "constant") : MetaM Expr := do
  let some row := table.find? (·.id == id) | throwError "undeclared constant ID"
  unless role == "constant" || row.role == role do throwError "constant role differs"
  let info ← getConstInfo row.declaration
  let env ← getEnv
  let some idx := env.getModuleIdxFor? row.declaration | throwError "unimported constant"
  unless env.allImportedModuleNames[idx.toNat]! == row.moduleName do
    throwError "constant module differs: {row.declaration}; expected {row.moduleName}; actual {env.allImportedModuleNames[idx.toNat]!}"
  return mkConst row.declaration (← info.levelParams.mapM fun _ => mkFreshLevelMVar)

private def fit (e : Expr) (expected : Option Expr) : MetaM Expr := do
  if let some t := expected then
    let actual ← inferType e
    unless ← isDefEq actual t do
      throwError "TYPE_REJECTED_THIS_APPLICATION: term {e}; actual {actual}; expected {t}"
  return e

/-- Only attempt-local metavariables are assignable. The target is rigid and closed. -/
partial def elaboratePlan (table : Array ApprovedConstant) (p : Plan)
    (locals : Array Expr) (expected : Option Expr) (fuel : Nat := 2048) : MetaM Expr := do
  if fuel == 0 then throwError "RESOURCE_EXHAUSTED: term nodes"
  let next := fuel - 1
  match p with
  | .const id => fit (← resolve table id) expected
  | .local slot =>
    let some e := locals[slot]? | throwError "unauthorized local slot"
    fit e expected
  | .lam body =>
    let some target := expected | throwError "lambda requires trusted expected telescope"
    let .forallE n d b bi ← whnf target | throwError "lambda outside expected telescope"
    withLocalDecl n bi d fun x => do
      let value ← elaboratePlan table body (locals.push x) (some (b.instantiate1 x)) next
      fit (← mkLambdaFVars #[x] value) expected
  | .letE value body =>
    let v ← elaboratePlan table value locals none next
    let t ← inferType v
    withLetDecl `shared t v fun x => do
      let result ← elaboratePlan table body (locals.push x) expected next
      return ← mkLetFVars #[x] result
  | .app fn args =>
    let f ← elaboratePlan table fn locals none next
    applyPlans f args
  | .transport id args =>
    let f ← resolve table id "transport"
    applyPlans f args
  | .project id value =>
    let f ← resolve table id "projection"
    let n := f.getAppFn.constName!
    unless (← getEnv).getProjectionFnInfo? n |>.isSome do throwError "uncertified projection"
    let v ← elaboratePlan table value locals none next
    fit (← mkAppM' f #[v]) expected
  | .cases value branches =>
    let some target := expected | throwError "cases requires expected result"
    let v ← elaboratePlan table value locals none next
    let ty ← whnf (← inferType v)
    let args := ty.getAppArgs
    match ty.getAppFn.constName? with
    | some ``Exists =>
      unless branches.size == 1 && args.size == 2 do throwError "Exists requires one complete branch"
      withLocalDeclD `witness args[0]! fun x => do
        withLocalDeclD `witness_property (mkApp args[1]! x) fun h => do
          let b ← elaboratePlan table branches[0]! (locals ++ #[x,h]) (some target) next
          fit (← mkAppM ``Exists.elim #[v, ← mkLambdaFVars #[x,h] b]) expected
    | some ``And =>
      unless branches.size == 1 && args.size == 2 do throwError "And requires one complete branch"
      withLocalDeclD `left args[0]! fun a => do
        withLocalDeclD `right args[1]! fun b => do
          let out ← elaboratePlan table branches[0]! (locals ++ #[a,b]) (some target) next
          fit (← mkAppM ``And.elim #[← mkLambdaFVars #[a,b] out, v]) expected
    | some ``Or =>
      unless branches.size == 2 && args.size == 2 do throwError "Or requires both branches"
      let left ← withLocalDeclD `left args[0]! fun a => do
        mkLambdaFVars #[a] (← elaboratePlan table branches[0]! (locals.push a) (some target) next)
      let right ← withLocalDeclD `right args[1]! fun b => do
        mkLambdaFVars #[b] (← elaboratePlan table branches[1]! (locals.push b) (some target) next)
      fit (← mkAppM ``Or.elim #[v,left,right]) expected
    | _ => throwError "cases supports only proved And/Or/Exists"
where
  applyPlans (f : Expr) (args : Array Plan) : MetaM Expr := do
    let mut out := f
    let mut instances : Array Expr := #[]
    let mut slots : Array Expr := #[]
    for _arg in args do
      let mut ty ← whnf (← inferType out)
      while ty.isForall && ty.binderInfo != .default do
        let dom := ty.bindingDomain!
        let v ← mkFreshExprMVar dom
        if ty.binderInfo == .instImplicit then instances := instances.push v
        out := mkApp out v
        ty ← whnf (ty.bindingBody!.instantiate1 v)
      let .forallE _ dom _ _ := ty | throwError "application arity differs"
      let slot ← mkFreshExprMVar dom
      slots := slots.push slot
      out := mkApp out slot
    -- Constrain the result by the rigid evaluator target before elaborating
    -- dependent arguments (notably nested Exists.intro predicates).
    out ← fit out expected
    for i in [:args.size] do
      let dom ← instantiateMVars (← inferType slots[i]!)
      let x ← elaboratePlan table args[i]! locals (some dom) (fuel - 1)
      unless ← isDefEq slots[i]! x do throwError "TYPE_REJECTED_THIS_APPLICATION: explicit argument"
    for inst in instances do
      let value ← synthInstance (← inferType inst)
      unless ← isDefEq inst value do throwError "typeclass assignment failed"
    return ← instantiateMVars out

def elaborateClosed (table : Array ApprovedConstant) (p : Plan) (target : Expr) : MetaM Expr := do
  if target.hasMVar || target.hasFVar || target.hasLooseBVars then throwError "frozen target is not rigid/closed"
  let targetBefore := target
  let result ← withNewMCtxDepth do
    forallTelescope target fun xs conclusion => do
      let e ← elaboratePlan table p xs (some conclusion)
      let e ← instantiateMVars e
      if e.hasMVar then throwError "UNRESOLVED: metavariables remain"
      mkLambdaFVars xs e
  unless target == targetBefore do throwError "frozen target changed"
  check result
  unless ← isDefEq (← inferType result) target do throwError "actual target differs"
  if result.hasMVar || result.hasFVar || result.hasLooseBVars then throwError "open candidate"
  return result

end Zeta23.RHRC.OpicaComposition
