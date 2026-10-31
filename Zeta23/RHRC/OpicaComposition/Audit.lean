import Zeta23.RHRC.OpicaComposition.Elaborate
import Zeta23.RHRC.OpicaComposition.Export

open Lean Elab Command
namespace Zeta23.RHRC.OpicaComposition

private def json (s : String) : CommandElabM Json := ofExcept <| Json.parse s

/-- Fixed evaluator entry point. All strings are evaluator-generated protocol JSON;
the proposal controls only the closed Plan tree parsed in Protocol.lean. -/
def runAttempt (targetName : Name) (targetKind : String) (plan table allowed forbidden : String) : CommandElabM Unit := do
  let p ← ofExcept <| parsePlan (← json plan)
  let constants ← ofExcept <| parseConstants (← json table)
  let allowedAxioms ← ofExcept <| fromJson? (α := Array String) (← json allowed)
  let forbiddenNames ← ofExcept <| fromJson? (α := Array String) (← json forbidden)
  let (target, value) ← liftTermElabM do
    let target ← expectedTarget targetName targetKind
    let value ← elaborateClosed constants p target
    return (target, value)
  let targetInfo ← getConstInfo targetName
  liftTermElabM <| addDecl <| .thmDecl {name := `OpicaAttempt.result, levelParams := targetInfo.levelParams, type := target, value := value}
  auditDeclaration `OpicaAttempt.result target allowedAxioms forbiddenNames "OPICA_NATIVE"

def runAudit (targetName : Name) (targetKind : String) (allowed forbidden : String) : CommandElabM Unit := do
  let allowedAxioms ← ofExcept <| fromJson? (α := Array String) (← json allowed)
  let forbiddenNames ← ofExcept <| fromJson? (α := Array String) (← json forbidden)
  let target ← liftTermElabM <| expectedTarget targetName targetKind
  let result ← getConstInfo `OpicaAttempt.result
  liftTermElabM do
    unless ← Lean.Meta.isDefEq result.type target do throwError "independent expected target differs"
  liftTermElabM <| addDecl <| .thmDecl {name := `OpicaConsumer.result, levelParams := result.levelParams, type := target, value := (mkConst `OpicaAttempt.result (result.levelParams.map Level.param))}
  auditDeclaration `OpicaConsumer.result target allowedAxioms forbiddenNames "OPICA_INDEPENDENT"

end Zeta23.RHRC.OpicaComposition
