import OPICAAuditFixture
import Zeta23.OPICATerminal.Audit

open Lean Elab Command
open Zeta23.OPICATerminal.Audit

private def expectRejected (label fragment : String)
    (action : CommandElabM Unit) : CommandElabM Unit := do
  let result ← try
    action
    pure none
  catch ex =>
    pure (some (← ex.toMessageData.toString))
  match result with
  | none => throwError "negative auditor control accepted: {label}"
  | some message =>
    unless (message.splitOn fragment).length > 1 do
      throwError "wrong rejection for {label}: {message}"

set_option maxHeartbeats 0 in
run_cmd do
  let deps ← liftTermElabM (closure ``OPICAAuditFixture.clean)
  unless deps.contains ``OPICAAuditFixture.leaf && deps.contains ``OPICAAuditFixture.middle do
    throwError "imported transitive proof-body dependencies not visible"
  audit ``OPICAAuditFixture.clean [``OPICAAuditFixture.leaf, ``OPICAAuditFixture.middle] false []
  expectRejected "transitive axiom" "forbidden axiom"
    (audit ``OPICAAuditFixture.dirty [] false [])
  expectRejected "missing required declaration" "required proof dependency absent"
    (audit ``OPICAAuditFixture.clean [``OPICAAuditFixture.dirty] false [])
  expectRejected "explicit exclusion" "forbidden terminal dependency"
    (audit ``OPICAAuditFixture.clean [] false [``OPICAAuditFixture.leaf])
  expectRejected "forbidden declaration name" "forbidden terminal dependency"
    (audit ``OPICAAuditFixture.forbiddenNameRoot [] false [])
  expectRejected "unapproved native origin" "supplier contamination"
    (audit ``OPICAAuditFixture.clean [] true [])
