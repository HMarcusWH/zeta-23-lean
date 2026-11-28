import DirectWindowAudit.Core
import DirectWindowAudit.SmokeFixtures

open Lean Elab Command DirectWindowAudit DirectWindowFixtures

private def expectReject (label diagnostic : String) (test : CommandElabM Unit) : CommandElabM Unit := do
  let mut message : Option String := none
  try test catch ex => message := some (← ex.toMessageData.toString)
  let some diagnosticText := message | throwError "negative audit control accepted: {label}"
  unless (diagnosticText.splitOn diagnostic).length > 1 do
    throwError "control {label} failed for an unrelated reason: {diagnosticText}"
  logInfo m!"DIRECT_WINDOW_AUDIT_REJECTED {label}"

set_option maxHeartbeats 0 in
run_cmd
  audit ``good .fixture [] [] (some ``True)
  expectReject "wrong type" "wrong exact root type" (audit ``good .fixture [] [] (some ``False))
  expectReject "missing dependency" "required dependency missing" (audit ``good .fixture [``Nat] [])
  expectReject "custom axiom" "forbidden axiom" (audit ``extraAxiom .fixture [] [])
  expectReject "sorry" "sorryAx" (audit ``admitted .fixture [] [])
  expectReject "hidden endpoint" "forbidden endpoint" (audit ``hiddenEndpoint .fixture [] [])
  expectReject "type edge" "forbidden endpoint" (audit ``typeOnly .fixture [] [])
  expectReject "constructor edge" "forbidden endpoint" (audit ``structuralEndpoint .fixture [] [])
  expectReject "definitional RH alias" "unconditional RH dependency" (audit ``hiddenRH .fixture [] [])
  expectReject "production fixture origin" "forbidden origin" (audit ``good .terminal [] [])
  logInfo "DIRECT_WINDOW_AUDIT_CONTROLS_PASS"
