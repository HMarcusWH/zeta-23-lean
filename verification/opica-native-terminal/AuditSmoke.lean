import Zeta23.OPICANativeTerminal.AuditCore
import AuditSmokeFixtures
open Lean Elab Command
open OPICANativeTerminalAudit
open OPICAAuditFixtures

private def expectReject (label : String) (test : CommandElabM Unit) : CommandElabM Unit := do
  let mut rejected := false
  try test catch _ => rejected := true
  unless rejected do throwError "negative audit control accepted: {label}"
  liftIO <| IO.println s!"NATIVE_AUDIT_CONTROL_REJECTED {label}"

set_option maxHeartbeats 0 in
run_cmd do
  unless bannedName "New.grh" && bannedName "sorryAx" &&
    bannedModule "Zeta23Arithmetic.New.Main" && !allowedAxiom (Name.mkSimple "sorryAx") &&
    allowedAxiom ``propext && !bannedName "Zeta23Arithmetic.Principal.principal_fixed_strip" &&
    !permittedOrigin "Zeta23Arithmetic.New.ArithmeticOnly" true false false &&
    !permittedOrigin "Zeta23.CCM.SourceMatrix" false true false &&
    !permittedOrigin "AuditSmokeFixtures" false false false &&
    !permittedOrigin "Challenge.NativeRH" false false false do
    throwError "audit policy controls failed"
  audit ``True.intro [] true (some ``True) true
  audit ``good [] false (some ``True) true (allowSmokeFixtures := true)
  audit ``picked [``Branch.right] false (some ``Branch) true (allowSmokeFixtures := true)
  expectReject "missing required dependency" (audit ``True.intro [``Nat] true)
  expectReject "wrong exact type" (audit ``True.intro [] true (some ``False))
  expectReject "fixture origin" (audit ``good [])
  expectReject "forbidden axiom" (audit ``badAxiom [] (allowSmokeFixtures := true))
  expectReject "sorry dependency" (audit ``badSorry [] (allowSmokeFixtures := true))
  expectReject "hidden endpoint" (audit ``usesHiddenEndpoint [] (allowSmokeFixtures := true))
  expectReject "type-only endpoint" (audit ``typeOnly [] (allowSmokeFixtures := true))
  expectReject "forbidden endpoint itself" (audit ``New.grh [] (allowSmokeFixtures := true))
  liftIO <| IO.println "NATIVE_AUDIT_SMOKE_PASS"
