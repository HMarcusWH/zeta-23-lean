import Zeta23.OPICANativeTerminal.AuditCore
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  unless OPICANativeTerminalAudit.bannedName "New.grh" &&
    OPICANativeTerminalAudit.bannedName "sorryAx" &&
    OPICANativeTerminalAudit.bannedModule "Zeta23Arithmetic.New.Main" &&
    !OPICANativeTerminalAudit.allowedAxiom (Name.mkSimple "sorryAx") &&
    OPICANativeTerminalAudit.allowedAxiom ``propext &&
    !OPICANativeTerminalAudit.bannedName "Zeta23Arithmetic.Principal.principal_fixed_strip" do
    throwError "audit policy controls failed"
  OPICANativeTerminalAudit.audit ``True.intro [] true (some ``True) true
  let mut rejected := false
  try
    OPICANativeTerminalAudit.audit ``True.intro [``Nat] true
  catch _ => rejected := true
  unless rejected do throwError "missing dependency negative control accepted"
  liftIO <| IO.println "NATIVE_AUDIT_SMOKE_PASS"
