import OPICATerminalSupplier.ClosedPrincipal
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``OPICATerminalSupplier.principal_ramp_windows_proved
    [``OPICATerminalSupplier.topG_from_original,
     ``OPICAR2Original.principal_host_from_source,
     ``OPICAExtractionR1.principal_ramp_windows_of_connected] false
    []

