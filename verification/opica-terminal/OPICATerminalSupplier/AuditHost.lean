import OPICATerminalSupplier.PrincipalHost
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``OPICAR2Original.principal_host_from_source
    [``OPICAR2Original.principal_vwin_from_source,
     ``UpperTheory.One.vwin_of_row,
     ``UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter] false
    []
