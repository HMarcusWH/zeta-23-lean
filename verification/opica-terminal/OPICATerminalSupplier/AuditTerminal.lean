import OPICATerminalSupplier.Terminal
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``OPICATerminalSupplier.principal_ramp_windows_proved
  [``OPICATerminalSupplier.topG_from_original,
   ``OPICAR2Original.principal_host_from_source,
   ``OPICAExtractionR1.principal_ramp_windows_of_connected] false

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied
  [``OPICATerminalSupplier.principal_ramp_windows_proved,
   ``Zeta23.OPICATerminal.native_energy_subpower_arithmetic_supplied,
   ``Zeta23.OPICATerminal.native_c1_arithmetic_supplied,
   ``Zeta23.OPICATerminal.directEnergyToC1_proved,
   ``Zeta23.OPICATerminal.powerDetectorSupply_proved,
   ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
   ``Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds] false
