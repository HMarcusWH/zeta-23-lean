import OPICATerminalSupplier.Terminal
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied
    [``OPICATerminalSupplier.principal_ramp_windows_proved,
     ``Zeta23.OPICATerminal.native_energy_subpower_arithmetic_supplied,
     ``Zeta23.OPICATerminal.native_c1_arithmetic_supplied,
     ``Zeta23.OPICATerminal.directEnergyToC1_proved,
     ``Zeta23.OPICATerminal.powerDetectorSupply_proved,
     ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
     ``Zeta23.OPICATerminal.bothParityPowerComparison_proved,
     ``Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds] false
    []

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.riemannHypothesis_step4_direct_crosscheck
    [``OPICATerminalSupplier.principal_ramp_windows_proved,
     ``Zeta23.OPICATerminal.native_energy_subpower_arithmetic_supplied,
     ``Zeta23.OPICATerminal.riemannHypothesis_of_nativeEnergySubpower_direct,
     ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow] false
    [``Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied,
     ``Zeta23.OPICATerminal.native_c1_arithmetic_supplied,
     ``Zeta23.OPICATerminal.directEnergyToC1_proved,
     ``Zeta23.OPICATerminal.powerDetectorSupply_proved,
     ``Zeta23.OPICATerminal.bothParityPowerComparison_proved,
     ``Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds]

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.native_energy_subpower_arithmetic_supplied
    [``OPICATerminalSupplier.principal_ramp_windows_proved,
     ``OPICAExtractionR1.native_energy_of_ramp_windows]
    false
    []
