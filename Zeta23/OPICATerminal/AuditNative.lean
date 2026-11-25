import Zeta23.OPICATerminal.VerifyNative
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow
    [``Zeta23.OPICATerminal.eventual_energy_growth_of_right_zero,
     ``Zeta23.OPICATerminal.principalG_eq_literal,
     ``Zeta23.OPICATerminal.nativeZero_mem_principal,
     ``Deduction.landau_window, ``Deduction.poleData] true
    []

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.powerDetectorSupply_proved
    [``Zeta23.OPICATerminal.bothParityPowerComparison_proved,
     ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
     ``Deduction.landau_window, ``Deduction.poleData] true
    []

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.directEnergyToC1_proved
    [``Zeta23.OPICATerminal.powerDetectorSupply_proved,
     ``OPICAR2.directEnergyToC1_of_power_supply] true
    []

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.riemannHypothesis_of_nativeEnergySubpower_direct
    [``Zeta23.OPICATerminal.displacement_eq_zero_of_nativeEnergySubpower,
     ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
     ``Zeta23.OPICATerminal.displacement_bound,
     ``Deduction.landau_window, ``Deduction.poleData] true
    [``Zeta23.OPICATerminal.directEnergyToC1_proved,
     ``Zeta23.OPICATerminal.powerDetectorSupply_proved,
     ``Zeta23.OPICATerminal.bothParityPowerComparison_proved,
     ``Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_cofinal_moment_slice_bounds]

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``Zeta23.OPICATerminal.bothParityPowerComparison_proved
    [``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
     ``Zeta23.OPICATerminal.displacement_bound]
    true
    []

set_option maxHeartbeats 0 in
run_cmd do
  Zeta23.OPICATerminal.Audit.audit
    ``OPICAExtractionR1.native_energy_of_ramp_windows
    [``OPICAExtractionR1.window_energy_bound,
     ``OPICAExtractionR1.native_literalG_eq_rampG,
     ``OPICAExtractionR1.rampG_continuousOn_pos]
    true
    []
