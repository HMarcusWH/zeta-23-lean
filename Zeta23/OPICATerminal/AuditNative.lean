import Zeta23.OPICATerminal.VerifyNative
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow
  [``Zeta23.OPICATerminal.eventual_energy_growth_of_right_zero,
   ``Zeta23.OPICATerminal.principalG_eq_literal,
   ``Zeta23.OPICATerminal.nativeZero_mem_principal,
   ``Deduction.landau_window, ``Deduction.poleData] true

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``Zeta23.OPICATerminal.powerDetectorSupply_proved
  [``Zeta23.OPICATerminal.bothParityPowerComparison_proved,
   ``Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow,
   ``Deduction.landau_window, ``Deduction.poleData] true

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``Zeta23.OPICATerminal.directEnergyToC1_proved
  [``Zeta23.OPICATerminal.powerDetectorSupply_proved,
   ``OPICAR2.directEnergyToC1_of_power_supply] true
