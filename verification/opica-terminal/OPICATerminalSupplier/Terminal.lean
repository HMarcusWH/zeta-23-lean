import OPICATerminalSupplier.ClosedPrincipal
import Zeta23.OPICATerminal.PowerDetectorSupply
import Zeta23.OPICATerminal.DirectEnergyCrosscheck

/-! Arithmetic-supplied terminal candidate, checked only in a single common
Lean/Mathlib epoch. No hypothesis is permitted in the exact root. -/
noncomputable section
namespace Zeta23.OPICATerminal
open Zeta23.OPICARound4.ArithmeticFrontier

theorem native_energy_subpower_arithmetic_supplied : OPICAExtractionR1.NativeEnergySubpower :=
  OPICAExtractionR1.native_energy_of_ramp_windows
    OPICATerminalSupplier.principal_ramp_windows_proved

theorem native_c1_arithmetic_supplied : CofinalMomentSliceVanishingErrorBounds :=
  directEnergyToC1_proved native_energy_subpower_arithmetic_supplied

theorem riemannHypothesis_step4_arithmetic_supplied : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds native_c1_arithmetic_supplied

/-- Independent direct-energy cross-check using the same arithmetic premise. -/
theorem riemannHypothesis_step4_direct_crosscheck : RiemannHypothesis :=
  riemannHypothesis_of_nativeEnergySubpower_direct native_energy_subpower_arithmetic_supplied

end Zeta23.OPICATerminal

example : RiemannHypothesis :=
  Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied

#print axioms OPICAR2Original.principal_vwin_from_source
#print axioms OPICAR2Original.principal_host_from_source
#print axioms OPICATerminalSupplier.topG_from_original
#print axioms OPICATerminalSupplier.principal_connected_proved
#print axioms OPICATerminalSupplier.principal_ramp_windows_proved
#print axioms Zeta23.OPICATerminal.native_energy_subpower_arithmetic_supplied
#print axioms Zeta23.OPICATerminal.native_c1_arithmetic_supplied
#print axioms Zeta23.OPICATerminal.riemannHypothesis_step4_arithmetic_supplied

example : RiemannHypothesis := Zeta23.OPICATerminal.riemannHypothesis_step4_direct_crosscheck
#print axioms Zeta23.OPICATerminal.riemannHypothesis_step4_direct_crosscheck
