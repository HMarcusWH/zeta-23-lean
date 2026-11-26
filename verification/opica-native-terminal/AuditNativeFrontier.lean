import Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure
import Zeta23.OPICANativeTerminal.AuditCore
open Lean Elab Command
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier
example (h : CofinalMomentSliceVanishingErrorBounds) : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds h
set_option maxHeartbeats 0 in
run_cmd do
  OPICANativeTerminalAudit.audit ``riemannHypothesis_of_cofinal_moment_slice_bounds [] true
  OPICANativeTerminalAudit.audit ``evenMomentSliceLowerBound_zero_of_critical_line [] true
  OPICANativeTerminalAudit.audit ``oddMomentSliceLowerBound_zero_of_critical_line [] true
