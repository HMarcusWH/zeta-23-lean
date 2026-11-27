import Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure
import Zeta23.OPICANativeTerminal.AuditCore
open Lean Elab Command OPICANativeTerminalAudit
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier
example (h : CofinalMomentSliceVanishingErrorBounds) : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds h
example (h : CofinalMomentSliceVanishingErrorBounds) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_cofinal_moment_slice_bounds h

set_option maxHeartbeats 0 in
run_cmd do
  audit ``riemannHypothesis_of_cofinal_moment_slice_bounds
    [``no_off_line_zero_of_cofinal_moment_slice_bounds] true
  audit ``no_off_line_zero_of_cofinal_moment_slice_bounds [] true
  audit ``evenMomentSliceLowerBound_zero_of_critical_line [] true
  audit ``oddMomentSliceLowerBound_zero_of_critical_line [] true
  audit ``abs_re_sub_half_le_of_re_le [] true
