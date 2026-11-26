import Zeta23.OPICANativeTerminal.Terminal
import Zeta23.OPICANativeTerminal.AuditCore

open Lean Elab Command Filter
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICANativeTerminal

-- Explicit expected types, not a proof by name.
example : CofinalMomentSliceVanishingErrorBounds := step4C1_native_arithmetic
example : RiemannHypothesis := riemannHypothesis_step4_native_arithmetic
example (L : ℝ) (hL : 0 < L) :
    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 ∧
    OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 :=
  both_parity_zero_floor_arithmetic L hL

set_option maxHeartbeats 0 in
run_cmd do
  unless OPICANativeTerminalAudit.bannedName "New.grh" &&
    OPICANativeTerminalAudit.bannedName "sorryAx" &&
    OPICANativeTerminalAudit.bannedModule "New.Main" &&
    !OPICANativeTerminalAudit.bannedName "Zeta23Arithmetic.Principal.principal_fixed_strip" do
    throwError "endpoint policy controls failed"
  OPICANativeTerminalAudit.audit ``riemannHypothesis_of_cofinal_moment_slice_bounds [] true
  OPICANativeTerminalAudit.audit ``evenMomentSliceLowerBound_zero_of_critical_line [] true
  OPICANativeTerminalAudit.audit ``oddMomentSliceLowerBound_zero_of_critical_line [] true
  OPICANativeTerminalAudit.audit ``eventually_primeError_le_rpow
    [``star_inequality, ``Data.short_forms, ``Data.enough_forms, ``Data.integral_forms_long] false none true
  OPICANativeTerminalAudit.audit ``entireL_ne_zero_of_primeError_le [``exists_entireL_quadTwist_ne_zero]
  OPICANativeTerminalAudit.audit ``Zeta23Arithmetic.Principal.principal_weighted_upper
    [``eventually_primeError_le_rpow]
  OPICANativeTerminalAudit.audit ``Zeta23Arithmetic.Principal.principal_fixed_strip
    [``Zeta23Arithmetic.Principal.principal_weighted_upper,
     ``entireL_ne_zero_of_primeError_le,
     ``exists_entireL_quadTwist_ne_zero]
  OPICANativeTerminalAudit.audit ``both_parity_zero_floor_arithmetic
    [``Zeta23Arithmetic.Principal.principal_fixed_strip,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line]
  OPICANativeTerminalAudit.audit ``step4C1_native_arithmetic
    [``both_parity_zero_floor_arithmetic,
     ``Zeta23Arithmetic.Principal.principal_fixed_strip,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line] false (some ``CofinalMomentSliceVanishingErrorBounds)
  OPICANativeTerminalAudit.audit ``riemannHypothesis_step4_native_arithmetic
    [``step4C1_native_arithmetic,
     ``riemannHypothesis_of_cofinal_moment_slice_bounds,
     ``eventually_primeError_le_rpow,
     ``entireL_ne_zero_of_primeError_le,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line] false (some ``RiemannHypothesis) true
