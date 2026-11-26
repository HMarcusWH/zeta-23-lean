import Zeta23.OPICANativeTerminal.Terminal
import Zeta23.OPICANativeTerminal.AuditCore
open Lean Elab Command Filter Real OPICANativeTerminalAudit
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23Arithmetic.Principal
example (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) :=
  eventually_primeError_le_rpow P h
example (P : Parameters) {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, primeError P.d P.N₀ x ≤ x ^ (β - 1) :=
  weighted_upper_at P hβ hβ1
example {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    PrincipalWeightedUpper β := principal_weighted_upper hβ hβ1
example {β : ℝ} (hβ : 1 / 2 < β) (h : PrincipalWeightedUpper β)
    (ρ : ℂ) (hρ : β < ρ.re) (hs1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 :=
  zeta_ne_zero_of_principal_weighted_upper hβ h ρ hρ hs1
example {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1)
    (ρ : ℂ) (hs1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) : ρ.re ≤ β :=
  principal_fixed_strip hβ hβ1 ρ hs1 hz
example (h : CofinalMomentSliceVanishingErrorBounds) : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds h
example (h : CofinalMomentSliceVanishingErrorBounds) :
    ∀ ρ : Zeta23.zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_cofinal_moment_slice_bounds h
open Zeta23.OPICANativeTerminal
example : CofinalMomentSliceVanishingErrorBounds := step4C1_native_arithmetic
example : RiemannHypothesis := riemannHypothesis_step4_native_arithmetic
example (ρ : ℂ) (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) : ρ.re ≤ 1 / 2 :=
  actual_zero_re_le_half ρ hρ
example (ρ : ℂ) (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) : ρ.re = 1 / 2 :=
  actual_critical_line_arithmetic ρ hρ
example (L : ℝ) (hL : 0 < L) :
    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 ∧
    OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 :=
  both_parity_zero_floor_arithmetic L hL

set_option maxHeartbeats 0 in
run_cmd do
  audit ``riemannHypothesis_of_cofinal_moment_slice_bounds
    [``no_off_line_zero_of_cofinal_moment_slice_bounds] true
  audit ``no_off_line_zero_of_cofinal_moment_slice_bounds [] true
  audit ``evenMomentSliceLowerBound_zero_of_critical_line [] true
  audit ``oddMomentSliceLowerBound_zero_of_critical_line [] true
  audit ``abs_re_sub_half_le_of_re_le [] true
  audit ``eventually_primeError_le_rpow
    [``star_inequality, ``Data.short_forms, ``Data.enough_forms, ``Data.integral_forms_long]
    false none true (arithmeticOnly := true)
  audit ``entireL_ne_zero_of_primeError_le [``exists_entireL_quadTwist_ne_zero] (arithmeticOnly := true)
  audit ``weighted_upper_at [``eventually_primeError_le_rpow] (arithmeticOnly := true)
  audit ``principal_weighted_upper [``weighted_upper_at, ``eventually_primeError_le_rpow] (arithmeticOnly := true)
  audit ``zeta_ne_zero_of_principal_weighted_upper [``entireL_ne_zero_of_primeError_le] (arithmeticOnly := true)
  audit ``principal_fixed_strip
    [``principal_weighted_upper, ``zeta_ne_zero_of_principal_weighted_upper,
     ``entireL_ne_zero_of_primeError_le, ``exists_entireL_quadTwist_ne_zero] (arithmeticOnly := true)
  audit ``actual_zero_re_le_half [``principal_fixed_strip]
  audit ``actual_critical_line_arithmetic [``actual_zero_re_le_half, ``abs_re_sub_half_le_of_re_le]
  audit ``both_parity_zero_floor_arithmetic
    [``actual_critical_line_arithmetic, ``principal_fixed_strip,
     ``evenMomentSliceLowerBound_zero_of_critical_line, ``oddMomentSliceLowerBound_zero_of_critical_line]
  audit ``step4C1_native_arithmetic
    [``both_parity_zero_floor_arithmetic, ``principal_fixed_strip,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line] false (some ``CofinalMomentSliceVanishingErrorBounds)
  audit ``riemannHypothesis_step4_native_arithmetic
    [``step4C1_native_arithmetic, ``riemannHypothesis_of_cofinal_moment_slice_bounds,
     ``eventually_primeError_le_rpow, ``entireL_ne_zero_of_primeError_le,
     ``actual_zero_re_le_half, ``actual_critical_line_arithmetic,
     ``evenMomentSliceLowerBound_zero_of_critical_line,
     ``oddMomentSliceLowerBound_zero_of_critical_line] false (some ``RiemannHypothesis) true
