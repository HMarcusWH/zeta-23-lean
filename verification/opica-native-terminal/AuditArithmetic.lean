import Zeta23Arithmetic.NativePrincipal
import Zeta23.OPICANativeTerminal.AuditCore
open Lean Elab Command Filter Real
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

open OPICANativeTerminalAudit
set_option maxHeartbeats 0 in
run_cmd do
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
