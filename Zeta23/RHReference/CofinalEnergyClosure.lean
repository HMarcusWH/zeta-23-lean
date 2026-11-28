import Zeta23.RHReference.DirectWindowEnergy
import Zeta23.RHReference.CompactEnergyRate
import Zeta23.OPICATerminal.PowerDetectorSupply
import Zeta23.RHReference.Step123MomentHandoff

/-!
# Cofinal literal energy closes through the actual generated trial pair

The elementary model power is eventually small. A supplied arithmetic window
is then selected beyond that threshold. The proof never treats a cofinal
arithmetic upper bound as an eventual arithmetic upper bound.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open Zeta23.OPICARound4.ArithmeticFrontier Zeta23.OPICARound6.PrimeDeficit

namespace Zeta23.RHReference

/-- A strict exponent gap gives normalized smallness on arbitrarily late
supplied windows. The eventual estimate is applied only to the explicit power
model, for which its upper-bound premise is reflexive everywhere. -/
theorem cofinal_normalized_energy_of_power_upper {δ κ C : ℝ}
    (hgap : 0 < δ - κ)
    (hupper : CofinalWindowEnergyUpper κ C) :
    CofinalNormalizedLiteralEnergy δ := by
  intro n hn B
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmodel : ∀ᶠ Y : ℝ in atTop, C * Y ^ κ ≤ C * Y ^ κ :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  obtain ⟨Y₀, h₀⟩ := eventually_atTop.1
    (eventually_scaled_energy_small (energy := fun Y : ℝ => C * Y ^ κ)
      hgap hnpos hmodel)
  obtain ⟨Y, hY, henergy⟩ := hupper (max B Y₀)
  have hBY : max B 2 ≤ Y :=
    (max_le_max (le_max_left B Y₀) le_rfl).trans hY
  have hY₀ : Y₀ ≤ Y :=
    (le_max_right B Y₀).trans ((le_max_left _ _).trans hY)
  have hY₂ : 2 ≤ Y := (le_max_right _ _).trans hY
  have hYnonneg : 0 ≤ Y := by linarith
  refine ⟨Y, hBY, ?_⟩
  exact (div_le_div_of_nonneg_right henergy (Real.rpow_nonneg hYnonneg δ)).trans
    (h₀ Y hY₀).2

/-- Choose the supplied window after the comparison onset and after
`exp (n + 2)`. Both full parity bounds hold at this same aperture; the even
one already gives the disjunctive C1 contract at the original cutoff. -/
theorem c1_of_cofinal_normalized_energy {δ : ℝ}
    (hcompare : Zeta23.OPICATerminal.BothParityPowerComparison δ)
    (hsmall : CofinalNormalizedLiteralEnergy δ) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  obtain ⟨Y₀, h₀⟩ := hcompare
  obtain ⟨Y, hY, htolerance⟩ := hsmall n hn (max Y₀ (Real.exp ((n : ℝ) + 2)))
  have hy₀ : Y₀ ≤ Y :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hY)
  have hyexp : Real.exp ((n : ℝ) + 2) ≤ Y :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hY)
  have hy₂ : 2 ≤ Y := (le_max_right _ _).trans hY
  have hlate : (n : ℝ) + 2 ≤ Real.log Y := by
    rw [← Real.log_exp ((n : ℝ) + 2)]
    exact Real.log_le_log (Real.exp_pos _) hyexp
  have hb := h₀ Y (max_le hy₀ hy₂)
  exact ⟨Real.log Y, hlate, Or.inl (hb.1.mono htolerance)⟩

/-- Fix the arithmetic exponent once, after obtaining the native comparison
exponent and before selecting any of the cofinal windows. -/
theorem c1_of_direct_windows
    (hupper : DirectArithmeticWindowSupply) :
    CofinalMomentSliceVanishingErrorBounds := by
  obtain ⟨δ, hδ, hcompare⟩ := Zeta23.OPICATerminal.bothParityPowerComparison_proved
  let t : ℝ := min (δ / 12) (1 / 8)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by positivity) (by norm_num)
  have htδ : t ≤ δ / 12 := min_le_left _ _
  have hgap : 0 < δ - 3 * t := by linarith
  have henergy := cofinal_energy_upper_of_windows ht (by norm_num : (0 : ℝ) ≤ 1)
    (hupper t ht)
  exact c1_of_cofinal_normalized_energy hcompare
    (cofinal_normalized_energy_of_power_upper hgap henergy)

/-- The conditional consumer uses the actual generated even and odd trials.
The only arithmetic premise is the direct complete-window supplier. -/
theorem riemannHypothesis_of_direct_windows
    (hupper : DirectArithmeticWindowSupply) : RiemannHypothesis :=
  riemannHypothesis_of_c1_through_generated_pair (c1_of_direct_windows hupper)

end Zeta23.RHReference

#print axioms Zeta23.RHReference.cofinal_normalized_energy_of_power_upper
#print axioms Zeta23.RHReference.c1_of_cofinal_normalized_energy
#print axioms Zeta23.RHReference.c1_of_direct_windows
#print axioms Zeta23.RHReference.riemannHypothesis_of_direct_windows
