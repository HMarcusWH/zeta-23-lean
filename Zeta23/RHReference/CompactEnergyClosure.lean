import Zeta23.OPICATerminal.PowerDetectorSupply
import Zeta23.RHReference.CompactEnergyRate
import Zeta23.RHReference.Step123MomentHandoff

/-!
Native energy closure at the original quartic cutoff. The estimate on
the literal ramp and the fixed-strip arithmetic are explicit parameters.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier Zeta23.OPICARound6.PrimeDeficit

namespace Zeta23.RHReference

/-- Evaluate the ramp integral on the line `1/2 + t`, given zero
    exclusion to the right of the strictly smaller `1/2 + t/2`. -/
def LiteralRampFixedStripTransfer : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 / 2 →
    (∀ s : ℂ, 1 / 2 + t / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, literalG x ≤ A * x ^ (1 / 2 + t)

/-- A pointwise upper bound on the literal source survives the complete
    positive-part square and integration over the native window. -/
theorem literal_energy_eventually_le {t A : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A)
    (hu : ∀ᶠ x : ℝ in atTop, literalG x ≤ A * x ^ (1 / 2 + t)) :
    ∀ᶠ Y : ℝ in atTop, literalGEnergy Y ≤ (A ^ 2 / (2 * t)) * Y ^ (3 * t) := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 hu
  refine eventually_atTop.2 ⟨max X 2, fun Y hY => ?_⟩
  have hY₂ : 2 ≤ Y := (le_max_right X (2 : ℝ)).trans hY
  have hYpos : 0 < Y := by linarith
  unfold literalGEnergy
  simp only [OPICAExtractionR1.native_literalG_eq_rampG]
  exact OPICAExtractionR1.window_energy_bound OPICAExtractionR1.rampG hY₂ ht hA
    (OPICAExtractionR1.rampG_continuousOn_pos hYpos) (fun x hx => by
      rw [← OPICAExtractionR1.native_literalG_eq_rampG]
      exact hX x (((le_max_left X (2 : ℝ)).trans hY).trans hx.1))

/-- Compare at the original cutoff. The same aperture provides both full
    parity bounds, from which the disjunctive C1 contract follows. -/
theorem c1_of_fixed_energy_upper {δ t C : ℝ}
    (hmargin : 0 < δ - 3 * t)
    (hcompare : Zeta23.OPICATerminal.BothParityPowerComparison δ)
    (hupper : ∀ᶠ Y : ℝ in atTop, literalGEnergy Y ≤ C * Y ^ (3 * t)) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  obtain ⟨Y₀, h₀⟩ := hcompare
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨Y₁, h₁⟩ := eventually_atTop.1
    (eventually_scaled_energy_small hmargin hnpos hupper)
  let Y := max (max Y₀ Y₁) (Real.exp ((n : ℝ) + 2))
  have hy₀ : Y₀ ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hy₁ : Y₁ ≤ Y := (le_max_right _ _).trans (le_max_left _ _)
  have hyexp : Real.exp ((n : ℝ) + 2) ≤ Y := le_max_right _ _
  obtain ⟨hy₂, htolerance⟩ := h₁ Y hy₁
  have hlate : (n : ℝ) + 2 ≤ Real.log Y := by
    rw [← Real.log_exp ((n : ℝ) + 2)]
    exact Real.log_le_log (Real.exp_pos _) hyexp
  have hb := h₀ Y (max_le hy₀ hy₂)
  exact ⟨Real.log Y, hlate, Or.inl (hb.1.mono htolerance)⟩

/-- The caller supplies one threshold beneath the evaluation line, matched
    to the native comparison margin. -/
theorem compact_energy_c1_of_fixed_strip {δ t : ℝ}
    (hcompare : Zeta23.OPICATerminal.BothParityPowerComparison δ)
    (ht : 0 < t) (ht₁ : t < 1 / 2) (hmargin : 0 < δ - 3 * t)
    (hzero : ∀ s : ℂ, 1 / 2 + t / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (htransfer : LiteralRampFixedStripTransfer) :
    CofinalMomentSliceVanishingErrorBounds := by
  obtain ⟨A, hA, hu⟩ := htransfer t ht ht₁ hzero
  exact c1_of_fixed_energy_upper hmargin hcompare (literal_energy_eventually_le ht hA hu)

/-- Conditional terminal proof through the generated original trial pair. -/
theorem compact_energy_reference_of_fixed_strip {δ t : ℝ}
    (hcompare : Zeta23.OPICATerminal.BothParityPowerComparison δ)
    (ht : 0 < t) (ht₁ : t < 1 / 2) (hmargin : 0 < δ - 3 * t)
    (hzero : ∀ s : ℂ, 1 / 2 + t / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (htransfer : LiteralRampFixedStripTransfer) :
    RiemannHypothesis :=
  riemannHypothesis_of_c1_through_generated_pair
    (compact_energy_c1_of_fixed_strip hcompare ht ht₁ hmargin hzero htransfer)

end Zeta23.RHReference

#print axioms Zeta23.RHReference.literal_energy_eventually_le
#print axioms Zeta23.RHReference.c1_of_fixed_energy_upper
#print axioms Zeta23.RHReference.compact_energy_c1_of_fixed_strip
#print axioms Zeta23.RHReference.compact_energy_reference_of_fixed_strip
