import Zeta23.RHReference.DirectWindowContract
import Zeta23.OPICATerminal.Energy

/-!
# Positive energy on a supplied arithmetic window

Only the complete interval supplied by the arithmetic theorem is integrated.
Taking the positive part requires a one-sided upper bound, not an absolute
bound on the literal source.
-/

set_option autoImplicit false

noncomputable section

open Zeta23.OPICARound6.PrimeDeficit

namespace Zeta23.RHReference

/-- Integrate one complete supplied window, preserving the native energy. -/
theorem literal_energy_le_of_window {Y t A : ℝ}
    (hY : 2 ≤ Y) (ht : 0 < t) (hA : 0 ≤ A)
    (hupper : LiteralWindowUpper t A Y) :
    literalGEnergy Y ≤ (A ^ 2 / (2 * t)) * Y ^ (3 * t) := by
  have hYpos : 0 < Y := by linarith
  unfold literalGEnergy
  simp only [OPICAExtractionR1.native_literalG_eq_rampG]
  exact OPICAExtractionR1.window_energy_bound OPICAExtractionR1.rampG hY ht hA
    (OPICAExtractionR1.rampG_continuousOn_pos hYpos) (fun x hx => by
      rw [← OPICAExtractionR1.native_literalG_eq_rampG]
      exact hupper x hx)

/-- Integration preserves the cofinal quantifiers. It does not promote the
arithmetic bound to an eventual estimate at every large scale. -/
theorem cofinal_energy_upper_of_windows {t A : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A)
    (hupper : CofinalLiteralWindowUpper t A) :
    CofinalWindowEnergyUpper (3 * t) (A ^ 2 / (2 * t)) := by
  intro B
  obtain ⟨Y, hY, hwindow⟩ := hupper B
  exact ⟨Y, hY,
    literal_energy_le_of_window ((le_max_right B (2 : ℝ)).trans hY) ht hA hwindow⟩

end Zeta23.RHReference

#print axioms Zeta23.RHReference.literal_energy_le_of_window
#print axioms Zeta23.RHReference.cofinal_energy_upper_of_windows
