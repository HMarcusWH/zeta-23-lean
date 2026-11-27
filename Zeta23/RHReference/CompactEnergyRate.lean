import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Turn a strict exponent gap into a prescribed eventual energy tolerance. -/

set_option autoImplicit false

open Filter

namespace Zeta23.RHReference

theorem eventually_scaled_energy_small {energy : ℝ → ℝ} {δ κ C n : ℝ}
    (hgap : 0 < δ - κ) (hn : 0 < n)
    (henergy : ∀ᶠ Y : ℝ in atTop, energy Y ≤ C * Y ^ κ) :
    ∀ᶠ Y : ℝ in atTop, 2 ≤ Y ∧ energy Y / Y ^ δ ≤ 1 / n := by
  have hcoefficient : ∀ᶠ Y : ℝ in atTop, C * n ≤ Y ^ (δ - κ) :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (C * n)
  filter_upwards [henergy, hcoefficient, eventually_ge_atTop (2 : ℝ)] with Y hY hC hY₂
  have hYpos : 0 < Y := by linarith
  refine ⟨hY₂, (div_le_div_iff₀ (Real.rpow_pos_of_pos hYpos _) hn).2 ?_⟩
  simp only [one_mul]
  calc
    energy Y * n ≤ (C * Y ^ κ) * n := mul_le_mul_of_nonneg_right hY hn.le
    _ = (C * n) * Y ^ κ := by ring
    _ ≤ Y ^ (δ - κ) * Y ^ κ :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hYpos.le _)
    _ = Y ^ δ := by rw [← Real.rpow_add hYpos, sub_add_cancel]

end Zeta23.RHReference

#print axioms Zeta23.RHReference.eventually_scaled_energy_small
