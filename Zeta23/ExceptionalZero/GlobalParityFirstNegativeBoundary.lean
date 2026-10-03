import Zeta23.ExceptionalZero.GlobalParityBottomSignOpposition
import Zeta23.CCM.FirstCrossingGlobalAlignment

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Post-#281 counterexample-generated global first-negative boundary

A hypothetical off-line zeta zero already produces a same-N positive/negative
legal-ground bracket.  The pure CCM global-boundary/alignment theorems turn that
bracket into an actual first-negative boundary and selected parity shell.

This is a conditional counterexample state.  It is not a contradiction and it
does not prove RH.
-/

/-- An off-line zero produces an exact generated global first-crossing state. -/
theorem nonempty_generatedGlobalFirstCrossing_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    Nonempty GeneratedGlobalFirstCrossing := by
  obtain ⟨N, hN, Lneg, hLt, hbase, hneg⟩ :=
    exists_fixedN_ground_sign_opposition_of_offLine_zero
      (Lsmall := (1 : ℝ) / 512)
      (by norm_num) le_rfl ρ₀ hoff
  obtain ⟨c, _hN, _hsmall, _hnegL⟩ :=
    exists_globalParityFirstNegativeBoundary_of_signOpposition
      hN
      (Lsmall := (1 : ℝ) / 512)
      (Lneg := Lneg)
      (by norm_num) hLt (lt_of_lt_of_le (by norm_num) hbase) hneg
  obtain ⟨g, _hg⟩ := c.exists_generatedGlobalFirstCrossing
  exact ⟨g⟩

/-- Existential off-line-zero wrapper. -/
theorem nonempty_generatedGlobalFirstCrossing_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    Nonempty GeneratedGlobalFirstCrossing := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact nonempty_generatedGlobalFirstCrossing_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nonempty_generatedGlobalFirstCrossing_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_generatedGlobalFirstCrossing_of_exists_offLine_zero
