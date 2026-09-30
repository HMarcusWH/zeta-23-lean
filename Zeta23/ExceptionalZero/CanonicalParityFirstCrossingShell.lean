import Zeta23.ExceptionalZero.GlobalParityBottomSignOpposition
import Zeta23.CCM.CanonicalParityFirstCrossingShell

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Post-#278 counterexample-generated parity first crossing

A hypothetical off-line zero already produces same-fixed-N global ground sign
opposition.  The global negative endpoint selects one responsible parity.  The
same parity is positive at the small-aperture anchor, so production continuity
gives its first negative boundary.

The unconditional CCM reductions then extract the zero plateau, exact kernel
tower, and least right-crossing truncation index.

This is a counterexample-generated structural state, not a contradiction.
RH remains OPEN.
-/

/-- One hypothetical off-line zero produces a fixed-parity first-negative
boundary. -/
theorem exists_parityFirstNegativeBoundary_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ c : ParityFirstNegativeBoundary, True := by
  obtain ⟨N, hN, Lneg, hLt, hbase, hneg⟩ :=
    exists_fixedN_ground_sign_opposition_of_offLine_zero
      (Lsmall := (1 : ℝ) / 512)
      (by norm_num) le_rfl ρ₀ hoff
  obtain ⟨p, hpbase, hpneg⟩ :=
    exists_parity_ground_sign_opposition_of_global hbase hneg
  have hpbasePos :
      0 < paritySuccessorGround p N ((1 : ℝ) / 512) := by
    linarith
  obtain ⟨c, _hp, _hN, _hsmall, _hnegL⟩ :=
    exists_parityFirstNegativeBoundary_of_signOpposition
      p hN
      (Lsmall := (1 : ℝ) / 512)
      (Lneg := Lneg)
      (by norm_num) hLt hpbasePos hpneg
  exact ⟨c, trivial⟩

/-- Existential off-line-zero wrapper for the fixed-parity first boundary. -/
theorem exists_parityFirstNegativeBoundary_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ c : ParityFirstNegativeBoundary, True := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_parityFirstNegativeBoundary_of_offLine_zero ρ₀ hρ₀

/-- Main post-#278 structural reduction: every hypothetical off-line zero
produces a finite canonical parity first-crossing shell carrying an exact zero
plateau and inherited kernel tower. -/
theorem nonempty_canonicalParityFirstCrossingShell_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    Nonempty CanonicalParityFirstCrossingShell := by
  obtain ⟨b, _⟩ :=
    exists_parityFirstNegativeBoundary_of_offLine_zero ρ₀ hoff
  obtain ⟨z, _⟩ := b.exists_zeroPlateau
  obtain ⟨t, _⟩ := z.exists_kernelTower
  obtain ⟨c, _⟩ := t.exists_firstCrossingShell
  exact ⟨c⟩

/-- Existential wrapper of the first-crossing-shell producer. -/
theorem nonempty_canonicalParityFirstCrossingShell_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    Nonempty CanonicalParityFirstCrossingShell := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact nonempty_canonicalParityFirstCrossingShell_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_parityFirstNegativeBoundary_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_canonicalParityFirstCrossingShell_of_offLine_zero
