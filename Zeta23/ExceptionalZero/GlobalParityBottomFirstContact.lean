import Zeta23.ExceptionalZero.GlobalParityBottomSignOpposition
import Zeta23.CCM.GlobalParityBottomContactNormalForm

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Post-#277 counterexample-generated zero contact

This module composes the merged fixed-N sign-opposition theorem with the exact
continuity interface.  The production continuity theorem is checked in as a
candidate, but it does not become theorem authority until the exact PR head
passes the compiler and axiom-validation gates.

Once production fixed-N continuity is compiler-validated independently, an
assumed off-line zero generates a legal finite zero-contact state at the same
successor index.  RH remains OPEN.
-/

theorem nonempty_globalParityBottomZeroContact_of_offLine_zero
    (hcont : CanonicalFixedNGroundContinuity)
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    Nonempty GlobalParityBottomZeroContact := by
  obtain ⟨N, hN, Lneg, hLt, hbase, hneg⟩ :=
    exists_fixedN_ground_sign_opposition_of_offLine_zero
      (Lsmall := (1 : ℝ) / 512)
      (by norm_num) le_rfl ρ₀ hoff
  obtain ⟨c, _hN, _hsmall, _hnegL⟩ :=
    exists_globalParityBottomZeroContact_of_signOpposition
      hcont hN
      (Lsmall := (1 : ℝ) / 512)
      (Lneg := Lneg)
      (by norm_num) le_rfl hLt hbase hneg
  exact ⟨c⟩

theorem nonempty_globalParityBottomZeroContact_of_exists_offLine_zero
    (hcont : CanonicalFixedNGroundContinuity)
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    Nonempty GlobalParityBottomZeroContact := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact nonempty_globalParityBottomZeroContact_of_offLine_zero
    hcont ρ₀ hρ₀

/-- Unconditional post-#277 composition: once the production continuity
theorem is discharged in CCM, an assumed off-line zero forces an exact same-N
legal zero contact. -/
theorem nonempty_globalParityBottomZeroContact_proved_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    Nonempty GlobalParityBottomZeroContact :=
  nonempty_globalParityBottomZeroContact_of_offLine_zero
    canonicalFixedNGroundContinuity_proved ρ₀ hoff

/-- Existential wrapper of the unconditional zero-contact theorem. -/
theorem nonempty_globalParityBottomZeroContact_proved_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    Nonempty GlobalParityBottomZeroContact :=
  nonempty_globalParityBottomZeroContact_of_exists_offLine_zero
    canonicalFixedNGroundContinuity_proved hoff

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_of_exists_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_proved_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_proved_of_exists_offLine_zero
