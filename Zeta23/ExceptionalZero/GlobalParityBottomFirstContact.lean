import Zeta23.ExceptionalZero.GlobalParityBottomSignOpposition
import Zeta23.CCM.GlobalParityBottomContactNormalForm

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Post-#277 counterexample-generated zero contact

This module composes the merged fixed-N sign-opposition theorem with the exact
continuity interface.  The continuity proposition remains OPEN here; no theorem
below upgrades it to authority.

Once production fixed-N continuity is proved independently, an assumed off-line
zero generates a legal finite zero-contact state at the same successor index.
RH remains OPEN.
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

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.nonempty_globalParityBottomZeroContact_of_exists_offLine_zero
