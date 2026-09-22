import Zeta23.ExceptionalZero.ApertureFreedom
import Zeta23.CCM.WholeCellBiRegularCanonicalEnergy

noncomputable section

namespace Zeta23.ExceptionalZero

open Real Set
open Zeta23.CCM

/-!
# Off-line-generated whole-cell retained family

A hypothetical off-line zeta zero forces finite canonical badness at every
sufficiently large aperture.  Earlier terminal wrappers selected one physical
cutoff cell and then discarded that aperture-family provenance.

This module preserves it.  Every sufficiently far-out physical cutoff cell is
bad at every aperture (with finite size allowed to vary), and therefore admits
the existing bi-regular retained negative-energy certificate while keeping that
whole-cell ancestry.  Such retained states consequently occur at arbitrarily
large apertures.

No contact theorem, scalar orientation theorem, branch exclusion, or RH claim
is made here.
-/

/-- A hypothetical off-line zero forces a whole-cell bi-regular retained
negative-energy state in every physical cutoff cell whose left endpoint lies
beyond the eventual-badness threshold. -/
theorem
    eventually_all_cutoffCells_have_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ Q : ℕ, 1 ≤ Q →
        L₀ < Real.log (Q : ℝ) →
          Nonempty (WholeCellBiRegularNegativeEnergyCertificate Q) := by
  obtain ⟨L₀, hL₀, hbadAll⟩ :=
    eventually_all_apertures_have_anyParityBad_of_offLine_zero ρ₀ hoff
  refine ⟨L₀, hL₀, ?_⟩
  intro Q hQ hQabove
  have hall : WholeCellAnyParityBad Q := by
    intro L hL
    exact hbadAll L (lt_trans hQabove hL.1)
  exact exists_wholeCellBiRegular_negativeEnergyCertificate Q hQ hall

/-- Off-line-generated whole-cell retained states occur at arbitrarily large
physical apertures. -/
theorem
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ c : WholeCellBiRegularNegativeEnergyCertificate Q,
        A < c.retained.energy.firstBad.L := by
  obtain ⟨L₀, _hL₀, hcells⟩ :=
    eventually_all_cutoffCells_have_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff
  obtain ⟨Q, hQ, hlogQ⟩ :=
    exists_fixedCanonicalCutoffCell_above (max A L₀)
  have hL₀logQ : L₀ < Real.log (Q : ℝ) :=
    lt_of_le_of_lt (le_max_right A L₀) hlogQ
  obtain ⟨c⟩ := hcells Q hQ hL₀logQ
  have hAlogQ : A < Real.log (Q : ℝ) :=
    lt_of_le_of_lt (le_max_left A L₀) hlogQ
  exact ⟨Q, c, lt_trans hAlogQ c.retained.energy.firstBad.L_mem.1⟩

/-- Existential wrapper for arbitrary-large whole-cell retained provenance. -/
theorem
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ c : WholeCellBiRegularNegativeEnergyCertificate Q,
        A < c.retained.energy.firstBad.L := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hρ₀ A

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.eventually_all_cutoffCells_have_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_exists_offLine_zero
