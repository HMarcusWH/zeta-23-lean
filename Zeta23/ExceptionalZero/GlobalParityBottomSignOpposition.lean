import Zeta23.ExceptionalZero.ApertureFreedom
import Zeta23.CCM.CanonicalSmallApertureGroundSpectrum
import Zeta23.CCM.GlobalParityBottomSpectrum

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Post-#276 fixed-size ground sign opposition

PR #276 proves that every legal successor ground starts at least one unit above
zero throughout the small-aperture range.  The older aperture-freedom theorem
says that a hypothetical off-line zeta zero makes every sufficiently large
aperture bad at some finite size.

This file composes those two unconditional interfaces at one and the same
finite successor index.  It does not use residual-state regularity, a selected
ground eigenvector, fixed-cell propagation, seam transfer, continuity, or an RH
premise.
-/

/-- A hypothetical off-line zero forces one fixed successor index whose legal
ground is at least one at any chosen small-aperture anchor and strictly negative
at a later aperture. -/
theorem exists_fixedN_ground_sign_opposition_of_offLine_zero
    {Lsmall : ℝ}
    (hLsmall : 0 < Lsmall)
    (hsmall : Lsmall ≤ (1 : ℝ) / 512)
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ Lneg : ℝ,
        Lsmall < Lneg ∧
        1 ≤ globalParitySuccessorBottom Lsmall N ∧
        globalParitySuccessorBottom Lneg N < 0 := by
  obtain ⟨L₀, _hL₀, hbadAll⟩ :=
    eventually_all_apertures_have_anyParityBad_of_offLine_zero ρ₀ hoff
  let Lneg : ℝ := max L₀ Lsmall + 1
  have hL₀lt : L₀ < Lneg := by
    dsimp [Lneg]
    have hle : L₀ ≤ max L₀ Lsmall := le_max_left _ _
    linarith
  have hsmalllt : Lsmall < Lneg := by
    dsimp [Lneg]
    have hle : Lsmall ≤ max L₀ Lsmall := le_max_right _ _
    linarith
  obtain ⟨K, hbad⟩ := hbadAll Lneg hL₀lt
  have hK : 2 ≤ K := two_le_of_anyParityBad hbad
  let N : ℕ := K - 1
  have hN : 1 ≤ N := by
    dsimp [N]
    omega
  have hsucc : N + 1 = K := by
    dsimp [N]
    omega
  have hbase :
      1 ≤ globalParitySuccessorBottom Lsmall N :=
    one_le_globalParitySuccessorBottom_of_smallAperture
      hLsmall hsmall N hN
  have hneg :
      globalParitySuccessorBottom Lneg N < 0 := by
    apply globalParitySuccessorBottom_neg_of_anyParityBad
    rw [hsucc]
    exact hbad
  exact ⟨N, hN, Lneg, hsmalllt, hbase, hneg⟩

/-- Existential off-line-zero wrapper for fixed-size sign opposition. -/
theorem exists_fixedN_ground_sign_opposition_of_exists_offLine_zero
    {Lsmall : ℝ}
    (hLsmall : 0 < Lsmall)
    (hsmall : Lsmall ≤ (1 : ℝ) / 512)
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ Lneg : ℝ,
        Lsmall < Lneg ∧
        1 ≤ globalParitySuccessorBottom Lsmall N ∧
        globalParitySuccessorBottom Lneg N < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_fixedN_ground_sign_opposition_of_offLine_zero
      hLsmall hsmall ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_fixedN_ground_sign_opposition_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_fixedN_ground_sign_opposition_of_exists_offLine_zero
