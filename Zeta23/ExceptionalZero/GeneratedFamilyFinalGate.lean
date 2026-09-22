import Zeta23.ExceptionalZero.OffLineGeneratedRetainedFamily
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Generated-family final gate

PR #243 preserves the aperture-family provenance of a hypothetical off-line
zero: whole-cell bi-regular retained negative-energy certificates occur at
arbitrarily large physical apertures.

The exact remaining generated-family gate can therefore be stated much more
weakly than `NoRegularFirstBadCertificates`: it is enough to prove that all
whole-cell bi-regular retained certificates are bounded above in aperture.

This file proves only the terminal composition of that one gate.  It does not
prove the bound itself, does not add a contact theory, and does not claim RH
unconditionally.
-/

/-- Exact generated-family final gate.

A uniform upper bound on the retained aperture of every whole-cell bi-regular
negative-energy certificate contradicts the arbitrarily-large family forced by
any off-line zero.

This is intentionally weaker than excluding every retained certificate. -/
def NoArbitrarilyLargeWholeCellRetainedFamily : Prop :=
  ∃ A : ℝ,
    ∀ Q : ℕ,
      ∀ c : WholeCellBiRegularNegativeEnergyCertificate Q,
        c.retained.energy.firstBad.L ≤ A

/-- The generated-family final gate excludes every off-line zeta zero. -/
theorem no_offLine_zero_of_noArbitrarilyLargeWholeCellRetainedFamily
    (hno : NoArbitrarilyLargeWholeCellRetainedFamily) :
    ¬ ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2 := by
  rintro ⟨ρ₀, hoff⟩
  obtain ⟨A, hA⟩ := hno
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  exact (not_lt_of_ge (hA Q c)) hlarge

/-- The generated-family final gate implies the repository's strip-zero form
of RH. -/
theorem criticalLine_of_noArbitrarilyLargeWholeCellRetainedFamily
    (hno : NoArbitrarilyLargeWholeCellRetainedFamily) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  exact
    (no_offLine_zero_of_noArbitrarilyLargeWholeCellRetainedFamily hno)
      ⟨⟨ρ, hρ⟩, hoff⟩

/-- **Generated-family terminal composition.**

If the single generated-family aperture-bound gate is proved, the already
validated Mathlib statement seam closes the exact `RiemannHypothesis`.
The hypothesis of this theorem remains OPEN. -/
theorem riemannHypothesis_of_noArbitrarilyLargeWholeCellRetainedFamily
    (hno : NoArbitrarilyLargeWholeCellRetainedFamily) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs :
      IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  exact
    criticalLine_of_noArbitrarilyLargeWholeCellRetainedFamily hno s hmem

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.NoArbitrarilyLargeWholeCellRetainedFamily
#print axioms Zeta23.ExceptionalZero.no_offLine_zero_of_noArbitrarilyLargeWholeCellRetainedFamily
#print axioms Zeta23.ExceptionalZero.criticalLine_of_noArbitrarilyLargeWholeCellRetainedFamily
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_noArbitrarilyLargeWholeCellRetainedFamily
