import Zeta23.ExceptionalZero.OffLineGeneratedRetainedFamily
import Zeta23.CCM.GlobalFirstBadParityBottom

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Matrix Set
open Zeta23.CCM
open scoped ComplexConjugate

/-!
# PR #247 — historical compatibility projection: off-line zero to global parity ground state

This file is retained as a historical compatibility projection. The active #247\nroute now runs through `GlobalParityBottomGeneratedState` and the typed\n`GlobalBottomArithmeticResidual`; this naked trichotomy projection is not\nimported by `Zeta23.ExceptionalZero`.\n\nThis was the original exceptional-zero attachment for the new global-bottom geometry.
A hypothetical off-line zero already produces whole-cell bi-regular retained
negative-energy certificates at arbitrarily large aperture.  The retained
first-bad state now additionally carries a strictly negative common parity
ground shift and an exact even-strict / tie / odd-strict classification.

This is a reduction theorem, not a closure theorem.
-/

/-- Arbitrarily far out in aperture, an off-line zero forces a retained
first-bad state whose common two-parity spectral bottom is negative and whose
two parity bottoms fall into the exact trichotomy used by the #247 closure
attempt. -/
theorem
    exists_arbitrarilyLarge_globalParityBottom_state_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ c : WholeCellBiRegularNegativeEnergyCertificate Q,
        A < c.retained.energy.firstBad.L ∧
        globalParitySuccessorBottom
            c.retained.energy.firstBad.L
            c.retained.energy.firstBad.Nstar < 0 ∧
        (parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) <
            parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) ∨
          parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) =
            parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) ∨
          parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) <
            parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1)) := by
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  let fb := c.retained.energy.firstBad
  have hneg : globalParitySuccessorBottom fb.L fb.Nstar < 0 :=
    fb.globalParityBottom_neg
  have htri := fb.parityBottom_trichotomy
  exact ⟨Q, c, hlarge, by simpa [fb] using hneg, by simpa [fb] using htri⟩

/-- Existential off-line-zero wrapper. -/
theorem
    exists_arbitrarilyLarge_globalParityBottom_state_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ,
      ∃ c : WholeCellBiRegularNegativeEnergyCertificate Q,
        A < c.retained.energy.firstBad.L ∧
        globalParitySuccessorBottom
            c.retained.energy.firstBad.L
            c.retained.energy.firstBad.Nstar < 0 ∧
        (parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) <
            parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) ∨
          parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) =
            parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) ∨
          parityRayleighBottom .odd
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1) <
            parityRayleighBottom .even
              c.retained.energy.firstBad.L
              (c.retained.energy.firstBad.Nstar + 1)) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_arbitrarilyLarge_globalParityBottom_state_of_offLine_zero
    ρ₀ hρ₀ A

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalParityBottom_state_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_globalParityBottom_state_of_exists_offLine_zero
