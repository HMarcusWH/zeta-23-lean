import Zeta23.ExceptionalZero.RegularFirstBadClosure
import Zeta23.CCM.RegularFirstBadRieszEnergy

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Real Set
open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03F: exceptional-zero Riesz closure

This is a thin wrapper around the retained #153/#150 regular first-bad
certificate.  A hypothetical off-line zero yields the same complete certificate
and therefore, by the production FB-03E/FB-03F theorems, a strictly negative
complete order-six Riesz source-channel energy.

No nonnegativity theorem, negative-root exclusion theorem, finite-to-infinite
closure, or RH theorem is asserted here.
-/

/-- A hypothetical off-line zero forces a retained regular first-bad
certificate whose complete order-six Riesz source channel is strictly
negative. -/
theorem exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ Q : ℕ,
      ∃ c : RegularCellMinimalNegativeEnergyCertificate Q,
        canonicalRieszSourceChannelEnergy
            c.firstBad.L 6 (c.firstBad.Nstar + 1)
            (cubicZeroShiftTrialVector
              c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
              EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 := by
  obtain ⟨Q, hc⟩ :=
    exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero ρ₀ hoff
  obtain ⟨c⟩ := hc
  exact ⟨Q, c, c.rieszSixNeg⟩

/-- Existential off-line-zero wrapper preserving the complete retained
certificate alongside the transformed negative source channel. -/
theorem exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ Q : ℕ,
      ∃ c : RegularCellMinimalNegativeEnergyCertificate Q,
        canonicalRieszSourceChannelEnergy
            c.firstBad.L 6 (c.firstBad.Nstar + 1)
            (cubicZeroShiftTrialVector
              c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
              EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
    ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
