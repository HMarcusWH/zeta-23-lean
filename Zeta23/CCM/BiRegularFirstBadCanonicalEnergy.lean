import Zeta23.CCM.CellMinimalBiRegularFirstBad
import Zeta23.CCM.RegularFirstBadCanonicalEnergy

noncomputable section

namespace Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A4R8: bi-regular negative-energy certificate

This module carries the complete historical negative-energy certificate onto
the strengthened bi-regular retained aperture.  It deliberately reuses the
constructor from a supplied first-bad certificate so that no second existential
choice can silently move the aperture and discard simultaneous regularity.

No successor branch is excluded and no RH-directed terminal claim is made.
-/

/-- Complete retained negative-energy state together with regularity of both
parity predecessor blocks at the exact same aperture. -/
structure BiRegularCellMinimalNegativeEnergyCertificate (Q : ℕ) where
  energy : RegularCellMinimalNegativeEnergyCertificate Q
  regular_even :
    IntrinsicPredecessorRegular
      .even energy.firstBad.L energy.firstBad.Nstar
  regular_odd :
    IntrinsicPredecessorRegular
      .odd energy.firstBad.L energy.firstBad.Nstar

/-- Any cell-bad state admits the complete negative-energy certificate at a
simultaneously even/odd regular retained aperture. -/
theorem exists_biRegular_cellMinimal_negativeCanonicalEnergyCertificate
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    Nonempty (BiRegularCellMinimalNegativeEnergyCertificate Q) := by
  obtain ⟨b⟩ := exists_biRegular_cellMinimal_firstBadCertificate Q hQ hex
  obtain ⟨e, heq⟩ :=
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad b.firstBad
  refine ⟨{
    energy := e
    regular_even := ?_
    regular_odd := ?_
  }⟩
  · rw [heq]
    exact b.regular_even
  · rw [heq]
    exact b.regular_odd

end Zeta23.CCM

#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate
#print axioms Zeta23.CCM.exists_biRegular_cellMinimal_negativeCanonicalEnergyCertificate
