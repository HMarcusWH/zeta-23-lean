import Zeta23.CCM.BiRegularFirstBadCanonicalEnergy

noncomputable section

namespace Zeta23.CCM

open Set

/-!
# Whole-cell bi-regular retained negative-energy provenance

The ordinary retained first-bad certificate remembers whole-cell minimality of
its selected size, but not the stronger fact that every aperture in the same
physical cutoff cell remains bad at some finite size.

This module packages that stronger aperture-family property together with the
existing bi-regular retained negative-energy certificate.  No fixed finite size
or fixed witness is asserted to remain bad across the whole cell.

No branch exclusion, contact theorem, large-aperture sign theorem, or RH claim
is made here.
-/

/-- Every aperture in one physical cutoff cell is bad at some finite size.
The bad size is allowed to depend on the aperture. -/
def WholeCellAnyParityBad (Q : ℕ) : Prop :=
  ∀ L : ℝ, L ∈ fixedCanonicalCutoffCell Q →
    ∃ K : ℕ, AnyParityBad L K

/-- A bi-regular retained negative-energy state together with the stronger
whole-cell fact that no aperture in its physical cutoff cell is globally good
at all finite sizes. -/
structure WholeCellBiRegularNegativeEnergyCertificate (Q : ℕ) where
  retained : BiRegularCellMinimalNegativeEnergyCertificate Q
  wholeCellBad : WholeCellAnyParityBad Q

/-- Whole-cell badness can be combined with the already-proved bi-regular
selection theorem without discarding the family property. -/
theorem exists_wholeCellBiRegular_negativeEnergyCertificate
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hall : WholeCellAnyParityBad Q) :
    Nonempty (WholeCellBiRegularNegativeEnergyCertificate Q) := by
  obtain ⟨L, hL⟩ := fixedCanonicalCutoffCell_nonempty Q hQ
  obtain ⟨K, hbad⟩ := hall L hL
  have hcell : CellAnyParityBad Q K := ⟨L, hL, hbad⟩
  obtain ⟨c⟩ :=
    exists_biRegular_cellMinimal_negativeCanonicalEnergyCertificate
      Q hQ ⟨K, hcell⟩
  exact ⟨{
    retained := c
    wholeCellBad := hall
  }⟩

/-- Any bad size occurring anywhere in the retained physical cell is at least
the whole-cell minimal size stored by the retained certificate. -/
theorem WholeCellBiRegularNegativeEnergyCertificate.badSize_ge_cellMinimum
    {Q : ℕ}
    (c : WholeCellBiRegularNegativeEnergyCertificate Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q)
    {K : ℕ} (hbad : AnyParityBad L K) :
    c.retained.energy.firstBad.Kstar ≤ K := by
  by_contra hnot
  have hlt : K < c.retained.energy.firstBad.Kstar := Nat.lt_of_not_ge hnot
  exact
    (c.retained.energy.firstBad.cell_minimal K hlt)
      ⟨L, hL, hbad⟩

/-- At every aperture in the cell, some bad size survives at or above the
retained whole-cell minimum. -/
theorem
    WholeCellBiRegularNegativeEnergyCertificate.exists_bad_at_or_above_cellMinimum
    {Q : ℕ}
    (c : WholeCellBiRegularNegativeEnergyCertificate Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q) :
    ∃ K : ℕ,
      c.retained.energy.firstBad.Kstar ≤ K ∧
      AnyParityBad L K := by
  obtain ⟨K, hbad⟩ := c.wholeCellBad L hL
  exact ⟨K, c.badSize_ge_cellMinimum hL hbad, hbad⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.WholeCellAnyParityBad
#print axioms Zeta23.CCM.WholeCellBiRegularNegativeEnergyCertificate
#print axioms Zeta23.CCM.exists_wholeCellBiRegular_negativeEnergyCertificate
#print axioms Zeta23.CCM.WholeCellBiRegularNegativeEnergyCertificate.badSize_ge_cellMinimum
#print axioms Zeta23.CCM.WholeCellBiRegularNegativeEnergyCertificate.exists_bad_at_or_above_cellMinimum
