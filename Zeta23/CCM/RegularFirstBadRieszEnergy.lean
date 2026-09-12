import Zeta23.CCM.RegularFirstBadCanonicalEnergy
import Zeta23.CCM.CanonicalSourceRieszEnergy

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03F: retained Riesz first-bad energy

This module composes the production Riesz representation with the complete
regular first-bad certificate retained by #153.  It does not introduce a new
certificate type: whole-cell ancestry, predecessor nonnegativity, the regular
zero-shift preimage, negative explicit root, and exact channel negativity stay
attached to the same object.

Every retained first-bad trial is boundary-flat and therefore has an exact
order-six Riesz representation.  Order eight is available only when the
retained parity is even.
-/

/-- Membership in either Euclidean parity sector implies the underlying
production boundary-flat moment equations. -/
theorem boundaryFlatCoefficients_of_mem_euclideanParityBoundaryFlatSubspace
    (p : ReversalParity)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hx : x ∈ euclideanParityBoundaryFlatSubspace p K) :
    BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  cases p with
  | even =>
      have hraw := (mem_euclideanEvenBoundaryFlatSubspace_iff K x).mp hx
      exact (mem_boundaryFlatSubspace_iff K _).mp hraw.1
  | odd =>
      have hraw := (mem_euclideanOddBoundaryFlatSubspace_iff K x).mp hx
      exact (mem_boundaryFlatSubspace_iff K _).mp hraw.1

/-- The raw coordinate vector of an even Euclidean constrained carrier lies in
the even coefficient sector. -/
theorem evenCoefficientSubspace_of_mem_euclideanEvenBoundaryFlatSubspace
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hx : x ∈ euclideanEvenBoundaryFlatSubspace K) :
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
      evenCoefficientSubspace K := by
  exact ((mem_euclideanEvenBoundaryFlatSubspace_iff K x).mp hx).2

/-- The retained zero-shift trial is boundary-flat in the canonical production
coordinate sense. -/
theorem RegularCellMinimalNegativeEnergyCertificate.trial_boundaryFlat
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    BoundaryFlatCoefficients (c.firstBad.Nstar + 1)
      ((EuclideanSpace.equiv
        (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) := by
  let u := cubicZeroShiftTrialVector
    c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀
  exact boundaryFlatCoefficients_of_mem_euclideanParityBoundaryFlatSubspace
    c.firstBad.p (c.firstBad.Nstar + 1)
    (u : EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) u.property

/-- Exact order-six Riesz representation on the retained regular first-bad
trial. -/
theorem RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    canonicalSourceChannelEnergy
        c.firstBad.L (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) =
      canonicalRieszSourceChannelEnergy
        c.firstBad.L 6 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) := by
  exact canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
    c.firstBad.L_pos (c.firstBad.Nstar + 1)
    (cubicZeroShiftTrialVector
      c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
      EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))
    c.trial_boundaryFlat

/-- The complete retained order-six Riesz source channel is strictly negative. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 6 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 := by
  rw [← c.channelEnergy_eq_rieszSix]
  exact c.channelEnergyNeg

/-- If the retained first-bad parity is even, its trial coordinates lie in the
even coefficient sector. -/
theorem RegularCellMinimalNegativeEnergyCertificate.trial_evenCoefficient
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ((EuclideanSpace.equiv
      (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
      (cubicZeroShiftTrialVector
        c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
        EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) ∈
      evenCoefficientSubspace (c.firstBad.Nstar + 1) := by
  let u := cubicZeroShiftTrialVector
    c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀
  have hu :
      (u : EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) ∈
        euclideanParityBoundaryFlatSubspace c.firstBad.p
          (c.firstBad.Nstar + 1) := u.property
  rw [hp] at hu
  exact evenCoefficientSubspace_of_mem_euclideanEvenBoundaryFlatSubspace
    (c.firstBad.Nstar + 1)
    (u : EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) hu

/-- Even retained first-bad states admit the stronger order-eight exact Riesz
representation. -/
theorem RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalSourceChannelEnergy
        c.firstBad.L (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) =
      canonicalRieszSourceChannelEnergy
        c.firstBad.L 8 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) := by
  exact canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
    c.firstBad.L_pos (c.firstBad.Nstar + 1)
    (cubicZeroShiftTrialVector
      c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
      EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))
    c.trial_boundaryFlat (c.trial_evenCoefficient hp)

/-- The complete retained order-eight Riesz source channel is strictly negative
whenever the first-bad parity is even. -/
theorem RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 8 (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 := by
  rw [← c.channelEnergy_eq_rieszEight_of_even hp]
  exact c.channelEnergyNeg

end Zeta23.CCM

#print axioms Zeta23.CCM.boundaryFlatCoefficients_of_mem_euclideanParityBoundaryFlatSubspace
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
