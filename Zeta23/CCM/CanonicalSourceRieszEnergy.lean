import Zeta23.CCM.CanonicalSourceEnergyJets
import Zeta23.CCM.CanonicalPolePrimeRiesz

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03E: production Riesz source channel

The generic #155 Riesz engine is left untouched.  This module supplies its
production endpoint hypotheses from the exact boundary-flat source jets and
then restores the complete canonical channel, including both reduced
archimedean pieces and the scalar correction.

No sign of the Riesz integrand, discrepancy, or complete channel is asserted.
-/

/-- Complete canonical source-channel energy with the pole-prime discrepancy
represented at Riesz order `r`. -/
def canonicalRieszSourceChannelEnergy
    (L : ℝ) (r K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  canonicalPolePrimeRieszEnergy L r K x
    - matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x
    - matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x
    - canonicalArchScalarCorrection L * ‖x‖ ^ 2

/-- Every production boundary-flat carrier admits exact order-six Riesz
smoothing of the pole-prime discrepancy. -/
theorem canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    canonicalPolePrimeDiscrepancyEnergy L K x =
      canonicalPolePrimeRieszEnergy L 6 K x := by
  exact canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
    hL K x 6 (sourceAtomRealEnergy_boundaryFlat_jets_through_six K x hflat)

/-- Even production boundary-flat carriers admit exact order-eight Riesz
smoothing. -/
theorem canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    canonicalPolePrimeDiscrepancyEnergy L K x =
      canonicalPolePrimeRieszEnergy L 8 K x := by
  exact canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
    hL K x 8
      (sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
        K x hflat heven)

/-- Complete production channel equals its order-six Riesz representation on
every boundary-flat carrier. -/
theorem canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    canonicalSourceChannelEnergy L K x =
      canonicalRieszSourceChannelEnergy L 6 K x := by
  rw [canonicalSourceChannelEnergy_eq_discrepancy hL K x]
  rw [canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
    hL K x hflat]
  rfl

/-- Complete production channel equals its order-eight Riesz representation on
the even boundary-flat sector. -/
theorem canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    canonicalSourceChannelEnergy L K x =
      canonicalRieszSourceChannelEnergy L 8 K x := by
  rw [canonicalSourceChannelEnergy_eq_discrepancy hL K x]
  rw [canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
    hL K x hflat heven]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
