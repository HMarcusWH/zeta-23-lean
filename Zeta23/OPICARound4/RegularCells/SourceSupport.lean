import Zeta23.CCM.FrozenCanonicalSourceAnalytic
import Zeta23.CCM.CanonicalPoleNeutralGeometry

noncomputable section

namespace Zeta23.OPICARound4.RegularCells
open CCM Matrix

/-- G02 exact reuse consumer: the frozen arithmetic agrees with production
only on the stated physical prime cell. Outside it the family is auxiliary. -/
theorem frozen_source_cell_consumer {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hcell : L ∈ fixedCanonicalCutoffCell Q) (K : ℕ) :
    frozenCanonicalSourceMatrix Q L K = canonicalSourceMatrix L K :=
  frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell hQ hcell K

/-- Pole cancellation in the auxiliary source is valid at fixed Q,K on any
positive aperture, independently of equality to the growing-cutoff source. -/
theorem frozen_source_neutral_action {L : ℝ} (hL : 0 < L) (Q K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    frozenCanonicalSourceMatrix Q L K *ᵥ evenBoundaryFlatRawCoefficients K u.val =
      -(canonicalArchMatrix L K *ᵥ evenBoundaryFlatRawCoefficients K u.val) -
        frozenCanonicalPrimeMatrix Q L K *ᵥ evenBoundaryFlatRawCoefficients K u.val := by
  rw [frozenCanonicalSourceMatrix, sub_mulVec, sub_mulVec,
    canonicalPoleMatrix_mulVec_poleNeutralEven_eq_zero hL K u, zero_sub]

end Zeta23.OPICARound4.RegularCells
