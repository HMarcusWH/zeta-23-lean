import Zeta23.CCM.CanonicalSourceMomentAtoms
import Zeta23.CCM.SourceExplicitCubicDefect

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ArithmeticFunction ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4a: exact canonical source-moment decomposition

This module assembles the source-channel identities into the scalar observable
exposed by PR #129.  At positive aperture the active quadratic-normal source
moment is exactly:

* one surviving rational pole profile channel;
* minus the reduced archimedean diagonal moment;
* minus the reduced archimedean off-diagonal moment;
* minus a finite von-Mangoldt weighted sum of elementary source-matrix moments.

Index-independent canonical archimedean scalars have disappeared because the
quadratic normal is orthogonal to the even boundary-flat sector.  No sign,
nonzeroness, branch exclusion, or RH conclusion is asserted.
-/

/-- Explicit finite canonical-source formula for the quadratic-normal moment.
The pole contribution is already reduced to its single even profile and the
prime contribution is already expanded into elementary source matrices. -/
def explicitCanonicalSourceMoment
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  (poleProfileScale L *
      (poleEvenProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K v) *
      (poleEvenProfile L K ⬝ᵥ
        fun i => star (centeredQuadraticNormal K i))) /
      inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)
    - quadraticNormalMatrixMoment K
        (reducedCanonicalArchDiagonalMatrix L K) v
    - quadraticNormalMatrixMoment K
        (reducedCanonicalArchOffDiagonalMatrix L K) v
    - ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          quadraticNormalMatrixMoment K
            (sourceMatrix (primeSourceCoordinate q L) K) v

/-- Coarse exact channel decomposition before the pole and prime channels are
expanded into their atomized forms. -/
theorem evenQuadraticSourceMoment_eq_channel_moments
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    evenQuadraticSourceMoment L K v =
      quadraticNormalMatrixMoment K (canonicalPoleMatrix L K) v -
        quadraticNormalMatrixMoment K
          (reducedCanonicalArchDiagonalMatrix L K) v -
        quadraticNormalMatrixMoment K
          (reducedCanonicalArchOffDiagonalMatrix L K) v -
        quadraticNormalMatrixMoment K (canonicalPrimeMatrix L K) v := by
  rw [evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment]
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime]
  rw [quadraticNormalMatrixMoment_sub,
    quadraticNormalMatrixMoment_sub]
  rw [quadraticNormalMatrixMoment_canonicalArch_eq_reduced hL]
  rw [reducedCanonicalArchMatrix_eq_diagonal_add_offDiagonal]
  rw [quadraticNormalMatrixMoment_add]
  ring

/-- Main A4a endpoint: exact production source-moment decomposition. -/
theorem evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    evenQuadraticSourceMoment L K v =
      explicitCanonicalSourceMoment L K v := by
  rw [evenQuadraticSourceMoment_eq_channel_moments hL K v]
  rw [quadraticNormalPoleMoment_eq_evenProfile hL K v]
  rw [quadraticNormalPrimeMoment_eq_sum_sourceMatrix]
  simp [explicitCanonicalSourceMoment]

/-- PR #129's cubic parity-defect coefficient inherits the exact A4a production
source decomposition. -/
theorem cubicDefectFunctional_eq_explicitCanonicalSourceMoment
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    cubicDefectFunctional L K v =
      explicitCanonicalSourceMoment L K v := by
  rw [cubicDefectFunctional_eq_evenQuadraticSourceMoment hL K hK v]
  exact evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment hL K v

end Zeta23.CCM

#print axioms Zeta23.CCM.evenQuadraticSourceMoment_eq_channel_moments
#print axioms Zeta23.CCM.evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
#print axioms Zeta23.CCM.cubicDefectFunctional_eq_explicitCanonicalSourceMoment
