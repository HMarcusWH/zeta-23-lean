import Zeta23.CCM.FirstCrossingProductionTests
import Zeta23.CCM.ProductionWeightedTestCalculus
import Zeta23.CCM.FirstCrossingOptimizedCurvatureAlgebra
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#281 concrete production contact remainder

The handoff remainder is now constructed from one actual even legal state and
one actual even legal response.  No caller supplies an arbitrary
`remainderSource`.

The tangential channel is first defined by the exact source-energy difference
`e_Dz - Re(conj(M4) H_z)`.  A later legality theorem may identify that
difference with the intrinsic projected `D*D z` energy; the arithmetic bridge
does not need to assume a free tangential function.
-/

/-- Fourth centered moment of one even legal state. -/
def productionContactMomentFour
    (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)

/-- Normal quadratic-source channel Re(conj(M4) H_z). -/
def productionContactNormalSourceChannel
    (L : ℝ) (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) : ℝ :=
  Complex.re
    (star (productionContactMomentFour K v) *
      quadraticNormalSourceAtom K v (1 - t / L))

/-- Source energy of the centered-index image D z. -/
def productionContactIndexEnergy
    (L : ℝ) (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) : ℝ :=
  sourceAtomRealEnergy K
    (sourceIndexAction K
      (v : EuclideanSpace ℂ (Fin (2 * K + 1))))
    (1 - t / L)

/-- The exact complementary/tangential source energy used in the remainder,
defined by the source decomposition itself. -/
def productionContactTangentialEnergy
    (L : ℝ) (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) : ℝ :=
  productionContactIndexEnergy L K v t -
    productionContactNormalSourceChannel L K v t

/-- Mixed source-coordinate derivative Re <z, A'(omega) w>. -/
def productionContactMixedSourceDerivative
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) : ℝ :=
  Complex.re
    (sourceAtomPairingDerivative K
      (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (1 - t / L))

/-- Concrete handoff remainder source R_{L,z,w}. -/
def productionContactRemainderSource
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    ℝ → ℝ :=
  fun t =>
    optimizedCurvatureSourceRemainderIntegrand
      L t
      (productionContactNormalSourceChannel L K v t)
      (productionContactTangentialEnergy L K v t)
      (productionContactMixedSourceDerivative L K v w t)

/-- The source decomposition e_Dz = e_tangent + Re(conj(M4) H_z) is exact by
construction; no independent arbitrary function is admitted. -/
theorem productionContactIndexEnergy_eq_tangential_add_normal
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) :
    productionContactIndexEnergy L K v t =
      productionContactTangentialEnergy L K v t +
        productionContactNormalSourceChannel L K v t := by
  unfold productionContactTangentialEnergy
  ring

/-- Pointwise concrete form of the remainder. -/
theorem productionContactRemainderSource_apply
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) :
    productionContactRemainderSource L K v w t =
      (2 * Real.pi) ^ 2 * (L ^ 2 - t ^ 2) / L ^ 4 *
          productionContactNormalSourceChannel L K v t -
        (2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 *
          productionContactTangentialEnergy L K v t +
        2 * t / L ^ 2 *
          productionContactMixedSourceDerivative L K v w t := by
  rfl

/-- Exact production evaluation of the constructed remainder. -/
def productionContactRemainderValue
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  productionArithmeticRealValue L
    (productionContactRemainderSource L K v w)

/-- Concrete saturation gap: no free remainder function occurs. -/
def productionContactSaturationGap
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  productionContactRemainderValue L K v w -
    (2 * Real.pi) ^ 2 / L ^ 2 *
      productionStrictEvenSourceValue L K v

/-- Simplified concrete remainder after substituting
tangential = indexEnergy - normal. -/
theorem productionContactRemainderSource_simplified
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) (t : ℝ) :
    productionContactRemainderSource L K v w t =
      (2 * Real.pi) ^ 2 / L ^ 2 *
          productionContactNormalSourceChannel L K v t -
        (2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 *
          productionContactIndexEnergy L K v t +
        2 * t / L ^ 2 *
          productionContactMixedSourceDerivative L K v w t := by
  rw [productionContactRemainderSource_apply]
  unfold productionContactTangentialEnergy
  field_simp [hL]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactRemainderSource_simplified
#print axioms Zeta23.CCM.productionContactIndexEnergy_eq_tangential_add_normal
#print axioms Zeta23.CCM.productionContactRemainderSource_apply
