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


/-! ## F03 production authority and phase invariance -/

/-- The fourth centered moment is complex-linear in the legal vector. -/
theorem productionContactMomentFour_smul
    (K : ℕ) (u : ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionContactMomentFour K (u • v) =
      u * productionContactMomentFour K v := by
  unfold productionContactMomentFour evenBoundaryFlatRawCoefficients centeredMoment
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The quadratic-normal source atom is linear in the carrier. -/
theorem quadraticNormalSourceAtom_smul_right
    (K : ℕ) (u : ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) (ω : ℝ) :
    quadraticNormalSourceAtom K (u • v) ω =
      u * quadraticNormalSourceAtom K v ω := by
  rw [quadraticNormalSourceAtom_eq_sourceAtomPairing_div,
      quadraticNormalSourceAtom_eq_sourceAtomPairing_div]
  unfold sourceAtomPairing
  simp only [Submodule.coe_smul, LinearMapClass.map_smul,
    inner_smul_right]
  ring

/-- Source energy is invariant under a unit complex phase. -/
theorem sourceAtomRealEnergy_unitPhase
    (K : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomRealEnergy K (u • x) ω =
      sourceAtomRealEnergy K x ω := by
  unfold sourceAtomRealEnergy matrixRealEnergy
  rw [quadraticForm_smul]
  have hunit : star u * u = 1 := by
    rw [← Complex.normSq_eq_abs, Complex.normSq_eq_conj_mul_self]
    simp [hu]
  rw [hunit, one_mul]

/-- The centered-index action commutes with complex phase. -/
theorem sourceIndexAction_smul
    (K : ℕ) (u : ℂ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceIndexAction K (u • x) = u • sourceIndexAction K x := by
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  simp [sourceIndexAction_coordinates, Matrix.mulVec, Finset.mul_sum,
    mul_assoc]

/-- The mixed source derivative is invariant when both state and response are
rotated by the same unit phase. -/
theorem sourceAtomPairingDerivative_unitPhase
    (K : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (v w : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomPairingDerivative K (u • v) (u • w) ω =
      sourceAtomPairingDerivative K v w ω := by
  unfold sourceAtomPairingDerivative
  have hunit : star u * u = 1 := by
    rw [← Complex.normSq_eq_abs, Complex.normSq_eq_conj_mul_self]
    simp [hu]
  simp only [Pi.smul_apply, map_mul, starRingEnd_apply]
  rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hunit]
  ring

/-- Every scalar channel entering the concrete remainder is phase invariant. -/
theorem productionContactRemainderSource_unitPhase
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (u : ℂ) (hu : ‖u‖ = 1)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderSource L K (u • v) (u • w) =
      productionContactRemainderSource L K v w := by
  funext t
  rw [productionContactRemainderSource_simplified hL,
      productionContactRemainderSource_simplified hL]
  have hnormal :
      productionContactNormalSourceChannel L K (u • v) t =
        productionContactNormalSourceChannel L K v t := by
    unfold productionContactNormalSourceChannel
    rw [productionContactMomentFour_smul,
      quadraticNormalSourceAtom_smul_right]
    have hunit : star u * u = 1 := by
      rw [← Complex.normSq_eq_abs, Complex.normSq_eq_conj_mul_self]
      simp [hu]
    simp [map_mul, hunit]
    ring
  have hindex :
      productionContactIndexEnergy L K (u • v) t =
        productionContactIndexEnergy L K v t := by
    unfold productionContactIndexEnergy
    rw [sourceIndexAction_smul]
    exact sourceAtomRealEnergy_unitPhase K u hu _ _
  have hmixed :
      productionContactMixedSourceDerivative L K (u • v) (u • w) t =
        productionContactMixedSourceDerivative L K v w t := by
    unfold productionContactMixedSourceDerivative
    simp only [Submodule.coe_smul]
    rw [sourceAtomPairingDerivative_unitPhase K u hu]
  rw [hnormal, hindex, hmixed]

/-- The complete physical value of the concrete remainder is phase invariant. -/
theorem productionContactRemainderValue_unitPhase
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (u : ℂ) (hu : ‖u‖ = 1)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderValue L K (u • v) (u • w) =
      productionContactRemainderValue L K v w := by
  unfold productionContactRemainderValue
  rw [productionContactRemainderSource_unitPhase hL K u hu v w]

/-- The theorem-authoritative production source scalar is phase invariant. -/
theorem productionStrictEvenSourceValue_unitPhase
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (u : ℂ) (hu : ‖u‖ = 1)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionStrictEvenSourceValue L K (u • v) =
      productionStrictEvenSourceValue L K v := by
  rw [productionStrictEvenSourceValue_eq_pairing hL K hK,
      productionStrictEvenSourceValue_eq_pairing hL K hK]
  unfold strictEvenSourceMomentPairing
  have hsource :
      explicitCanonicalSourceMoment L K (u • v) =
        u * explicitCanonicalSourceMoment L K v := by
    rw [explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum,
        explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum]
    simp only [Submodule.coe_smul, LinearMapClass.map_smul,
      quadraticNormalSourceAtom_smul_right,
      productionContactMomentFour_smul]
    ring
  have hm4 :
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K (u • v)) =
        u * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
    simpa [productionContactMomentFour] using
      productionContactMomentFour_smul K u v
  rw [hsource, hm4]
  have hunit : star u * u = 1 := by
    rw [← Complex.normSq_eq_abs, Complex.normSq_eq_conj_mul_self]
    simp [hu]
  simp [map_mul, hunit]
  ring

/-- Consequently the saturation gap is phase invariant. -/
theorem productionContactSaturationGap_unitPhase
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (u : ℂ) (hu : ‖u‖ = 1)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K (u • v) (u • w) =
      productionContactSaturationGap L K v w := by
  unfold productionContactSaturationGap
  rw [productionContactRemainderValue_unitPhase hL.ne' K u hu,
      productionStrictEvenSourceValue_unitPhase hL K hK u hu]

/-- The normal source channel is exactly the existing source scalar after
production evaluation.  This is the F03 normalization bridge; it introduces no
new source quantity. -/
theorem productionContactNormalSourceValue_eq_sourceValue
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L
        (productionContactNormalSourceChannel L K v) =
      productionStrictEvenSourceValue L K v := by
  unfold productionContactNormalSourceChannel productionStrictEvenSourceValue
    productionArithmeticRealValue
  rw [← explicitCanonicalSourceMoment_eq_productionArithmeticComplexValue
    hL K hK v]
  -- The complete physical RHS has real scalar weights, so taking Re after
  -- multiplying the source test by conj(M4) commutes with evaluation.
  unfold productionArithmeticComplexValue dictionaryCompletePhysicalRHS
  simp_rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [map_sum]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactRemainderSource_simplified
#print axioms Zeta23.CCM.productionContactIndexEnergy_eq_tangential_add_normal
#print axioms Zeta23.CCM.productionContactRemainderSource_apply
#print axioms Zeta23.CCM.productionContactRemainderSource_unitPhase
#print axioms Zeta23.CCM.productionStrictEvenSourceValue_unitPhase
#print axioms Zeta23.CCM.productionContactSaturationGap_unitPhase
#print axioms Zeta23.CCM.productionContactNormalSourceValue_eq_sourceValue
