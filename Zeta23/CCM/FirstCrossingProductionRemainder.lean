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
  simp only [Submodule.coe_smul, LinearMapClass.map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The generic normalized quadratic-normal matrix moment is linear in
the legal carrier. -/
theorem quadraticNormalMatrixMoment_smul_right
    (K : ℕ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (u : ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K M (u • v) =
      u * quadraticNormalMatrixMoment K M v := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_eq_inner,
      quadraticNormalMatrixNumerator_eq_inner]
  simp only [Submodule.coe_smul, LinearMapClass.map_smul, inner_smul_right]
  ring

/-- Unit complex phase as the exact algebraic identity used by all phase
invariance proofs below. -/
private theorem star_mul_self_eq_one_of_norm_eq_one
    (u : ℂ) (hu : ‖u‖ = 1) :
    star u * u = 1 := by
  change Complex.conj u * u = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hu]
  norm_num

/-- The complete canonical source moment is linear in the legal carrier. -/
private theorem explicitCanonicalSourceMoment_smul_right
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : ℂ) (v : euclideanEvenBoundaryFlatSubspace K) :
    explicitCanonicalSourceMoment L K (u • v) =
      u * explicitCanonicalSourceMoment L K v := by
  calc
    explicitCanonicalSourceMoment L K (u • v) =
        evenQuadraticSourceMoment L K (u • v) :=
      (evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
        hL K (u • v)).symm
    _ = quadraticNormalMatrixMoment K (canonicalSourceMatrix L K) (u • v) :=
      evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment L K (u • v)
    _ = u * quadraticNormalMatrixMoment K (canonicalSourceMatrix L K) v :=
      quadraticNormalMatrixMoment_smul_right K (canonicalSourceMatrix L K) u v
    _ = u * evenQuadraticSourceMoment L K v := by
      rw [evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment]
    _ = u * explicitCanonicalSourceMoment L K v := by
      rw [evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment hL K v]

/-- The quadratic-normal source atom is linear in the carrier. -/
theorem quadraticNormalSourceAtom_smul_right
    (K : ℕ) (u : ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) (ω : ℝ) :
    quadraticNormalSourceAtom K (u • v) ω =
      u * quadraticNormalSourceAtom K v ω := by
  unfold quadraticNormalSourceAtom
  exact quadraticNormalMatrixMoment_smul_right K (sourceMatrix ω K) u v

/-- Source energy is invariant under a unit complex phase. -/
theorem sourceAtomRealEnergy_unitPhase
    (K : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomRealEnergy K (u • x) ω =
      sourceAtomRealEnergy K x ω := by
  unfold sourceAtomRealEnergy matrixRealEnergy
  have hcoord :
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (u • x) =
        u • (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x := by
    exact LinearMapClass.map_smul
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u x
  rw [hcoord, quadraticForm_smul,
    star_mul_self_eq_one_of_norm_eq_one u hu, one_mul]

/-- The centered-index action commutes with complex phase. -/
theorem sourceIndexAction_smul
    (K : ℕ) (u : ℂ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceIndexAction K (u • x) = u • sourceIndexAction K x := by
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  simpa only [sourceIndexAction_coordinates, LinearMapClass.map_smul] using
    (Matrix.mulVec_smul (indexMatrix K) u
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))

/-- The mixed source derivative is invariant when both state and response are
rotated by the same unit phase. -/
theorem sourceAtomPairingDerivative_unitPhase
    (K : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (v w : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomPairingDerivative K (u • v) (u • w) ω =
      sourceAtomPairingDerivative K v w ω := by
  unfold sourceAtomPairingDerivative
  have hunit := star_mul_self_eq_one_of_norm_eq_one u hu
  simp only [LinearMapClass.map_smul, Pi.smul_apply, map_mul,
    starRingEnd_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hunit]
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
    have hunit := star_mul_self_eq_one_of_norm_eq_one u hu
    apply congrArg Complex.re
    rw [map_mul]
    calc
      star u * star (productionContactMomentFour K v) *
          (u * quadraticNormalSourceAtom K v (1 - t / L)) =
          (star u * u) *
            (star (productionContactMomentFour K v) *
              quadraticNormalSourceAtom K v (1 - t / L)) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hindex :
      productionContactIndexEnergy L K (u • v) t =
        productionContactIndexEnergy L K v t := by
    unfold productionContactIndexEnergy
    change
      sourceAtomRealEnergy K
          (sourceIndexAction K
            (u • (v : EuclideanSpace ℂ (Fin (2 * K + 1)))))
          (1 - t / L) =
        sourceAtomRealEnergy K
          (sourceIndexAction K
            (v : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (1 - t / L)
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
        u * explicitCanonicalSourceMoment L K v :=
    explicitCanonicalSourceMoment_smul_right hL K u v
  have hm4 :
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K (u • v)) =
        u * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
    simpa [productionContactMomentFour] using
      productionContactMomentFour_smul K u v
  rw [hsource, hm4]
  have hunit := star_mul_self_eq_one_of_norm_eq_one u hu
  apply congrArg Complex.re
  rw [map_mul]
  calc
    star u * star (explicitCanonicalSourceMoment L K v) *
        (u * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) =
        (star u * u) *
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by ring
    _ = _ := by rw [hunit, one_mul]

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
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
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
