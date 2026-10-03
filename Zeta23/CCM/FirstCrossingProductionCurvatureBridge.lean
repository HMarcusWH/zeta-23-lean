import Zeta23.CCM.FirstCrossingProductionResponse
import Zeta23.CCM.FirstCrossingProductionSaturation

noncomputable section

namespace Zeta23.CCM

open Complex
open scoped ComplexConjugate

/-!
# Post-#281 concrete optimized curvature

Curvature is defined from the actual production derivative operators and the
perpendicular stationary response.  It is not defined by the arithmetic gap.

The final equality with the constructed production remainder is isolated as the
concrete arithmetic-derivative identity still to be discharged by the weighted
explicit-formula differentiation layer.
-/

/-- Response energy in the contact operator. -/
def productionContactResponseCost
    (L : ℝ) (K : ℕ)
    (w : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  Complex.re (inner ℂ (evenCompressedCanonical L K w) w)

/-- Actual optimized second variation from E'', E' and the response. -/
def productionContactOptimizedCurvature
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  productionContactFixedSecondVariation .even L K z +
    2 * Complex.re
      (inner ℂ z (evenProductionApertureFirst L K w))

/-- The response equation turns the mixed term into the usual nonnegative
complement cost. -/
theorem productionContactOptimizedCurvature_eq_fixedSecond_sub_response
    {L : ℝ} (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K)
    (hresponse :
      evenCompressedCanonical L K w =
        -(evenProductionApertureFirst L K z)) :
    productionContactOptimizedCurvature L K z w =
      productionContactFixedSecondVariation .even L K z -
        2 * productionContactResponseCost L K w := by
  have hsym :=
    evenProductionApertureFirst_isSymmetric L K z w
  have hDz :
      evenProductionApertureFirst L K z =
        -(evenCompressedCanonical L K w) := by
    rw [hresponse]
    simp
  unfold productionContactOptimizedCurvature productionContactResponseCost
  have hmix :
      Complex.re
          (inner ℂ z (evenProductionApertureFirst L K w)) =
        - Complex.re
          (inner ℂ (evenCompressedCanonical L K w) w) := by
    rw [← hsym]
    rw [hDz]
    simp
  rw [hmix]
  ring

/-- At a zero even ground, the response cost is nonnegative.

The spectral-bottom theorem is stated on the generic parity carrier.  We move
its scalar quadratic value through the ambient canonical matrix before
returning to the native strict-even response operator, so no subtype
inner-product instance equality is required. -/
theorem productionContactResponseCost_nonnegative
    {L : ℝ} {K : ℕ}
    (hground : parityRayleighBottom .even L K = 0)
    (w : euclideanEvenBoundaryFlatSubspace K) :
    0 ≤ productionContactResponseCost L K w := by
  let wg : euclideanParityBoundaryFlatSubspace .even K :=
    ⟨(w : EuclideanSpace ℂ (Fin (2 * K + 1))),
      by
        simpa [euclideanParityBoundaryFlatSubspace] using w.property⟩
  have hgeneric0 :
      0 ≤ Complex.re
        (inner ℂ (parityCompressedCanonical .even L K wg) wg) := by
    have hbottom :=
      parityRayleighBottom_mul_norm_sq_le .even L K wg
    rw [hground, zero_mul] at hbottom
    simpa only [RCLike.re_to_complex] using hbottom
  have hambient :
      0 ≤ Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L K).toEuclideanLin
            (w : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
    rw [re_inner_parityCompressedCanonical_self .even L K wg] at hgeneric0
    simpa [wg] using hgeneric0
  have hcostNative :
      productionContactResponseCost L K w =
        Complex.re (inner ℂ (evenResponseContactOperator L K w) w) := by
    unfold productionContactResponseCost
    rw [evenResponseContactOperator_apply]
  have hnativeAmbient :
      Complex.re (inner ℂ (evenResponseContactOperator L K w) w) =
        Complex.re
          (inner ℂ
            ((canonicalSourceMatrix L K).toEuclideanLin
              (w : EuclideanSpace ℂ (Fin (2 * K + 1))))
            (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
    change
      Complex.re
        (inner ℂ
          ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
            ((canonicalSourceMatrix L K).toEuclideanLin
              (w : EuclideanSpace ℂ (Fin (2 * K + 1)))))
          w) = _
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [hcostNative, hnativeAmbient]
  exact hambient

/-- Consequently response optimization can only lower the fixed-vector second
variation. -/
theorem productionContactOptimizedCurvature_le_fixedSecond
    {L : ℝ} {K : ℕ}
    (z w : euclideanEvenBoundaryFlatSubspace K)
    (hground : parityRayleighBottom .even L K = 0)
    (hresponse :
      evenCompressedCanonical L K w =
        -(evenProductionApertureFirst L K z)) :
    productionContactOptimizedCurvature L K z w ≤
      productionContactFixedSecondVariation .even L K z := by
  rw [productionContactOptimizedCurvature_eq_fixedSecond_sub_response
    K z w hresponse]
  have hc := productionContactResponseCost_nonnegative hground w
  linarith

/-- Exact remaining production differentiation obligation for the *constructed*
objects.  This is not a free kappa/remainder interface: both sides are concrete
functions of L,K,z,w. -/
def ProductionContactCurvatureArithmeticIdentity
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : Prop :=
  productionContactOptimizedCurvature L K z w =
    productionContactSaturationGap L K z w

/-- Once the concrete derivative identity is discharged, it instantiates the
older #281 bridge with no caller-supplied curvature or remainder source. -/
theorem productionOptimizedCurvatureBridge_of_concreteIdentity
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 1 ≤ K)
    {z w : euclideanEvenBoundaryFlatSubspace K}
    (h :
      ProductionContactCurvatureArithmeticIdentity L K z w) :
    ProductionOptimizedCurvatureBridge
      L K z
      (productionContactOptimizedCurvature L K z w)
      (productionContactRemainderSource L K z w) := by
  unfold ProductionContactCurvatureArithmeticIdentity at h
  unfold productionContactSaturationGap productionContactRemainderValue at h
  rw [productionStrictEvenSourceValue_eq_pairing hL K hK z] at h
  unfold ProductionOptimizedCurvatureBridge
  unfold OptimizedCurvatureRemainderBalance
  exact h

/-- Concrete saturation equivalence after the actual bridge is proved. -/
theorem productionContactOptimizedCurvature_zero_iff
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 1 ≤ K)
    {z w : euclideanEvenBoundaryFlatSubspace K}
    (h :
      ProductionContactCurvatureArithmeticIdentity L K z w) :
    productionContactOptimizedCurvature L K z w = 0 ↔
      productionContactRemainderValue L K z w =
        (2 * Real.pi) ^ 2 / L ^ 2 *
          productionStrictEvenSourceValue L K z := by
  have hb :=
    productionOptimizedCurvatureBridge_of_concreteIdentity hL hK h
  have hz := productionOptimizedCurvatureBridge_zero_iff hb
  rw [← productionStrictEvenSourceValue_eq_pairing hL K hK z] at hz
  simpa [productionContactRemainderValue] using hz

/-- In the strict-even zero-ground branch, concrete saturation forces a
strictly positive production remainder. -/
theorem productionContactRemainderValue_pos_of_zeroCurvature_strictEven
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 2 ≤ K)
    {z w : euclideanEvenBoundaryFlatSubspace K}
    (hzne : z ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hzero : evenCompressedCanonical L K z = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    (hbridge :
      ProductionContactCurvatureArithmeticIdentity L K z w)
    (hkappa : productionContactOptimizedCurvature L K z w = 0) :
    0 < productionContactRemainderValue L K z w := by
  have hb :=
    productionOptimizedCurvatureBridge_of_concreteIdentity
      hL (by omega : 1 ≤ K) hbridge
  exact productionArithmeticRemainder_pos_of_saturation_strictEven
    (v := z) hL hK hzne hground hzero hodd hb hkappa

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactOptimizedCurvature_eq_fixedSecond_sub_response
#print axioms Zeta23.CCM.productionContactResponseCost_nonnegative
#print axioms Zeta23.CCM.productionOptimizedCurvatureBridge_of_concreteIdentity
#print axioms Zeta23.CCM.productionContactOptimizedCurvature_zero_iff
