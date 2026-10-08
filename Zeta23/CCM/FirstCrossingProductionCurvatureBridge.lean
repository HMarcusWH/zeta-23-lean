import Zeta23.CCM.FirstCrossingProductionResponse
import Zeta23.CCM.FirstCrossingProductionSaturation
import Zeta23.CCM.FirstCrossingProductionRemainderValueAuthority
import Zeta23.CCM.StationarySchurContact

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

/-- Corrected pair second-order quantity built from the actual compressed
derivatives. -/
def canonicalContactSecondPairing
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  productionContactFixedSecondVariation .even L K z +
    2 * Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w))

/-- Actual optimized curvature: the second pairing evaluated at the unique
perpendicular response. -/
def canonicalOptimizedContactCurvature
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K)
    (hzne : z ≠ 0) (hznorm : ‖z‖ = 1)
    (hzero : evenCompressedCanonical L K z = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    (hstationary :
      productionContactFirstVariation .even L K z = 0) : ℝ :=
  canonicalContactSecondPairing L K z
    (canonicalStationaryEvenResponse
      hL K hK z hzne hznorm hzero hodd hstationary)

/-- Value-level decomposition of the concrete remainder into admitted normal,
second-derivative, and mixed channels.  This does not identify the weighted
evaluations with the compressed aperture derivatives; that is F04's open gate. -/
theorem productionContactRemainderValue_physical_decomposition
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderValue L K z w =
      (2 * Real.pi) ^ 2 / L ^ 2 *
        productionArithmeticRealValue L
          (productionContactNormalPhysicalTest L K z) +
      productionArithmeticRealValue L
        (productionSecondDerivativePhysicalTest L K z) +
      2 * productionArithmeticRealValue L
        (productionMixedDerivativePhysicalTest L K z w) := by
  have hn := productionContactNormalPhysical_admissible
    hL K (by omega : 1 ≤ K) z
  have hd := production_derivative_tests_admissible hL K z w
  have hc := hn.smul (a := (2 * Real.pi) ^ 2 / L ^ 2)
  have hm := hd.2.2.smul (a := 2)
  rw [productionContactRemainderValue_eq_physicalTest hL K z w,
    productionContactRemainderPhysicalTest_decomposition hL K z w]
  rw [productionArithmeticRealValue_add_of_admissible (hc.add hd.2.1) hm]
  rw [productionArithmeticRealValue_add_of_admissible hc hd.2.1]
  rw [productionArithmeticRealValue_smul_of_admissible hn]
  rw [productionArithmeticRealValue_smul_of_admissible hd.2.2]

/-- This is the strongest unconditional value calculation available from the
admitted physical-test decomposition.  No differentiation under the varying
aperture or through the prime staircase is asserted. -/
theorem productionContactSaturationGap_eq_physical_second_mixed
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K z w =
      productionArithmeticRealValue L
        (productionSecondDerivativePhysicalTest L K z) +
      2 * productionArithmeticRealValue L
        (productionMixedDerivativePhysicalTest L K z w) := by
  unfold productionContactSaturationGap
  rw [productionContactRemainderValue_physical_decomposition hL K hK z w]
  rw [productionContactNormalPhysicalValue_eq_sourceValue
    hL K (by omega : 1 ≤ K) z]
  ring

/-- F04 arithmetic derivative transport is a separate, presently OPEN
mathematical obligation.  Fixed-L weighted admissibility is not enough to
differentiate the L-dependent complete physical functional.  This proposition
is an explicit hypothesis, NOT an axiom and NOT an established theorem. -/
structure ProductionContactF04DerivativeAuthority
    (L : ℝ) (K : ℕ) : Prop where
  first : ∀ z : euclideanEvenBoundaryFlatSubspace K,
    productionContactFirstVariation .even L K z =
      productionArithmeticRealValue L
        (productionFirstDerivativePhysicalTest L K z)
  fixedSecondEuler : ∀ z : euclideanEvenBoundaryFlatSubspace K,
    productionContactFixedSecondVariation .even L K z +
      2 * productionContactFirstVariation .even L K z / L =
        productionArithmeticRealValue L
          (productionSecondDerivativePhysicalTest L K z)
  mixed : ∀ z w : euclideanEvenBoundaryFlatSubspace K,
    Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w)) =
      productionArithmeticRealValue L
        (productionMixedDerivativePhysicalTest L K z w)

/-- The Euler-corrected balance is a genuine implication of F04 derivative
transport plus the unconditional value decomposition, not a premise-free
arithmetic identity. -/
theorem canonicalSecondPairing_euler_eq_productionSaturationGap
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K)
    (hF04 : ProductionContactF04DerivativeAuthority L K) :
    productionContactSaturationGap L K z w =
      canonicalContactSecondPairing L K z w +
        2 * productionContactFirstVariation .even L K z / L := by
  rw [productionContactSaturationGap_eq_physical_second_mixed hL K hK z w,
    ← hF04.fixedSecondEuler z, ← hF04.mixed z w]
  unfold canonicalContactSecondPairing
  ring

/-! ## F04 explicit physical derivative identities -/

/-- The real part of the mixed source derivative on the diagonal is the genuine
real source-energy derivative. -/
theorem sourceAtomPairingDerivative_self_re_eq_realEnergyDerivative
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    Complex.re (sourceAtomPairingDerivative K x x ω) =
      sourceAtomRealEnergyDerivative K x ω := by
  have hpair :
      HasDerivAt
        (fun s : ℝ => Complex.re (sourceAtomPairing K x x s))
        (Complex.re (sourceAtomPairingDerivative K x x ω)) ω := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt ω
      (hasDerivAt_sourceAtomPairing K x x ω)
  have henergy :=
    hasDerivAt_sourceAtomRealEnergy_transport K x ω
  have hfun :
      (fun s : ℝ => Complex.re (sourceAtomPairing K x x s)) =
        sourceAtomRealEnergy K x := by
    funext s
    unfold sourceAtomPairing sourceAtomRealEnergy matrixRealEnergy quadraticForm
    simp_rw [sourceMatrix_apply, sourceEntry_eq_ofReal]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.real_smul]
    ring
  rw [hfun] at hpair
  exact hpair.unique henergy

/-- The mixed physical test specializes to the first-variation physical test
when the response slot equals the state slot. -/
theorem productionMixedDerivativePhysicalTest_self_eq_firstDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionMixedDerivativePhysicalTest L K z z =
      productionFirstDerivativePhysicalTest L K z := by
  funext t
  unfold productionMixedDerivativePhysicalTest
    productionFirstDerivativePhysicalTest productionPhysicalClamp
  by_cases ht : t ∈ Set.Icc (0 : ℝ) L
  · simp only [ht, if_pos]
    unfold productionMixedDerivativePhysicalRaw
      productionFirstDerivativePhysicalRaw
    rw [sourceAtomPairingDerivative_self_re_eq_realEnergyDerivative]
  · simp [ht]

/-- With zero response, the concrete saturation gap is exactly the admitted
Euler-weighted second physical test.  The normal source cancels against the
same theorem-authoritative Q term. -/
theorem productionContactSaturationGap_zeroResponse_eq_secondPhysical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K z 0 =
      productionArithmeticRealValue L
        (productionSecondDerivativePhysicalTest L K z) := by
  have hn :=
    productionContactNormalPhysical_admissible hL K (by omega : 1 ≤ K) z
  have hd := production_derivative_tests_admissible
    hL K z (0 : euclideanEvenBoundaryFlatSubspace K)
  have hs := hd.2.1
  have hm0 :
      productionMixedDerivativePhysicalTest L K z
          (0 : euclideanEvenBoundaryFlatSubspace K) = 0 := by
    funext t
    simp [productionMixedDerivativePhysicalTest,
      productionMixedDerivativePhysicalRaw, productionPhysicalClamp,
      sourceAtomPairingDerivative]
  unfold productionContactSaturationGap
  rw [productionContactRemainderValue_eq_physicalTest hL K z 0]
  rw [productionContactRemainderPhysicalTest_decomposition hL K z 0]
  rw [hm0]
  simp only [Pi.zero_apply, mul_zero, add_zero]
  rw [productionArithmeticRealValue_add_of_admissible
    (hn.smul (a := (2 * Real.pi) ^ 2 / L ^ 2)) hs]
  rw [productionArithmeticRealValue_smul_of_admissible hn]
  rw [productionContactNormalPhysicalValue_eq_sourceValue
    hL K (by omega : 1 ≤ K) z]
  ring

/-- Changing only the response slot changes the concrete remainder by exactly
twice the admitted mixed physical test. -/
theorem productionContactRemainderValue_eq_zeroResponse_add_two_mixedPhysical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderValue L K z w =
      productionContactRemainderValue L K z 0 +
        2 * productionArithmeticRealValue L
          (productionMixedDerivativePhysicalTest L K z w) := by
  have hR0 :=
    productionContactRemainderPhysical_admissible
      hL K (by omega : 1 ≤ K) z
        (0 : euclideanEvenBoundaryFlatSubspace K)
  have hd := production_derivative_tests_admissible hL K z w
  have hm := hd.2.2
  have hm0 :
      productionMixedDerivativePhysicalTest L K z
          (0 : euclideanEvenBoundaryFlatSubspace K) = 0 := by
    funext t
    simp [productionMixedDerivativePhysicalTest,
      productionMixedDerivativePhysicalRaw, productionPhysicalClamp,
      sourceAtomPairingDerivative]
  have hfun :
      productionContactRemainderPhysicalTest L K z w =
        fun t =>
          productionContactRemainderPhysicalTest L K z 0 t +
            2 * productionMixedDerivativePhysicalTest L K z w t := by
    rw [productionContactRemainderPhysicalTest_decomposition hL K z w,
      productionContactRemainderPhysicalTest_decomposition hL K z 0,
      hm0]
    funext t
    simp
  rw [productionContactRemainderValue_eq_physicalTest hL K z w,
      productionContactRemainderValue_eq_physicalTest hL K z 0,
      hfun]
  rw [productionArithmeticRealValue_add_of_admissible
    hR0 (hm.smul (a := 2))]
  rw [productionArithmeticRealValue_smul_of_admissible hm]

/-- Response variation of the saturation gap is exactly the mixed physical
authority. -/
theorem productionContactSaturationGap_eq_zeroResponse_add_two_mixedPhysical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K z w =
      productionContactSaturationGap L K z 0 +
        2 * productionArithmeticRealValue L
          (productionMixedDerivativePhysicalTest L K z w) := by
  unfold productionContactSaturationGap
  rw [productionContactRemainderValue_eq_zeroResponse_add_two_mixedPhysical
    hL K hK z w]
  ring

/-- Explicit F04 mixed identity:
Re <z,E1 w> is the admitted complete physical evaluation of kM. -/
theorem canonicalMixedFirstVariation_eq_physical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K)
    (hF04 : ProductionContactF04DerivativeAuthority L K) :
    Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w)) =
      productionArithmeticRealValue L
        (productionMixedDerivativePhysicalTest L K z w) := by
  exact hF04.mixed z w

/-- Explicit F04 first identity:
J1 is the admitted complete physical evaluation of k1. -/
theorem canonicalFirstVariation_eq_physical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K)
    (hF04 : ProductionContactF04DerivativeAuthority L K) :
    productionContactFirstVariation .even L K z =
      productionArithmeticRealValue L
        (productionFirstDerivativePhysicalTest L K z) := by
  exact hF04.first z

/-- Explicit F04 Euler-corrected fixed-second identity:
J2_fixed + 2 J1/L is the admitted complete physical evaluation of k2. -/
theorem canonicalFixedSecondEuler_eq_physical
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K)
    (hF04 : ProductionContactF04DerivativeAuthority L K) :
    productionContactFixedSecondVariation .even L K z +
        2 * productionContactFirstVariation .even L K z / L =
      productionArithmeticRealValue L
        (productionSecondDerivativePhysicalTest L K z) := by
  exact hF04.fixedSecondEuler z

/-- Stationary specialization: Euler correction disappears. -/
theorem canonicalStationaryCurvature_eq_productionSaturationGap
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K)
    (hzne : z ≠ 0) (hznorm : ‖z‖ = 1)
    (hzero : evenCompressedCanonical L K z = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    (hstationary :
      productionContactFirstVariation .even L K z = 0)
    (hF04 : ProductionContactF04DerivativeAuthority L K) :
    canonicalOptimizedContactCurvature
        hL K hK z hzne hznorm hzero hodd hstationary =
      productionContactSaturationGap L K z
        (canonicalStationaryEvenResponse
          hL K hK z hzne hznorm hzero hodd hstationary) := by
  have h :=
    canonicalSecondPairing_euler_eq_productionSaturationGap
      hL K hK z
        (canonicalStationaryEvenResponse
          hL K hK z hzne hznorm hzero hodd hstationary) hF04
  simpa [canonicalOptimizedContactCurvature, hstationary] using h.symm

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalFirstVariation_eq_physical
#print axioms Zeta23.CCM.canonicalFixedSecondEuler_eq_physical
#print axioms Zeta23.CCM.canonicalMixedFirstVariation_eq_physical
#print axioms Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap
#print axioms Zeta23.CCM.canonicalStationaryCurvature_eq_productionSaturationGap
#print axioms Zeta23.CCM.productionContactOptimizedCurvature_eq_fixedSecond_sub_response
#print axioms Zeta23.CCM.productionContactResponseCost_nonnegative
#print axioms Zeta23.CCM.productionOptimizedCurvatureBridge_of_concreteIdentity
#print axioms Zeta23.CCM.productionContactOptimizedCurvature_zero_iff
