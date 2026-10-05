import Zeta23.CCM.FirstCrossingProductionRemainder
import Zeta23.CCM.ProductionWeightedGlobalTests
import Zeta23.CCM.ProductionPhysicalFunctionalCongruence
import Zeta23.CCM.CanonicalQuadraticNormalSourceKernel

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# Post-#282 physical authority for the normal source channel

The normal channel in the concrete remainder is not a new source quantity.
After positive-half clamping it is the real part of the established
quadratic-normal mixed dictionary test, multiplied by the fixed fourth moment.
This file packages its physical integrability and exact production value.
-/

def productionContactNormalPhysicalTest
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  productionPhysicalClamp L (productionContactNormalSourceChannel L K v)

theorem productionContactNormalPhysicalTest_eq_source_on_Icc
    {L : ℝ} (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionContactNormalPhysicalTest L K v t =
      productionContactNormalSourceChannel L K v t := by
  simp [productionContactNormalPhysicalTest, productionPhysicalClamp_eq ht]

/-- The complex mixed dictionary representative of the normal channel. -/
def productionContactNormalDictionaryTest
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℂ :=
  dictionaryMixedTest K
    (fun i => centeredQuadraticNormal K i)
    (fun j =>
      (2 / inner ℂ (centeredQuadraticNormal K)
              (centeredQuadraticNormal K)) *
        evenBoundaryFlatRawCoefficients K v j)
    L

theorem productionContactNormalDictionaryTest_eq_sourceLift
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionContactNormalDictionaryTest L K v =
      canonicalSourcePhysicalLift L (quadraticNormalSourceAtom K v) := by
  exact
    (canonicalSourcePhysicalLift_quadraticNormalSourceAtom_eq_mixedTest
      hL K hK v).symm

@[simp] theorem productionContactNormalDictionaryTest_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionContactNormalDictionaryTest L K v 0 = 0 := by
  rw [productionContactNormalDictionaryTest_eq_sourceLift hL K hK v]
  exact canonicalSourcePhysicalLift_quadraticNormalSourceAtom_zero hL K v

/-- On the production interval, the clamped real normal test is the real part
of the fixed fourth-moment multiple of the mixed dictionary representative. -/
theorem productionContactNormalPhysicalTest_eq_dictionary_re
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionContactNormalPhysicalTest L K v t =
      Complex.re
        (star (productionContactMomentFour K v) *
          productionContactNormalDictionaryTest L K v t) := by
  rw [productionContactNormalPhysicalTest_eq_source_on_Icc K v ht]
  rw [productionContactNormalDictionaryTest_eq_sourceLift hL K hK v,
    canonicalSourcePhysicalLift_eq_one_sub_of_mem hL ht.1 ht.2]
  rfl

/-- Admissibility of the normal source channel.  The apparent archimedean
singularity at the physical origin is removable because the mixed dictionary
representative vanishes there. -/
theorem productionContactNormalPhysical_admissible
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedPhysicalAdmissible L
      (productionContactNormalPhysicalTest L K v) := by
  let g := productionContactNormalDictionaryTest L K v
  have hgcont : Continuous g := by
    simpa [g, productionContactNormalDictionaryTest] using
      continuous_dictionaryMixedTest K
        (fun i => centeredQuadraticNormal K i)
        (fun j =>
          (2 / inner ℂ (centeredQuadraticNormal K)
                  (centeredQuadraticNormal K)) *
            evenBoundaryFlatRawCoefficients K v j) hL
  have hg0 : g 0 = 0 := by
    simpa [g] using productionContactNormalDictionaryTest_zero hL K hK v
  have harch :
      IntervalIntegrable
        (fun t : ℝ => g t * (archDensity t : ℂ)) volume 0 L := by
    simpa [g, productionContactNormalDictionaryTest] using
      intervalIntegrable_dictionaryMixedTest_mul_archDensity_of_zero K
        (fun i => centeredQuadraticNormal K i)
        (fun j =>
          (2 / inner ℂ (centeredQuadraticNormal K)
                  (centeredQuadraticNormal K)) *
            evenBoundaryFlatRawCoefficients K v j)
        hL hg0
  have hpole :
      IntervalIntegrable
        (fun t : ℝ => g t * (completeSourcePoleWeight t : ℂ))
        volume 0 L := by
    simpa [g, productionContactNormalDictionaryTest] using
      intervalIntegrable_dictionaryMixedTest_mul_pole K
        (fun i => centeredQuadraticNormal K i)
        (fun j =>
          (2 / inner ℂ (centeredQuadraticNormal K)
                  (centeredQuadraticNormal K)) *
            evenBoundaryFlatRawCoefficients K v j)
        hL
  refine ⟨?_, ?_, ?_, productionPhysicalClamp_support_subset L _⟩
  · unfold productionContactNormalPhysicalTest productionPhysicalClamp
    exact
      (Measurable.ite measurableSet_Icc
        ((Complex.continuous_re.comp
          (continuous_const.mul hgcont)).measurable)
        measurable_const).aestronglyMeasurable
  · have h :=
      ((hpole.const_mul (star (productionContactMomentFour K v))).re)
    refine h.congr ?_
    filter_upwards with t
    by_cases ht : t ∈ Icc (0 : ℝ) L
    · rw [productionContactNormalPhysicalTest_eq_dictionary_re
        hL K hK v ht]
      ring
    · simp [productionContactNormalPhysicalTest, productionPhysicalClamp, ht]
  · have h :=
      ((harch.const_mul (star (productionContactMomentFour K v))).re)
    refine h.congr ?_
    filter_upwards with t
    by_cases ht : t ∈ Icc (0 : ℝ) L
    · rw [productionContactNormalPhysicalTest_eq_dictionary_re
        hL K hK v ht]
      ring
    · simp [productionContactNormalPhysicalTest, productionPhysicalClamp, ht]
/-- Clamping does not change the canonical normal-channel production value. -/
theorem productionContactNormalPhysicalValue_eq_sourceValue
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L
        (productionContactNormalPhysicalTest L K v) =
      productionStrictEvenSourceValue L K v := by
  rw [← productionContactNormalSourceValue_eq_sourceValue hL K hK v]
  apply productionArithmeticRealValue_congr_on_Icc hL
  intro t ht
  exact productionContactNormalPhysicalTest_eq_source_on_Icc K v ht

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactNormalPhysical_admissible
#print axioms Zeta23.CCM.productionContactNormalPhysicalValue_eq_sourceValue
