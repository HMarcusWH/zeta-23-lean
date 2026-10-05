import Zeta23.CCM.ProductionNormalSourceAuthority
import Zeta23.CCM.ProductionWeightedGlobalTests

noncomputable section
namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

def productionContactRemainderPhysicalTest
    (L : ℝ) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  productionPhysicalClamp L (productionContactRemainderSource L K v w)

theorem productionContactRemainderPhysicalTest_eq_source_on_Icc
    {L : ℝ} (K : ℕ) (v w : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionContactRemainderPhysicalTest L K v w t =
      productionContactRemainderSource L K v w t := by
  simp [productionContactRemainderPhysicalTest, productionPhysicalClamp_eq ht]

theorem productionSecondDerivativePhysicalTest_eq_neg_indexEnergy
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionSecondDerivativePhysicalTest L K v t =
      -(2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 *
        productionContactIndexEnergy L K v t := by
  rw [productionSecondDerivativePhysicalTest, productionPhysicalClamp_eq ht]
  unfold productionSecondDerivativePhysicalRaw productionContactIndexEnergy
  rw [sourceAtomRealEnergySecondDerivative_eq_indexAction K
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L)
    (evenBoundaryFlat_coordinateSum_zero K v)]
  ring

theorem productionMixedDerivativePhysicalTest_eq_mixedSource
    {L : ℝ} (K : ℕ) (v w : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionMixedDerivativePhysicalTest L K v w t =
      t / L ^ 2 * productionContactMixedSourceDerivative L K v w t := by
  rw [productionMixedDerivativePhysicalTest, productionPhysicalClamp_eq ht]
  rfl

theorem productionContactRemainderPhysicalTest_decomposition
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderPhysicalTest L K v w =
      fun t =>
        (2 * Real.pi) ^ 2 / L ^ 2 *
            productionContactNormalPhysicalTest L K v t +
          productionSecondDerivativePhysicalTest L K v t +
          2 * productionMixedDerivativePhysicalTest L K v w t := by
  funext t
  by_cases ht : t ∈ Icc (0 : ℝ) L
  · rw [productionContactRemainderPhysicalTest_eq_source_on_Icc K v w ht,
      productionContactNormalPhysicalTest_eq_source_on_Icc K v ht,
      productionSecondDerivativePhysicalTest_eq_neg_indexEnergy hL K v ht,
      productionMixedDerivativePhysicalTest_eq_mixedSource K v w ht,
      productionContactRemainderSource_simplified hL.ne' K v w t]
    ring
  · simp [productionContactRemainderPhysicalTest,
      productionContactNormalPhysicalTest,
      productionSecondDerivativePhysicalTest,
      productionMixedDerivativePhysicalTest, productionPhysicalClamp, ht]

theorem productionContactRemainderPhysical_admissible
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedPhysicalAdmissible L
      (productionContactRemainderPhysicalTest L K v w) := by
  have hn := productionContactNormalPhysical_admissible hL K hK v
  have hd := production_derivative_tests_admissible hL K v w
  have hs :=
    (hn.smul (a := (2 * Real.pi) ^ 2 / L ^ 2)).add
      (hd.2.1.add (hd.2.2.smul (a := 2)))
  rw [productionContactRemainderPhysicalTest_decomposition hL K v w]
  exact hs

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactRemainderPhysical_admissible
