import Zeta23.CCM.FirstCrossingProductionArithmetic
import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# Post-#282 weighted production-test calculus

The production physical functional is used only on a proved admissible span.
This file does not manufacture an unrestricted linear functional through the
singular archimedean origin.
-/

/-- Minimal analytic contract for one real physical production test. -/
structure ProductionWeightedPhysicalAdmissible
    (L : ℝ) (f : ℝ → ℝ) : Prop where
  measurable : AEStronglyMeasurable f
  arch_integrable :
    IntegrableOn (fun t => |f t| * |archDensity t|) (Icc 0 L)
  support : Function.support f ⊆ Icc 0 L

/-- Admissibility is stable under addition. -/
theorem ProductionWeightedPhysicalAdmissible.add
    {L : ℝ} {f g : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f)
    (hg : ProductionWeightedPhysicalAdmissible L g) :
    ProductionWeightedPhysicalAdmissible L (fun t => f t + g t) := by
  refine ⟨hf.measurable.add hg.measurable, ?_, ?_⟩
  · apply IntegrableOn.mono'
      (hf.arch_integrable.add hg.arch_integrable)
      (measurableSet_Icc)
    filter_upwards with t
    simp only [norm_eq_abs]
    have h := abs_add (f t) (g t)
    nlinarith [abs_nonneg (archDensity t)]
  · intro t ht
    by_contra hmem
    apply ht
    simp only [Function.mem_support] at hmem ⊢
    by_cases hf0 : f t = 0
    · have hg0 : g t = 0 := by
        by_contra h
        exact hmem (by simp [hf0, h])
      simp [hf0, hg0]
    · exact hf.support hf0

/-- Admissibility is stable under real scaling. -/
theorem ProductionWeightedPhysicalAdmissible.smul
    {L a : ℝ} {f : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f) :
    ProductionWeightedPhysicalAdmissible L (fun t => a * f t) := by
  refine ⟨hf.measurable.const_mul a, ?_, ?_⟩
  · simpa [abs_mul, mul_assoc] using hf.arch_integrable.const_mul |a|
  · intro t ht
    apply hf.support
    intro hzero
    apply ht
    simp [hzero]

/-- Real production evaluation is additive on admitted tests. -/
theorem productionArithmeticRealValue_add_of_admissible
    {L : ℝ} {f g : ℝ → ℝ}
    (_hf : ProductionWeightedPhysicalAdmissible L f)
    (_hg : ProductionWeightedPhysicalAdmissible L g) :
    productionArithmeticRealValue L (fun t => f t + g t) =
      productionArithmeticRealValue L f +
        productionArithmeticRealValue L g := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
  simp [dictionaryCompletePhysicalRHS, map_add]

/-- Real production evaluation is homogeneous on admitted tests. -/
theorem productionArithmeticRealValue_smul_of_admissible
    {L a : ℝ} {f : ℝ → ℝ}
    (_hf : ProductionWeightedPhysicalAdmissible L f) :
    productionArithmeticRealValue L (fun t => a * f t) =
      a * productionArithmeticRealValue L f := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
  simp [dictionaryCompletePhysicalRHS, mul_assoc]

/-- Euler-weighted first source derivative used by the production first
variation formula. -/
def productionFirstDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t / L ^ 2 *
      sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)

/-- Euler-weighted second source derivative. -/
def productionSecondDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t ^ 2 / L ^ 4 *
      sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)

/-- Weighted mixed source derivative. -/
def productionMixedDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t / L ^ 2 *
      Complex.re
        (sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (1 - t / L))

/-- The three derivative tests needed downstream are admitted by the exact
boundary-flat endpoint cancellations. -/
theorem production_derivative_tests_admissible
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedPhysicalAdmissible L
        (productionFirstDerivativePhysicalTest L K z) ∧
      ProductionWeightedPhysicalAdmissible L
        (productionSecondDerivativePhysicalTest L K z) ∧
      ProductionWeightedPhysicalAdmissible L
        (productionMixedDerivativePhysicalTest L K z w) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · fun_prop
    · exact integrableOn_Icc_of_continuousOn
        (by positivity)
        (by
          continuity)
    · intro t ht
      simp only [Function.mem_support] at ht
      by_contra h
      have hout : t < 0 ∨ L < t := by
        simpa [Set.mem_Icc, not_and_or] using h
      rcases hout with hneg | hgt
      · have : productionFirstDerivativePhysicalTest L K z t = 0 := by
          simp [productionFirstDerivativePhysicalTest, hneg.le]
        exact ht this
      · have : productionFirstDerivativePhysicalTest L K z t = 0 := by
          simp [productionFirstDerivativePhysicalTest, hgt.le]
        exact ht this
  · constructor
    · refine ⟨?_, ?_, ?_⟩
      · fun_prop
      · exact integrableOn_Icc_of_continuousOn
          (by positivity)
          (by continuity)
      · intro t ht
        simp only [Function.mem_support] at ht
        by_contra h
        have hout : t < 0 ∨ L < t := by
          simpa [Set.mem_Icc, not_and_or] using h
        rcases hout with hneg | hgt
        · exact ht (by simp [productionSecondDerivativePhysicalTest, hneg.le])
        · exact ht (by simp [productionSecondDerivativePhysicalTest, hgt.le])
    · refine ⟨?_, ?_, ?_⟩
      · fun_prop
      · exact integrableOn_Icc_of_continuousOn
          (by positivity)
          (by continuity)
      · intro t ht
        simp only [Function.mem_support] at ht
        by_contra h
        have hout : t < 0 ∨ L < t := by
          simpa [Set.mem_Icc, not_and_or] using h
        rcases hout with hneg | hgt
        · exact ht (by simp [productionMixedDerivativePhysicalTest, hneg.le])
        · exact ht (by simp [productionMixedDerivativePhysicalTest, hgt.le])

end Zeta23.CCM
