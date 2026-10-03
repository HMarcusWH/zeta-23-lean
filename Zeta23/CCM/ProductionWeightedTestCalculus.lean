import Zeta23.CCM.FirstCrossingProductionArithmetic
import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# Post-#282 weighted production-test calculus

There are two different objects in the explicit-formula bridge:

* a positive-half physical test, sampled only on `[0,L]` and at
  `log q ∈ [0,L]`;
* a global compact C² test supplied to the literature explicit formula.

This file keeps them separate.  In particular it does **not** claim that the
unclamped formula `t * e'(1-t/L)` is compactly supported on the real line.

The positive-half tests below are explicitly clamped.  Their archimedean
integrability is proved through the already-merged removable quantity
`regularizedArchScale = t * archDensity` away from the null endpoint.
-/

/-- Clamp a positive-half physical test to its actual physical aperture. -/
def productionPhysicalClamp (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => if t ∈ Icc (0 : ℝ) L then f t else 0

@[simp] theorem productionPhysicalClamp_eq
    {L t : ℝ} {f : ℝ → ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionPhysicalClamp L f t = f t := by
  simp [productionPhysicalClamp, ht]

@[simp] theorem productionPhysicalClamp_eq_zero_of_not_mem
    {L t : ℝ} {f : ℝ → ℝ} (ht : t ∉ Icc (0 : ℝ) L) :
    productionPhysicalClamp L f t = 0 := by
  simp [productionPhysicalClamp, ht]

theorem productionPhysicalClamp_support_subset
    (L : ℝ) (f : ℝ → ℝ) :
    Function.support (productionPhysicalClamp L f) ⊆ Icc (0 : ℝ) L := by
  intro t ht
  by_contra hmem
  exact ht (productionPhysicalClamp_eq_zero_of_not_mem hmem)

/-- Analytic requirements needed from the physical half of a test before it is
paired with a separately constructed global compact lift.  The singular
archimedean term is stored as an interval-integrability theorem, not inferred
from ordinary continuity of `archDensity` at zero. -/
structure ProductionWeightedPhysicalAdmissible
    (L : ℝ) (f : ℝ → ℝ) : Prop where
  measurable : AEStronglyMeasurable f
  arch_interval_integrable :
    IntervalIntegrable (fun t => f t * archDensity t) volume 0 L
  support : Function.support f ⊆ Icc 0 L

/-- The full explicit-formula authorization remains a global/physical pair.
Nothing in this structure is an arithmetic curvature equality. -/
structure ProductionWeightedTestAdmissible
    (L : ℝ) (globalTest : ℝ → ℂ) (physicalTest : ℝ → ℝ) : Prop where
  global_contDiff_two : ContDiff ℝ 2 globalTest
  global_compact_support : HasCompactSupport globalTest
  physical_admissible :
    ProductionWeightedPhysicalAdmissible L physicalTest
  physical_authority :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS globalTest =
      productionArithmeticComplexValue L (fun t => (physicalTest t : ℂ))

/-- Admissibility is stable under addition. -/
theorem ProductionWeightedPhysicalAdmissible.add
    {L : ℝ} {f g : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f)
    (hg : ProductionWeightedPhysicalAdmissible L g) :
    ProductionWeightedPhysicalAdmissible L (fun t => f t + g t) := by
  refine ⟨hf.measurable.add hg.measurable, ?_, ?_⟩
  · simpa [add_mul] using hf.arch_interval_integrable.add
      hg.arch_interval_integrable
  · intro t ht
    by_contra hmem
    have hf0 : f t = 0 := by
      by_contra h
      exact hmem (hf.support h)
    have hg0 : g t = 0 := by
      by_contra h
      exact hmem (hg.support h)
    exact ht (by simp [hf0, hg0])

/-- Admissibility is stable under real scaling. -/
theorem ProductionWeightedPhysicalAdmissible.smul
    {L a : ℝ} {f : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f) :
    ProductionWeightedPhysicalAdmissible L (fun t => a * f t) := by
  refine ⟨hf.measurable.const_mul a, ?_, ?_⟩
  · simpa [mul_assoc, mul_left_comm] using
      hf.arch_interval_integrable.const_mul a
  · intro t ht
    apply hf.support
    intro hzero
    exact ht (by simp [hzero])

/-- Real production evaluation is additive on admitted tests.  The proof is
value-level and uses only the actual physical RHS definition. -/
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

/-- Unclamped first source derivative on the physical half-line. -/
def productionFirstDerivativePhysicalRaw
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t / L ^ 2 *
      sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)

/-- Unclamped Euler-weighted second source derivative. -/
def productionSecondDerivativePhysicalRaw
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t ^ 2 / L ^ 4 *
      sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)

/-- Unclamped weighted mixed source derivative. -/
def productionMixedDerivativePhysicalRaw
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    t / L ^ 2 *
      Complex.re
        (sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (1 - t / L))

/-- Physical first-variation test with honest support. -/
def productionFirstDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  productionPhysicalClamp L (productionFirstDerivativePhysicalRaw L K z)

/-- Physical fixed-second test with honest support. -/
def productionSecondDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  productionPhysicalClamp L (productionSecondDerivativePhysicalRaw L K z)

/-- Physical mixed first-variation test with honest support. -/
def productionMixedDerivativePhysicalTest
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  productionPhysicalClamp L (productionMixedDerivativePhysicalRaw L K z w)

/-- Continuous removable archimedean representative for the first test. -/
def productionFirstDerivativeArchRegularized
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    (1 / L ^ 2) *
      sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L) *
      regularizedArchScale t

/-- Continuous removable archimedean representative for the second test. -/
def productionSecondDerivativeArchRegularized
    (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    (t / L ^ 4) *
      sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L) *
      regularizedArchScale t

/-- Continuous removable archimedean representative for the mixed test. -/
def productionMixedDerivativeArchRegularized
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℝ :=
  fun t =>
    (1 / L ^ 2) *
      Complex.re
        (sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (1 - t / L)) *
      regularizedArchScale t

private theorem first_arch_eq_regularized
    {L t : ℝ} (hL : 0 < L) (ht0 : t ≠ 0) (htL : t ∈ Icc (0 : ℝ) L)
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionFirstDerivativePhysicalTest L K z t * archDensity t =
      productionFirstDerivativeArchRegularized L K z t := by
  rw [productionFirstDerivativePhysicalTest,
    productionPhysicalClamp_eq htL,
    productionFirstDerivativePhysicalRaw,
    productionFirstDerivativeArchRegularized,
    regularizedArchScale_eq_mul_archDensity ht0]
  field_simp [hL.ne']
  ring

private theorem second_arch_eq_regularized
    {L t : ℝ} (hL : 0 < L) (ht0 : t ≠ 0) (htL : t ∈ Icc (0 : ℝ) L)
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionSecondDerivativePhysicalTest L K z t * archDensity t =
      productionSecondDerivativeArchRegularized L K z t := by
  rw [productionSecondDerivativePhysicalTest,
    productionPhysicalClamp_eq htL,
    productionSecondDerivativePhysicalRaw,
    productionSecondDerivativeArchRegularized,
    regularizedArchScale_eq_mul_archDensity ht0]
  field_simp [hL.ne']
  ring

private theorem mixed_arch_eq_regularized
    {L t : ℝ} (hL : 0 < L) (ht0 : t ≠ 0) (htL : t ∈ Icc (0 : ℝ) L)
    (K : ℕ) (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionMixedDerivativePhysicalTest L K z w t * archDensity t =
      productionMixedDerivativeArchRegularized L K z w t := by
  rw [productionMixedDerivativePhysicalTest,
    productionPhysicalClamp_eq htL,
    productionMixedDerivativePhysicalRaw,
    productionMixedDerivativeArchRegularized,
    regularizedArchScale_eq_mul_archDensity ht0]
  field_simp [hL.ne']
  ring

private theorem intervalIntegrable_first_arch
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t => productionFirstDerivativePhysicalTest L K z t * archDensity t)
      volume 0 L := by
  have hreg :
      IntervalIntegrable
        (productionFirstDerivativeArchRegularized L K z) volume 0 L := by
    apply Continuous.intervalIntegrable
    unfold productionFirstDerivativeArchRegularized
    fun_prop (disch := exact hL.ne')
  apply hreg.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with t ht0 ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    simpa only [uIcc_of_le hL.le] using ht
  exact (first_arch_eq_regularized hL ht0 ht' K z).symm

private theorem intervalIntegrable_second_arch
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t => productionSecondDerivativePhysicalTest L K z t * archDensity t)
      volume 0 L := by
  have hreg :
      IntervalIntegrable
        (productionSecondDerivativeArchRegularized L K z) volume 0 L := by
    apply Continuous.intervalIntegrable
    unfold productionSecondDerivativeArchRegularized
    fun_prop (disch := exact hL.ne')
  apply hreg.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with t ht0 ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    simpa only [uIcc_of_le hL.le] using ht
  exact (second_arch_eq_regularized hL ht0 ht' K z).symm

private theorem intervalIntegrable_mixed_arch
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t => productionMixedDerivativePhysicalTest L K z w t * archDensity t)
      volume 0 L := by
  have hreg :
      IntervalIntegrable
        (productionMixedDerivativeArchRegularized L K z w) volume 0 L := by
    apply Continuous.intervalIntegrable
    unfold productionMixedDerivativeArchRegularized
    fun_prop (disch := exact hL.ne')
  apply hreg.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with t ht0 ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    simpa only [uIcc_of_le hL.le] using ht
  exact (mixed_arch_eq_regularized hL ht0 ht' K z w).symm

/-- The three physical derivative tests have genuine support and a removable
archimedean singularity.  This is the production half of F02. -/
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
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, intervalIntegrable_first_arch hL K z,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionFirstDerivativePhysicalTest productionPhysicalClamp
    fun_prop
  · refine ⟨?_, intervalIntegrable_second_arch hL K z,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionSecondDerivativePhysicalTest productionPhysicalClamp
    fun_prop
  · refine ⟨?_, intervalIntegrable_mixed_arch hL K z w,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionMixedDerivativePhysicalTest productionPhysicalClamp
    fun_prop

end Zeta23.CCM

#print axioms Zeta23.CCM.production_derivative_tests_admissible
