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
  pole_interval_integrable :
    IntervalIntegrable (fun t => f t * completeSourcePoleWeight t) volume 0 L
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


/-! ### Continuity of the source-coordinate derivative channels -/

@[fun_prop] theorem continuous_sourceEntryDerivative
    (n m : ℤ) :
    Continuous (fun ω : ℝ => sourceEntryDerivative ω n m) := by
  rw [continuous_iff_continuousAt]
  intro ω
  exact (hasDerivAt_sourceEntryDerivative ω n m).continuousAt

@[fun_prop] theorem continuous_sourceEntrySecondDerivative
    (n m : ℤ) :
    Continuous (fun ω : ℝ => sourceEntrySecondDerivative ω n m) := by
  by_cases h : n = m
  · subst m
    have heq :
        (fun ω : ℝ => sourceEntrySecondDerivative ω n n) =
          fun ω =>
            -8 * Real.pi * (n : ℝ) *
                Real.sin (2 * Real.pi * (n : ℝ) * ω)
            - 8 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ω *
                Real.cos (2 * Real.pi * (n : ℝ) * ω) := by
      funext ω
      rw [sourceEntrySecondDerivative, if_pos rfl,
        sourceDiagonalSecondDerivative_formula]
    rw [heq]
    fun_prop
  · have heq :
        (fun ω : ℝ => sourceEntrySecondDerivative ω n m) =
          fun ω =>
            (sourcePotentialSecondDerivative ω n -
              sourcePotentialSecondDerivative ω m) / ((n - m : ℤ) : ℝ) := by
      funext ω
      rw [sourceEntrySecondDerivative, if_neg h]
    rw [heq]
    unfold sourcePotentialSecondDerivative
    fun_prop

@[fun_prop] theorem continuous_sourceContractRealSecondDerivative
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) :
    Continuous (sourceContractRealSecondDerivative K u) := by
  unfold sourceContractRealSecondDerivative
  fun_prop

@[fun_prop] theorem continuous_sourceAtomRealEnergyDerivative
    (K : ℕ)
    (z : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Continuous (sourceAtomRealEnergyDerivative K z) := by
  rw [continuous_iff_continuousAt]
  intro ω
  exact
    (hasDerivAt_sourceAtomRealEnergyDerivative_transport K z ω).continuousAt

@[fun_prop] theorem continuous_sourceAtomRealEnergySecondDerivative
    (K : ℕ)
    (z : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Continuous (sourceAtomRealEnergySecondDerivative K z) := by
  unfold sourceAtomRealEnergySecondDerivative
  exact
    (continuous_sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).re)).add
    (continuous_sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).im))

@[fun_prop] theorem continuous_sourceAtomPairingDerivative
    (K : ℕ)
    (z w : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Continuous (sourceAtomPairingDerivative K z w) := by
  unfold sourceAtomPairingDerivative
  fun_prop

private theorem IntervalIntegrable.ofRealComplex
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => (f t : ℂ)) volume a b := by
  constructor
  · exact hf.1.ofReal
  · exact hf.2.ofReal

/-- Admissibility is stable under addition. -/
theorem ProductionWeightedPhysicalAdmissible.add
    {L : ℝ} {f g : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f)
    (hg : ProductionWeightedPhysicalAdmissible L g) :
    ProductionWeightedPhysicalAdmissible L (fun t => f t + g t) := by
  refine ⟨hf.measurable.add hg.measurable, ?_, ?_, ?_⟩
  · simpa [add_mul] using hf.pole_interval_integrable.add
      hg.pole_interval_integrable
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
  refine ⟨hf.measurable.const_mul a, ?_, ?_, ?_⟩
  · simpa [mul_assoc, mul_left_comm] using
      hf.pole_interval_integrable.const_mul a
  · simpa [mul_assoc, mul_left_comm] using
      hf.arch_interval_integrable.const_mul a
  · intro t ht
    apply hf.support
    intro hzero
    exact ht (by simp [hzero])

/-- Real production evaluation is additive on admitted tests. -/
theorem productionArithmeticRealValue_add_of_admissible
    {L : ℝ} {f g : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f)
    (hg : ProductionWeightedPhysicalAdmissible L g) :
    productionArithmeticRealValue L (fun t => f t + g t) =
      productionArithmeticRealValue L f +
        productionArithmeticRealValue L g := by
  have hfp :
      IntervalIntegrable
        (fun t => (f t : ℂ) * (completeSourcePoleWeight t : ℂ))
        volume 0 L := by
    simpa only [Complex.ofReal_mul] using
      (IntervalIntegrable.ofRealComplex hf.pole_interval_integrable)
  have hgp :
      IntervalIntegrable
        (fun t => (g t : ℂ) * (completeSourcePoleWeight t : ℂ))
        volume 0 L := by
    simpa only [Complex.ofReal_mul] using
      (IntervalIntegrable.ofRealComplex hg.pole_interval_integrable)
  have hfa :
      IntervalIntegrable
        (fun t => (f t : ℂ) * (archDensity t : ℂ))
        volume 0 L := by
    simpa only [Complex.ofReal_mul] using
      (IntervalIntegrable.ofRealComplex hf.arch_interval_integrable)
  have hga :
      IntervalIntegrable
        (fun t => (g t : ℂ) * (archDensity t : ℂ))
        volume 0 L := by
    simpa only [Complex.ofReal_mul] using
      (IntervalIntegrable.ofRealComplex hg.arch_interval_integrable)
  unfold productionArithmeticRealValue productionArithmeticComplexValue
    dictionaryCompletePhysicalRHS
  have hp :
      (∫ x in (0 : ℝ)..L,
        ((f x + g x : ℝ) : ℂ) * (completeSourcePoleWeight x : ℂ)) =
      (∫ x in (0 : ℝ)..L,
        (f x : ℂ) * (completeSourcePoleWeight x : ℂ)) +
      (∫ x in (0 : ℝ)..L,
        (g x : ℂ) * (completeSourcePoleWeight x : ℂ)) := by
    rw [← intervalIntegral.integral_add hfp hgp]
    apply intervalIntegral.integral_congr
    intro x hx
    push_cast
    ring
  have ha :
      (∫ x in (0 : ℝ)..L,
        ((f x + g x : ℝ) : ℂ) * (archDensity x : ℂ)) =
      (∫ x in (0 : ℝ)..L, (f x : ℂ) * (archDensity x : ℂ)) +
      (∫ x in (0 : ℝ)..L, (g x : ℂ) * (archDensity x : ℂ)) := by
    rw [← intervalIntegral.integral_add hfa hga]
    apply intervalIntegral.integral_congr
    intro x hx
    push_cast
    ring
  rw [hp, ha]
  simp_rw [Complex.ofReal_add, add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- Real production evaluation is homogeneous on admitted tests. -/
theorem productionArithmeticRealValue_smul_of_admissible
    {L a : ℝ} {f : ℝ → ℝ}
    (hf : ProductionWeightedPhysicalAdmissible L f) :
    productionArithmeticRealValue L (fun t => a * f t) =
      a * productionArithmeticRealValue L f := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
    dictionaryCompletePhysicalRHS
  simp_rw [Complex.ofReal_mul]
  simp_rw [show ∀ x : ℝ,
      ((a : ℂ) * (f x : ℂ)) * (completeSourcePoleWeight x : ℂ) =
        (a : ℂ) * ((f x : ℂ) * (completeSourcePoleWeight x : ℂ)) by
          intro x; ring]
  simp_rw [show ∀ x : ℝ,
      ((a : ℂ) * (f x : ℂ)) * (archDensity x : ℂ) =
        (a : ℂ) * ((f x : ℂ) * (archDensity x : ℂ)) by
          intro x; ring]
  rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  norm_cast
  ring

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


private theorem intervalIntegrable_first_pole
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t =>
        (productionFirstDerivativePhysicalTest L K z t) *
          completeSourcePoleWeight t)
      volume 0 L := by
  have hraw :
      Continuous (productionFirstDerivativePhysicalRaw L K z) := by
    unfold productionFirstDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  have hint :
      IntervalIntegrable
        (fun t =>
          productionFirstDerivativePhysicalRaw L K z t *
            completeSourcePoleWeight t) volume 0 L :=
    (hraw.mul (by unfold completeSourcePoleWeight; fun_prop)).intervalIntegrable
  apply hint.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards with t ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  simp [productionFirstDerivativePhysicalTest, productionPhysicalClamp_eq ht']

private theorem intervalIntegrable_second_pole
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t =>
        productionSecondDerivativePhysicalTest L K z t *
          completeSourcePoleWeight t)
      volume 0 L := by
  have hraw :
      Continuous (productionSecondDerivativePhysicalRaw L K z) := by
    unfold productionSecondDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  have hint :
      IntervalIntegrable
        (fun t =>
          productionSecondDerivativePhysicalRaw L K z t *
            completeSourcePoleWeight t) volume 0 L :=
    (hraw.mul (by unfold completeSourcePoleWeight; fun_prop)).intervalIntegrable
  apply hint.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards with t ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  simp [productionSecondDerivativePhysicalTest, productionPhysicalClamp_eq ht']

private theorem intervalIntegrable_mixed_pole
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    IntervalIntegrable
      (fun t =>
        productionMixedDerivativePhysicalTest L K z w t *
          completeSourcePoleWeight t)
      volume 0 L := by
  have hraw :
      Continuous (productionMixedDerivativePhysicalRaw L K z w) := by
    unfold productionMixedDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  have hint :
      IntervalIntegrable
        (fun t =>
          productionMixedDerivativePhysicalRaw L K z w t *
            completeSourcePoleWeight t) volume 0 L :=
    (hraw.mul (by unfold completeSourcePoleWeight; fun_prop)).intervalIntegrable
  apply hint.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
  filter_upwards with t ht
  have ht' : t ∈ Icc (0 : ℝ) L := by
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  simp [productionMixedDerivativePhysicalTest, productionPhysicalClamp_eq ht']

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
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
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
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
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
    rw [uIoc_of_le hL.le] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  exact (mixed_arch_eq_regularized hL ht0 ht' K z w).symm

/-- The three physical derivative tests have genuine support and removable
pole/archimedean integrands.  This is the physical half of F02. -/
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
  have hfirstRaw :
      Continuous (productionFirstDerivativePhysicalRaw L K z) := by
    unfold productionFirstDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  have hsecondRaw :
      Continuous (productionSecondDerivativePhysicalRaw L K z) := by
    unfold productionSecondDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  have hmixedRaw :
      Continuous (productionMixedDerivativePhysicalRaw L K z w) := by
    unfold productionMixedDerivativePhysicalRaw
    fun_prop (disch := exact hL.ne')
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, intervalIntegrable_first_pole hL K z,
      intervalIntegrable_first_arch hL K z,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionFirstDerivativePhysicalTest productionPhysicalClamp
    exact
      (Measurable.ite measurableSet_Icc hfirstRaw.measurable measurable_const)
        .aestronglyMeasurable
  · refine ⟨?_, intervalIntegrable_second_pole hL K z,
      intervalIntegrable_second_arch hL K z,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionSecondDerivativePhysicalTest productionPhysicalClamp
    exact
      (Measurable.ite measurableSet_Icc hsecondRaw.measurable measurable_const)
        .aestronglyMeasurable
  · refine ⟨?_, intervalIntegrable_mixed_pole hL K z w,
      intervalIntegrable_mixed_arch hL K z w,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionMixedDerivativePhysicalTest productionPhysicalClamp
    exact
      (Measurable.ite measurableSet_Icc hmixedRaw.measurable measurable_const)
        .aestronglyMeasurable

end Zeta23.CCM

#print axioms Zeta23.CCM.production_derivative_tests_admissible
