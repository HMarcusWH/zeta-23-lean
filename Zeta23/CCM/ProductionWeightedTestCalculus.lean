import Zeta23.CCM.FirstCrossingProductionArithmetic
import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport
import Zeta23.CCM.DictionaryPoleSource
import Zeta23.CCM.DictionaryArchSourceBridge
import Zeta23.GammaFacts.Complete
import Zeta23.ExplicitFormula.Bridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval FourierTransform ArithmeticFunction

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



/-! ### Reusable mixed-test physical integrability -/

/-- A mixed dictionary test that vanishes at the physical origin has an
integrable archimedean density on the positive aperture.  This packages the
same removable-singularity argument used by the complete physical RHS bridge,
but exposes it as an interval-integrability theorem for F03. -/
theorem intervalIntegrable_dictionaryMixedTest_mul_archDensity_of_zero
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hzero : dictionaryMixedTest N x y L 0 = 0) :
    IntervalIntegrable
      (fun t : ℝ =>
        dictionaryMixedTest N x y L t * (archDensity t : ℂ))
      volume 0 L := by
  let k : ℝ → ℂ := dictionaryMixedTest N x y L
  have hk : Continuous k := continuous_dictionaryMixedTest N x y hL
  have hki : Integrable k :=
    hk.integrable_of_hasCompactSupport
      (dictionaryMixedTest_hasCompactSupport N x y L)
  have hFk : Integrable (𝓕 k) :=
    integrable_fourier_dictionaryMixedTest N x y hL
  have heven : ∀ t : ℝ, k (-t) = k t :=
    fun t => dictionaryMixedTest_neg N x y L t
  have hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) :=
    integrable_paperFT_dictionaryMixedTest_mul_mu_sub_mu_zero N x y hL
  have hsub :=
    integrableOn_sub_mul_archDensity_Ioi hk hki hFk heven hmu
  have hpos : IntegrableOn
      (fun t : ℝ => k t * (archDensity t : ℂ)) (Ioi 0) := by
    have hneg := hsub.neg
    simpa [k, hzero] using hneg
  constructor
  · exact hpos.mono_set (by
      intro t ht
      exact ht.1)
  · rw [Ioc_eq_empty (not_lt_of_ge hL.le)]
    exact integrableOn_empty

/-- The pole density of a mixed dictionary test is interval-integrable on the
physical aperture. -/
theorem intervalIntegrable_dictionaryMixedTest_mul_pole
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun t : ℝ =>
        dictionaryMixedTest N x y L t *
          (completeSourcePoleWeight t : ℂ))
      volume 0 L := by
  have hpole :
      Continuous (fun t : ℝ => (completeSourcePoleWeight t : ℂ)) := by
    unfold completeSourcePoleWeight
    fun_prop
  have hprod :
      Continuous (fun t : ℝ =>
        dictionaryMixedTest N x y L t *
          (completeSourcePoleWeight t : ℂ)) :=
    (continuous_dictionaryMixedTest N x y hL).mul hpole
  exact hprod.intervalIntegrable 0 L

/-! ### Smoothness of the source-coordinate derivative channels -/

@[fun_prop] theorem contDiff_two_sourceEntryDerivative
    (n m : ℤ) :
    ContDiff ℝ 2 (fun ω : ℝ => sourceEntryDerivative ω n m) := by
  by_cases h : n = m
  · subst m
    have hfun :
        (fun ω : ℝ => sourceEntryDerivative ω n n) =
          fun ω =>
            2 * Real.cos (2 * Real.pi * (n : ℝ) * ω) +
              2 * ω *
                (-Real.sin (2 * Real.pi * (n : ℝ) * ω) *
                  (2 * Real.pi * (n : ℝ))) := by
      funext ω
      rw [sourceEntryDerivative, if_pos rfl,
        sourceDiagonalDerivative_formula]
    rw [hfun]
    fun_prop
  · unfold sourceEntryDerivative sourcePotentialDerivative
    simp only [if_neg h]
    fun_prop

@[fun_prop] theorem contDiff_two_sourceEntrySecondDerivative
    (n m : ℤ) :
    ContDiff ℝ 2 (fun ω : ℝ => sourceEntrySecondDerivative ω n m) := by
  by_cases h : n = m
  · subst m
    have hfun :
        (fun ω : ℝ => sourceEntrySecondDerivative ω n n) =
          fun ω =>
            -8 * Real.pi * (n : ℝ) *
                Real.sin (2 * Real.pi * (n : ℝ) * ω)
            - 8 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ω *
                Real.cos (2 * Real.pi * (n : ℝ) * ω) := by
      funext ω
      rw [sourceEntrySecondDerivative, if_pos rfl,
        sourceDiagonalSecondDerivative_formula]
    rw [hfun]
    fun_prop
  · unfold sourceEntrySecondDerivative sourcePotentialSecondDerivative
    simp only [if_neg h]
    fun_prop

@[fun_prop] theorem contDiff_two_sourceContractRealDerivative
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) :
    ContDiff ℝ 2 (sourceContractRealDerivative K u) := by
  unfold sourceContractRealDerivative
  fun_prop

@[fun_prop] theorem contDiff_two_sourceContractRealSecondDerivative
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) :
    ContDiff ℝ 2 (sourceContractRealSecondDerivative K u) := by
  unfold sourceContractRealSecondDerivative
  fun_prop

@[fun_prop] theorem contDiff_two_sourceAtomRealEnergyDerivative
    (K : ℕ)
    (z : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ 2 (sourceAtomRealEnergyDerivative K z) := by
  unfold sourceAtomRealEnergyDerivative
  exact
    (contDiff_two_sourceContractRealDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).re)).add
    (contDiff_two_sourceContractRealDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).im))

@[fun_prop] theorem contDiff_two_sourceAtomRealEnergySecondDerivative
    (K : ℕ)
    (z : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ 2 (sourceAtomRealEnergySecondDerivative K z) := by
  unfold sourceAtomRealEnergySecondDerivative
  exact
    (contDiff_two_sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).re)).add
    (contDiff_two_sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) z) i).im))

@[fun_prop] theorem contDiff_two_sourceAtomPairingDerivative
    (K : ℕ)
    (z w : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ 2 (sourceAtomPairingDerivative K z w) := by
  unfold sourceAtomPairingDerivative
  fun_prop

/-- Real projection preserves C2 regularity of a complex-valued real family. -/
@[fun_prop] theorem contDiff_two_complex_re_comp
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun t : ℝ => Complex.re (f t)) := by
  exact Complex.reCLM.contDiff.fun_comp hf

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
  have hsum :
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight x * ((f (Real.log x) + g (Real.log x) : ℝ) : ℂ)) =
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight x * (f (Real.log x) : ℂ)) +
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight x * (g (Real.log x) : ℂ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    push_cast
    ring
  rw [hsum]
  simp only [Complex.add_re, Complex.sub_re]
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
  have hfp :
      (∫ x in (0 : ℝ)..L,
        ((a : ℂ) * (f x : ℂ)) * (completeSourcePoleWeight x : ℂ)) =
      (a : ℂ) * ∫ x in (0 : ℝ)..L,
        (f x : ℂ) * (completeSourcePoleWeight x : ℂ) := by
    simpa [mul_assoc] using
      (intervalIntegral.integral_const_mul
        (μ := volume) (a := (0 : ℝ)) (b := L) (a : ℂ)
        (fun x : ℝ => (f x : ℂ) * (completeSourcePoleWeight x : ℂ)))
  have hfa :
      (∫ x in (0 : ℝ)..L,
        ((a : ℂ) * (f x : ℂ)) * (archDensity x : ℂ)) =
      (a : ℂ) * ∫ x in (0 : ℝ)..L,
        (f x : ℂ) * (archDensity x : ℂ) := by
    simpa [mul_assoc] using
      (intervalIntegral.integral_const_mul
        (μ := volume) (a := (0 : ℝ)) (b := L) (a : ℂ)
        (fun x : ℝ => (f x : ℂ) * (archDensity x : ℂ)))
  have hsum :
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight x * ((a : ℂ) * (f (Real.log x) : ℂ))) =
      (a : ℂ) *
        (∑ x ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          primeSourceWeight x * (f (Real.log x) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hfp, hfa, hsum]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring


/-! ### Global-to-physical authority -/

/-- Verifiable data saying that a global compact C2 test is the even whole-line
lift of a positive-half physical test on the exact aperture.  No arithmetic
identity is stored in this structure. -/
structure ProductionWeightedGlobalLift
    (L : ℝ) (globalTest : ℝ → ℂ) (physicalTest : ℝ → ℝ) : Prop where
  contDiff_two : ContDiff ℝ 2 globalTest
  compact_support : HasCompactSupport globalTest
  even : ∀ t : ℝ, globalTest (-t) = globalTest t
  zero : globalTest 0 = 0
  support_subset : Function.support globalTest ⊆ Icc (-L) L
  agrees_positive :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) L → globalTest t = (physicalTest t : ℂ)

/-- The generic pole channel folds exactly to the positive physical aperture
for every certified global lift. -/
theorem ProductionWeightedGlobalLift.half_pole_eq_physical
    {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} {f : ℝ → ℝ}
    (h : ProductionWeightedGlobalLift L g f) :
    (1 / 2 : ℂ) * dictionaryPoleRHS g =
      ∫ t : ℝ in (0 : ℝ)..L,
        (f t : ℂ) * (completeSourcePoleWeight t : ℂ) := by
  let G : ℝ → ℂ := fun t =>
    g t * ((Real.exp (-|t| / 2) + Real.exp (|t| / 2) : ℝ) : ℂ)
  have hg : Continuous g := h.contDiff_two.continuous
  have hA : Integrable (fun t : ℝ =>
      g t * (Real.exp (-|t| / 2) : ℂ)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport
      h.compact_support.mul_right
  have hB : Integrable (fun t : ℝ =>
      g t * (Real.exp (|t| / 2) : ℂ)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport
      h.compact_support.mul_right
  have hpole := dictionaryPoleRHS_eq_spatial_weights hg h.compact_support
  have hsum : dictionaryPoleRHS g = ∫ t : ℝ, G t := by
    rw [hpole, ← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [G]
    push_cast
    ring
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro t ht
    apply h.support_subset
    intro hgt
    apply ht
    simp [G, hgt]
  rw [hsum]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc
    (by linarith : -L ≤ L) hGsupp]
  have hGcont : Continuous G := by
    dsimp [G]
    exact hg.mul (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0)
    (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hleft :
      (∫ t in -L..(0 : ℝ), G t) =
        ∫ t in (0 : ℝ)..L, G (-t) := by
    have hh := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := L) G
    simpa using hh.symm
  rw [hleft]
  have hevenG : ∀ t : ℝ, G (-t) = G t := by
    intro t
    dsimp [G]
    rw [h.even]
    simp [abs_neg]
  have hleftEq :
      (∫ t in (0 : ℝ)..L, G (-t)) =
        ∫ t in (0 : ℝ)..L, G t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hevenG t
  rw [hleftEq]
  have hpos :
      (∫ t in (0 : ℝ)..L, G t) =
        ∫ t in (0 : ℝ)..L,
          (f t : ℂ) * (completeSourcePoleWeight t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    have htIcc : t ∈ Icc (0 : ℝ) L := ht
    dsimp [G]
    rw [show g t = (f t : ℂ) from h.agrees_positive t htIcc]
    dsimp [completeSourcePoleWeight]
    rw [abs_of_nonneg ht.1]
  rw [hpos]
  ring

/-- The generic prime channel truncates at the exact production cutoff and,
by evenness, reduces to the positive logarithmic samples of the physical
test. -/
theorem ProductionWeightedGlobalLift.half_prime_eq_physical
    {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} {f : ℝ → ℝ}
    (h : ProductionWeightedGlobalLift L g f) :
    (1 / 2 : ℂ) * dictionaryPrimeRHS g =
      -(∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          primeSourceWeight q * (f (Real.log q) : ℂ)) := by
  have htsupp : tsupport g ⊆ Icc (-L) L :=
    closure_minimal h.support_subset isClosed_Icc
  rw [dictionaryPrimeRHS_eq_finset htsupp]
  have hsum :
      (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ((Λ q / Real.sqrt q : ℝ) : ℂ) *
          (g (Real.log q) + g (-Real.log q))) =
      2 * (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * (f (Real.log q) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqmem := Finset.mem_Icc.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1)
    have hqexp : (q : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
    have hlog0 : 0 ≤ Real.log (q : ℝ) :=
      Real.log_natCast_nonneg q
    have hlogL : Real.log (q : ℝ) ≤ L := by
      rw [← Real.log_exp L]
      exact Real.log_le_log hqpos hqexp
    have hpos :
        g (Real.log q) = (f (Real.log q) : ℂ) :=
      h.agrees_positive (Real.log q) ⟨hlog0, hlogL⟩
    have hneg :
        g (-Real.log q) = (f (Real.log q) : ℂ) := by
      rw [h.even]
      exact hpos
    rw [hpos, hneg]
    unfold primeSourceWeight
    push_cast
    ring
  rw [hsum]
  ring

/-- The generic archimedean channel reduces to the admitted positive physical
density integral. -/
theorem ProductionWeightedGlobalLift.half_arch_eq_physical
    {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} {f : ℝ → ℝ}
    (h : ProductionWeightedGlobalLift L g f) :
    (1 / 2 : ℂ) * dictionaryArchRHS g =
      -(∫ t : ℝ in (0 : ℝ)..L,
        (f t : ℂ) * (archDensity t : ℂ)) := by
  have hg : Continuous g := h.contDiff_two.continuous
  have hgi : Integrable g :=
    hg.integrable_of_hasCompactSupport h.compact_support
  have hF : Integrable (𝓕 g) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two
      h.contDiff_two h.compact_support
  have hpft : Integrable (fun τ : ℝ => Zeta23.paperFT g (τ : ℂ)) :=
    Zeta23.EF.integrable_paperFT_ofReal hF
  have hmuAll :
      Integrable (fun τ : ℝ =>
        Zeta23.paperFT g (τ : ℂ) * (Zeta23.mu τ : ℂ)) :=
    Zeta23.EF.integrable_paperFT_mul_mu
      h.contDiff_two h.compact_support Zeta23.gammaFacts
  have hmu0 :
      Integrable (fun τ : ℝ =>
        Zeta23.paperFT g (τ : ℂ) * (Zeta23.mu 0 : ℂ)) :=
    hpft.mul_const _
  have hmuSub :
      Integrable (fun τ : ℝ =>
        Zeta23.paperFT g (τ : ℂ) *
          ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) := by
    refine (hmuAll.sub hmu0).congr (Filter.Eventually.of_forall fun τ => ?_)
    change
      Zeta23.paperFT g (τ : ℂ) * (Zeta23.mu τ : ℂ) -
          Zeta23.paperFT g (τ : ℂ) * (Zeta23.mu 0 : ℂ) =
        Zeta23.paperFT g (τ : ℂ) *
          ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)
    push_cast
    ring
  have harch :=
    dictionaryArchRHS_eq_neg_two_mul_archDensity_integral_of_zero
      hg hgi hF h.even hmuSub h.zero
  rw [harch]
  let A : ℝ → ℂ := fun t => g t * (archDensity t : ℂ)
  have hrestrictIoc :
      (∫ t : ℝ in Ioi 0, A t) =
        ∫ t : ℝ in Ioc 0 L, A t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioi Ioc_subset_Ioi_self
    intro t ht
    have ht0 : 0 < t := ht.1
    have htL : L < t := by
      by_contra hn
      exact ht.2 ⟨ht0, le_of_not_gt hn⟩
    have hnot : t ∉ Icc (-L) L := by
      intro hmem
      exact (not_le_of_gt htL) hmem.2
    have hgz : g t = 0 := by
      by_contra hne
      exact hnot (h.support_subset hne)
    simp [A, hgz]
  have hrestrict :
      (∫ t : ℝ in Ioi 0, A t) =
        ∫ t : ℝ in Icc 0 L, A t := by
    rw [integral_Icc_eq_integral_Ioc]
    exact hrestrictIoc
  rw [hrestrict]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hL.le]
  have hpos :
      (∫ t : ℝ in (0 : ℝ)..L, A t) =
        ∫ t : ℝ in (0 : ℝ)..L,
          (f t : ℂ) * (archDensity t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    dsimp [A]
    rw [show g t = (f t : ℂ) from h.agrees_positive t ht]
  rw [hpos]
  ring

/-- A global lift with the verifiable analytic fields above has exact
literature-RHS/physical-RHS authority.  This is the theorem that downstream
production tests must use; authority is not an input field. -/
theorem ProductionWeightedGlobalLift.physical_authority
    {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} {f : ℝ → ℝ}
    (h : ProductionWeightedGlobalLift L g f) :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS g =
      productionArithmeticComplexValue L (fun t => (f t : ℂ)) := by
  rw [literatureRHS_eq_dictionaryChannels]
  rw [mul_add, mul_add]
  rw [h.half_pole_eq_physical hL,
      h.half_prime_eq_physical hL,
      h.half_arch_eq_physical hL]
  unfold productionArithmeticComplexValue dictionaryCompletePhysicalRHS
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


/-- The unclamped derivative channels are genuinely C2 on the real line. -/
theorem contDiff_two_productionFirstDerivativePhysicalRaw
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ContDiff ℝ 2 (productionFirstDerivativePhysicalRaw L K z) := by
  unfold productionFirstDerivativePhysicalRaw
  fun_prop

theorem contDiff_two_productionSecondDerivativePhysicalRaw
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ContDiff ℝ 2 (productionSecondDerivativePhysicalRaw L K z) := by
  unfold productionSecondDerivativePhysicalRaw
  fun_prop

theorem contDiff_two_productionMixedDerivativePhysicalRaw
    {L : ℝ} (hL : L ≠ 0) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ContDiff ℝ 2 (productionMixedDerivativePhysicalRaw L K z w) := by
  let p : ℝ → ℂ := fun t =>
    sourceAtomPairingDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (1 - t / L)
  have hp : ContDiff ℝ 2 p := by
    dsimp [p]
    exact (contDiff_two_sourceAtomPairingDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (w : EuclideanSpace ℂ (Fin (2 * K + 1)))).fun_comp
        (by fun_prop (disch := exact hL))
  have hre : ContDiff ℝ 2 (fun t : ℝ => Complex.re (p t)) :=
    contDiff_two_complex_re_comp hp
  unfold productionMixedDerivativePhysicalRaw
  change ContDiff ℝ 2 (fun t : ℝ => t / L ^ 2 * Complex.re (p t))
  exact (by fun_prop (disch := exact hL))

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
  field_simp [hL.ne'] <;> ring

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
  field_simp [hL.ne'] <;> ring

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
  field_simp [hL.ne'] <;> ring


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
  have hpole : Continuous completeSourcePoleWeight := by
    unfold completeSourcePoleWeight
    fun_prop
  have hprod :
      Continuous (fun t : ℝ =>
        productionFirstDerivativePhysicalRaw L K z t * completeSourcePoleWeight t) :=
    hraw.mul hpole
  have hint :
      IntervalIntegrable
        (fun t =>
          productionFirstDerivativePhysicalRaw L K z t *
            completeSourcePoleWeight t) volume 0 L :=
    hprod.intervalIntegrable 0 L
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
  have hpole : Continuous completeSourcePoleWeight := by
    unfold completeSourcePoleWeight
    fun_prop
  have hprod :
      Continuous (fun t : ℝ =>
        productionSecondDerivativePhysicalRaw L K z t * completeSourcePoleWeight t) :=
    hraw.mul hpole
  have hint :
      IntervalIntegrable
        (fun t =>
          productionSecondDerivativePhysicalRaw L K z t *
            completeSourcePoleWeight t) volume 0 L :=
    hprod.intervalIntegrable 0 L
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
  have hpole : Continuous completeSourcePoleWeight := by
    unfold completeSourcePoleWeight
    fun_prop
  have hprod :
      Continuous (fun t : ℝ =>
        productionMixedDerivativePhysicalRaw L K z w t * completeSourcePoleWeight t) :=
    hraw.mul hpole
  have hint :
      IntervalIntegrable
        (fun t =>
          productionMixedDerivativePhysicalRaw L K z w t *
            completeSourcePoleWeight t) volume 0 L :=
    hprod.intervalIntegrable 0 L
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
      Measurable.aestronglyMeasurable
        (Measurable.ite measurableSet_Icc hfirstRaw.measurable measurable_const)
  · refine ⟨?_, intervalIntegrable_second_pole hL K z,
      intervalIntegrable_second_arch hL K z,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionSecondDerivativePhysicalTest productionPhysicalClamp
    exact
      Measurable.aestronglyMeasurable
        (Measurable.ite measurableSet_Icc hsecondRaw.measurable measurable_const)
  · refine ⟨?_, intervalIntegrable_mixed_pole hL K z w,
      intervalIntegrable_mixed_arch hL K z w,
      productionPhysicalClamp_support_subset L _⟩
    unfold productionMixedDerivativePhysicalTest productionPhysicalClamp
    exact
      Measurable.aestronglyMeasurable
        (Measurable.ite measurableSet_Icc hmixedRaw.measurable measurable_const)

end Zeta23.CCM

#print axioms Zeta23.CCM.production_derivative_tests_admissible
