import Zeta23.CCM.NativeWeilResponse
import Zeta23.ExceptionalZero.UniversalSincSignedExcursions
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt
import Zeta23.CCM.NativeCompletedInputZetaLaplace
import Zeta23.OPICAFollowup.NativeSourceTransforms
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Zeta23.OPICARound4.HyperbolaDiagonal
import Zeta23.CCM.NativeAbelDiscrepancy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support
import Zeta23.OPICARound4.MobiusHyperbola
import Zeta23.CCM.OriginalSincNativeConvolution
import Zeta23.CCM.NativeIntegerDriveFiniteOrderBounds

/-!
# Exact hyperbola decomposition of the literal original correlation source

The source is the unchanged fixed-scale kernel self-convolution. All prime
powers are retained, and its actual compact support supplies the finite cutoff.
This module proves exact source identities and inherited integer-drive bounds.
It supplies no signed inverse estimate. Its final conditional theorem derives the
exact RH statement only from the explicit eventual native long-term lower bound.
-/

noncomputable section
open Finset MeasureTheory
open scoped Topology

namespace Zeta23.OPICARound4
open CCM

def actualCorrelationKernel (u : ℝ) : ℂ :=
  ∫ x : ℝ, universalSincKernel UniversalSinc.fixedScale x *
    universalSincKernel UniversalSinc.fixedScale (u - x)

def actualCorrelationSource (u : ℝ) : ℝ := (actualCorrelationKernel u).re

def actualCorrelationCutoff (t : ℝ) : ℕ :=
  nativeHistoryCutoff (2 * UniversalSinc.fixedScale) t

def actualCorrelationWeight (t : ℝ) (n : ℕ) : ℝ :=
  actualCorrelationSource (t - Real.log n) / Real.sqrt n

def actualCorrelationPrimeField (t : ℝ) : ℝ :=
  (nativeComplexPrimeField actualCorrelationKernel t).re

def actualCorrelationIntegerDrive (t : ℝ) : ℝ :=
  (nativeComplexIntegerDrive actualCorrelationKernel t).re

private theorem nativeIntegerDrive_convolution {s r : ℝ} {q j : ℝ → ℂ}
    (hq : NativeComplexSourceSupported s q) (hj : NativeComplexSourceSupported r j)
    (hqc : Continuous q) (hjc : Continuous j) (t : ℝ) :
    nativeComplexIntegerDrive (fun u => ∫ x : ℝ, q x * j (u - x)) t =
      ∫ x : ℝ, q x * nativeComplexIntegerDrive j (t - x) := by
  let M := nativeHistoryCutoff (s + r) t + 1
  have hi (n : ℕ) : Integrable (fun x : ℝ =>
      (nativeIntegerDriveCoefficient n : ℂ) * (q x * j (t - Real.log n - x))) :=
    ((hqc.mul (hjc.comp (by fun_prop))).integrable_of_hasCompactSupport
      hq.hasCompactSupport.mul_right).const_mul _
  rw [nativeComplexIntegerDrive_eq_history_sum (nativeComplexConvolution_supported hq hj) le_rfl]
  calc
    (∑ n ∈ range M, (nativeIntegerDriveCoefficient n : ℂ) *
        ∫ x : ℝ, q x * j (t - Real.log n - x)) =
        ∫ x : ℝ, ∑ n ∈ range M, (nativeIntegerDriveCoefficient n : ℂ) *
          (q x * j (t - Real.log n - x)) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = ∫ x : ℝ, q x * nativeComplexIntegerDrive j (t - x) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Set.Icc (-s) s
      · have ht : t - x ≤ t + s := by linarith [hx.1]
        rw [nativeComplexIntegerDrive_eq_history_sum hj ht]
        have hM : nativeHistoryCutoff r (t + s) + 1 = M := by
          simp only [M, nativeHistoryCutoff, add_assoc]
        rw [hM, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have he : t - Real.log n - x = t - x - Real.log n := by ring
        rw [he]
        ring
      · have hqx : q x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hq h))
        simp only [hqx, zero_mul, mul_zero, Finset.sum_const_zero]

/-- The literal correlation-source drive is the positive original density
    convolved with the already constructed native integer drive. -/
theorem actualCorrelationIntegerDrive_eq_sourceConvolution (t : ℝ) :
    actualCorrelationIntegerDrive t =
      ∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x *
        nativeOriginalIntegerDrive (t - x) := by
  have hconv : actualCorrelationKernel = fun u => ∫ x : ℝ,
      (universalSincSource UniversalSinc.fixedScale x : ℂ) *
        (nativeOriginalSource (u - x) : ℂ) := by
    funext u
    unfold actualCorrelationKernel
    rw [universalSincKernel_selfConvolution_eq_source_second UniversalSinc.fixedScale_pos u]
    apply integral_congr_ae
    filter_upwards with x
    rw [universalSincSecondKernel_eq_real UniversalSinc.fixedScale_pos]
    rfl
  unfold actualCorrelationIntegerDrive
  rw [hconv, nativeIntegerDrive_convolution
    (NativeComplexSourceSupported.ofReal (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (universalSincSource_support
        UniversalSinc.fixedScale_pos h))))
    (NativeComplexSourceSupported.ofReal nativeOriginalSource_supported)
    (Complex.continuous_ofReal.comp (universalSincSource_contDiff UniversalSinc.fixedScale_pos).continuous)
    (Complex.continuous_ofReal.comp nativeOriginalSource_contDiff.continuous)]
  have he : (fun x : ℝ => (universalSincSource UniversalSinc.fixedScale x : ℂ) *
      nativeComplexIntegerDrive (fun u => (nativeOriginalSource u : ℂ)) (t - x)) =
      fun x : ℝ => ((universalSincSource UniversalSinc.fixedScale x *
        nativeOriginalIntegerDrive (t - x) : ℝ) : ℂ) := by
    funext x
    rw [nativeComplexIntegerDrive_ofReal nativeOriginalSource_supported]
    push_cast
    rfl
  rw [he, integral_complex_ofReal]
  rfl

/-- Every fixed exponential decay estimate for the original integer drive
    transfers to the literal correlation source, with its exact source radius. -/
theorem actualCorrelationIntegerDrive_bound_of_native_bound
    (A C T t : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hU : ∀ v : ℝ, T ≤ v → |nativeOriginalIntegerDrive v| ≤ C * Real.exp (-A * v))
    (ht : T + UniversalSinc.fixedScale ≤ t) :
    |actualCorrelationIntegerDrive t| ≤
      (C * Real.exp (A * UniversalSinc.fixedScale)) * Real.exp (-A * t) := by
  let q := universalSincSource UniversalSinc.fixedScale
  let B := (C * Real.exp (A * UniversalSinc.fixedScale)) * Real.exp (-A * t)
  have hqc : Continuous q := (universalSincSource_contDiff UniversalSinc.fixedScale_pos).continuous
  have hqs : HasCompactSupport q := by
    apply HasCompactSupport.intro (K := Set.Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
      isCompact_Icc
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (universalSincSource_support
      UniversalSinc.fixedScale_pos h))
  have hi : Integrable (fun x : ℝ => q x * nativeOriginalIntegerDrive (t - x)) :=
    (hqc.mul (nativeOriginalIntegerDrive_continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      hqs.mul_right
  have hb : ∀ x : ℝ, |q x * nativeOriginalIntegerDrive (t - x)| ≤ q x * B := by
    intro x
    have hq : 0 ≤ q x := universalSincSource_nonneg UniversalSinc.fixedScale_pos x
    by_cases hx : x ∈ Set.Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
    · have hxT : T ≤ t - x := by linarith [hx.2]
      have he : Real.exp (-A * (t - x)) ≤
          Real.exp (A * UniversalSinc.fixedScale) * Real.exp (-A * t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hx.2]
      rw [abs_mul, abs_of_nonneg hq]
      apply mul_le_mul_of_nonneg_left _ hq
      exact (hU (t - x) hxT).trans (by
        dsimp [B]
        calc
          C * Real.exp (-A * (t - x)) ≤
              C * (Real.exp (A * UniversalSinc.fixedScale) * Real.exp (-A * t)) :=
            mul_le_mul_of_nonneg_left he hC
          _ = _ := by ring)
    · have hz : q x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx (universalSincSource_support UniversalSinc.fixedScale_pos h))
      simp only [hz, zero_mul, abs_zero, le_refl]
  rw [actualCorrelationIntegerDrive_eq_sourceConvolution]
  change |∫ x : ℝ, q x * nativeOriginalIntegerDrive (t - x)| ≤ B
  calc
    _ ≤ ∫ x : ℝ, |q x * nativeOriginalIntegerDrive (t - x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, q x * B := integral_mono hi.abs
      ((hqc.integrable_of_hasCompactSupport hqs).mul_const B) hb
    _ = B := by
      rw [integral_mul_const]
      change (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) * B = B
      rw [universalSincSource_integral_one UniversalSinc.fixedScale_pos, one_mul]

/-- Rapid decay is unconditional for the genuine correlation-source drive.
    It does not assert a bound for its signed Mobius inverse. -/
theorem actualCorrelationIntegerDrive_rapid_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |actualCorrelationIntegerDrive t| ≤ C * Real.exp (-A * t) := by
  obtain ⟨C, hC, T, hT, hU⟩ := nativeOriginalIntegerDrive_rapid_bound A hA
  refine ⟨C * Real.exp (A * UniversalSinc.fixedScale), by positivity,
    T + UniversalSinc.fixedScale, add_nonneg hT UniversalSinc.fixedScale_pos.le, ?_⟩
  intro t ht
  exact actualCorrelationIntegerDrive_bound_of_native_bound A C T t hA hC.le hU ht

theorem actualCorrelationKernel_supported :
    NativeComplexSourceSupported (2 * UniversalSinc.fixedScale) actualCorrelationKernel := by
  change NativeComplexSourceSupported (2 * UniversalSinc.fixedScale) (fun u =>
    ∫ x : ℝ, universalSincKernel UniversalSinc.fixedScale x *
      universalSincKernel UniversalSinc.fixedScale (u - x))
  simpa only [two_mul] using
    nativeComplexConvolution_supported
      (universalSincKernel_support UniversalSinc.fixedScale_pos)
      (universalSincKernel_support UniversalSinc.fixedScale_pos)

theorem actualCorrelationCutoff_exact (t : ℝ) :
    actualCorrelationCutoff t = ⌊Real.exp (t + 2 * UniversalSinc.fixedScale)⌋₊ := rfl

theorem actualCorrelationWeight_zero_above (t : ℝ) :
    ∀ n, actualCorrelationCutoff t < n → actualCorrelationWeight t n = 0 := by
  intro n hn
  have hz := nativeComplexSourceTranslate_zero_above_history
    actualCorrelationKernel_supported le_rfl hn
  simp only [actualCorrelationWeight, actualCorrelationSource, hz, Complex.zero_re, zero_div]

theorem actualCorrelationPrimeField_eq_weighted_vonMangoldt (t : ℝ) :
    actualCorrelationPrimeField t =
      ∑ n ∈ Ioc 0 (actualCorrelationCutoff t),
        ArithmeticFunction.vonMangoldt n * actualCorrelationWeight t n := by
  unfold actualCorrelationPrimeField
  rw [nativeComplexPrimeField_eq_history_sum actualCorrelationKernel_supported le_rfl]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  change (∑ n ∈ range (actualCorrelationCutoff t + 1),
      nativePrimeCoefficient n * (actualCorrelationKernel (t - Real.log n)).re) = _
  have hsub : Ioc 0 (actualCorrelationCutoff t) ⊆ range (actualCorrelationCutoff t + 1) := by
    intro n hn
    simp only [mem_Ioc] at hn
    simp only [mem_range]
    omega
  have hsum := sum_subset hsub (f := fun n =>
    nativePrimeCoefficient n * (actualCorrelationKernel (t - Real.log n)).re) (by
      intro n hn hnI
      have hn0 : n = 0 := by
        simp only [mem_range] at hn
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hnI
        omega
      subst n
      simp [nativePrimeCoefficient])
  rw [← hsum]
  apply sum_congr rfl
  intro n hn
  unfold nativePrimeCoefficient actualCorrelationWeight actualCorrelationSource
  ring

theorem actualCorrelationPrimeField_eq_nativeSourceConvolution (t : ℝ) :
    actualCorrelationPrimeField t =
      (∫ x : ℝ, UniversalSinc.originalDensityComplex UniversalSinc.fixedScale x *
        (nativeOriginalPrimeField (t - x) : ℂ)).re := by
  exact congrArg Complex.re (originalDetector_correlationField_eq_sourceConvolution t)

def actualCorrelationLogarithmicTest (t : ℝ) : ℕ → ℝ :=
  finiteLogarithmicTest (actualCorrelationWeight t) (actualCorrelationCutoff t)

/-- The finite logarithmic test is exactly the literal integer drive sampled
    at the delayed argument. This is not a global inverse-norm estimate. -/
theorem actualCorrelationLogarithmicTest_eq_integerDrive (t : ℝ) (a : ℕ) (ha : 0 < a) :
    actualCorrelationLogarithmicTest t a =
      actualCorrelationIntegerDrive (t - Real.log a) / Real.sqrt a := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hlog : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr ha)
  have ht : t - Real.log a ≤ t := by linarith
  unfold actualCorrelationLogarithmicTest finiteLogarithmicTest actualCorrelationIntegerDrive
  rw [nativeComplexIntegerDrive_eq_history_sum actualCorrelationKernel_supported ht]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, sum_div]
  change _ = ∑ b ∈ range (actualCorrelationCutoff t + 1),
    nativeIntegerDriveCoefficient b *
      (actualCorrelationKernel (t - Real.log a - Real.log b)).re / Real.sqrt a
  have hsub : Ioc 0 (actualCorrelationCutoff t) ⊆ range (actualCorrelationCutoff t + 1) := by
    intro n hn
    simp only [mem_Ioc] at hn
    simp only [mem_range]
    omega
  have hsum := sum_subset hsub (f := fun b =>
    nativeIntegerDriveCoefficient b *
      (actualCorrelationKernel (t - Real.log a - Real.log b)).re / Real.sqrt a) (by
      intro b hb hbI
      have hb0 : b = 0 := by
        simp only [mem_range] at hb
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hbI
        omega
      subst b
      simp [nativeIntegerDriveCoefficient])
  rw [← hsum]
  apply sum_congr rfl
  intro b hb
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr (mem_Ioc.mp hb).1
  unfold actualCorrelationWeight actualCorrelationSource nativeIntegerDriveCoefficient
  rw [Nat.cast_mul, Real.log_mul haR.ne' hbR.ne', Real.sqrt_mul (Nat.cast_nonneg a)]
  rw [show t - (Real.log a + Real.log b) = t - Real.log a - Real.log b by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The unnormalized fixed-source test in multiplicative coordinates.
    Its positive-input normalization is supplied by the next theorem. -/
def actualFlatMobiusTest (r : ℝ) : ℝ :=
  actualCorrelationIntegerDrive (-Real.log r) / Real.sqrt r

/-- The square-root scaling between the actual history test and the fixed
    multiplicative test is explicit; the two must not be identified directly. -/
theorem actualFlatMobiusTest_normalization (t : ℝ) (a : ℕ) (ha : 0 < a) :
    Real.sqrt (Real.exp t) * actualCorrelationLogarithmicTest t a =
      actualFlatMobiusTest ((a : ℝ) / Real.exp t) := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  rw [actualCorrelationLogarithmicTest_eq_integerDrive t a ha]
  unfold actualFlatMobiusTest
  rw [Real.log_div haR.ne' (Real.exp_pos t).ne', Real.log_exp,
    Real.sqrt_div (Nat.cast_nonneg a)]
  rw [show -(Real.log a - t) = t - Real.log a by ring]
  field_simp [ne_of_gt (Real.sqrt_pos.2 haR), ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos t))]

theorem actualCorrelationPrimeField_eq_mobius (t : ℝ) :
    actualCorrelationPrimeField t =
      hyperbolaU (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t) := by
  rw [actualCorrelationPrimeField_eq_weighted_vonMangoldt]
  exact vonMangoldt_weighted_is_hyperbolaU _ _ (actualCorrelationWeight_zero_above t)

theorem actualCorrelationPrimeField_hyperbola (t : ℝ) :
    actualCorrelationPrimeField t =
      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t) -
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t) := by
  rw [actualCorrelationPrimeField_eq_weighted_vonMangoldt]
  exact finite_vonMangoldt_hyperbola _ _ (actualCorrelationWeight_zero_above t)

/-- The logarithmic test vanishes beyond half of the actual history cutoff:
    the only possibly surviving integer factor would be one, whose log is zero. -/
theorem actualCorrelationLogarithmicTest_half_support (t : ℝ) :
    ∀ n, actualCorrelationCutoff t / 2 < n → actualCorrelationLogarithmicTest t n = 0 :=
  finiteLogarithmicTest_half_support _ _ (actualCorrelationWeight_zero_above t)

/-- Exact square-root hyperbola at the sharpened support. The inner logarithmic
    test keeps its original cutoff; only its outer Mobius range is halved. -/
theorem actualCorrelationPrimeField_hyperbola_half (t : ℝ) :
    actualCorrelationPrimeField t =
      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) -
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) := by
  rw [actualCorrelationPrimeField_eq_weighted_vonMangoldt]
  exact finite_vonMangoldt_hyperbola_half _ _ (actualCorrelationWeight_zero_above t)

/-- Existing source-identical adapter, now tied to the exact finite signed
    hyperbola target. No estimate of either side is assumed. -/
theorem actualNativeSourceConvolution_hyperbola_half (t : ℝ) :
    (∫ x : ℝ, UniversalSinc.originalDensityComplex UniversalSinc.fixedScale x *
        (nativeOriginalPrimeField (t - x) : ℂ)).re =
      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) -
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) := by
  rw [← actualCorrelationPrimeField_eq_nativeSourceConvolution]
  exact actualCorrelationPrimeField_hyperbola_half t


private theorem actualShortCutoff_le_exp (t : ℝ) :
    (Nat.sqrt (actualCorrelationCutoff t / 2) : ℝ) ≤
      Real.exp (t / 2 + UniversalSinc.fixedScale) := by
  have hsq : (Nat.sqrt (actualCorrelationCutoff t / 2) : ℝ) ^ 2 ≤
      (actualCorrelationCutoff t : ℝ) := by
    exact_mod_cast (Nat.sqrt_le' (actualCorrelationCutoff t / 2)).trans (Nat.div_le_self _ _)
  have hN : (actualCorrelationCutoff t : ℝ) ≤
      Real.exp (t + 2 * UniversalSinc.fixedScale) :=
    Nat.floor_le (Real.exp_pos _).le
  have he : (Real.exp (t / 2 + UniversalSinc.fixedScale)) ^ 2 =
      Real.exp (t + 2 * UniversalSinc.fixedScale) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp := Real.exp_pos (t / 2 + UniversalSinc.fixedScale)
  nlinarith

/-- The entire normalized short hyperbola term has every fixed exponential
    decay rate. Only the absolute Mobius bound is used; no cancellation is
    assumed. The threshold is chosen before every summation index. -/
theorem actualCorrelationShortTerm_rapid_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)| ≤
        C * Real.exp (-A * t) := by
  let D := 2 * A + 1
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨C, hC, T, hT, hU⟩ := actualCorrelationIntegerDrive_rapid_bound D hD
  refine ⟨C * Real.exp ((D + 1) * UniversalSinc.fixedScale), by positivity,
    2 * (T + UniversalSinc.fixedScale),
    mul_nonneg (by norm_num) (add_nonneg hT UniversalSinc.fixedScale_pos.le), ?_⟩
  intro t ht
  let Y := Nat.sqrt (actualCorrelationCutoff t / 2)
  let B := C * Real.exp (-D * (t / 2 - UniversalSinc.fixedScale))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hY : (Y : ℝ) ≤ Real.exp (t / 2 + UniversalSinc.fixedScale) :=
    actualShortCutoff_le_exp t
  have hterm : ∀ a ∈ Ioc 0 Y,
      |mobiusR a * actualCorrelationLogarithmicTest t a| ≤ B := by
    intro a ha
    have haN : 0 < a := (mem_Ioc.mp ha).1
    have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr haN
    have haY : (a : ℝ) ≤ Y := by exact_mod_cast (mem_Ioc.mp ha).2
    have hlog : Real.log (a : ℝ) ≤ t / 2 + UniversalSinc.fixedScale :=
      (Real.log_le_iff_le_exp haR).mpr (haY.trans hY)
    have harg : T ≤ t - Real.log a := by linarith
    have harg2 : t / 2 - UniversalSinc.fixedScale ≤ t - Real.log a := by linarith
    have hdrive : |actualCorrelationIntegerDrive (t - Real.log a)| ≤ B :=
      (hU _ harg).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left harg2 (neg_nonpos.mpr hD.le))) hC.le)
    have hsqrt : 1 ≤ Real.sqrt (a : ℝ) := by
      simpa using Real.sqrt_le_sqrt (Nat.one_le_cast.mpr haN : (1 : ℝ) ≤ a)
    have htest : |actualCorrelationLogarithmicTest t a| ≤ B := by
      rw [actualCorrelationLogarithmicTest_eq_integerDrive t a haN,
        abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (div_le_self (abs_nonneg _) hsqrt).trans hdrive
    have hmu : |mobiusR a| ≤ 1 := by
      change |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans (by simpa using htest)
  change |∑ a ∈ Ioc 0 Y, mobiusR a * actualCorrelationLogarithmicTest t a| ≤ _
  calc
    _ ≤ ∑ a ∈ Ioc 0 Y, |mobiusR a * actualCorrelationLogarithmicTest t a| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc 0 Y, B := sum_le_sum hterm
    _ = (Y : ℝ) * B := by simp
    _ ≤ Real.exp (t / 2 + UniversalSinc.fixedScale) * B :=
      mul_le_mul_of_nonneg_right hY hB
    _ = C * Real.exp ((D + 1) * UniversalSinc.fixedScale) * Real.exp (-A * t) := by
      dsimp [B]
      calc
        _ = C * Real.exp ((t / 2 + UniversalSinc.fixedScale) -
            D * (t / 2 - UniversalSinc.fixedScale)) := by
          rw [Real.exp_sub]
          simp only [neg_mul, Real.exp_neg, div_eq_mul_inv]
          ring
        _ = _ := by
          rw [show (t / 2 + UniversalSinc.fixedScale) - D * (t / 2 - UniversalSinc.fixedScale) =
            (D + 1) * UniversalSinc.fixedScale + (-A * t) by dsimp [D]; ring]
          rw [Real.exp_add]
          ring



/-- The complete actual prime observable and the complete normalized long
    hyperbola term cancel to every prescribed fixed exponential accuracy.
    This estimates their sum, not either summand separately. -/
theorem actualCorrelationPrimeField_add_longTerm_rapid_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |actualCorrelationPrimeField t +
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)| ≤
        C * Real.exp (-A * t) := by
  obtain ⟨C, hC, T, hT, hE⟩ := actualCorrelationShortTerm_rapid_bound A hA
  refine ⟨2 * C, by positivity, T, hT, ?_⟩
  intro t ht
  have he : actualCorrelationPrimeField t +
      hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) =
      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) := by
    rw [actualCorrelationPrimeField_hyperbola_half]
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (C * Real.exp (-A * t)) := mul_le_mul_of_nonneg_left (hE t ht) (by norm_num)
    _ = _ := by ring



/-! Source-only bounds: every higher prime power is retained; the ordinary-prime
contribution and the complete signed long-term estimate remain open. -/
section ActualSourceBounds
open Set Filter
open scoped Convolution

open CCM

def higherPrimePowerCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

theorem higherPrimePowerCoefficient_nonneg (n : ℕ) :
    0 ≤ higherPrimePowerCoefficient n := by
  unfold higherPrimePowerCoefficient
  split_ifs <;> positivity

theorem higherPrimePowerCoefficient_sum (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, higherPrimePowerCoefficient n) =
      Chebyshev.psi x - Chebyshev.theta x := by
  unfold Chebyshev.psi Chebyshev.theta
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [higherPrimePowerCoefficient, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [higherPrimePowerCoefficient, hp]

theorem actualCorrelationKernel_continuous : Continuous actualCorrelationKernel := by
  have hc := (universalSincKernel_contDiff UniversalSinc.fixedScale_pos).continuous
  have hs0 : NativeComplexSourceSupported UniversalSinc.fixedScale
      (universalSincKernel UniversalSinc.fixedScale) :=
    universalSincKernel_support UniversalSinc.fixedScale_pos
  have hs := hs0.hasCompactSupport
  have h := hs.continuous_convolution_right (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
    hc.locallyIntegrable hc
  have heq : actualCorrelationKernel =
      MeasureTheory.convolution (universalSincKernel UniversalSinc.fixedScale)
        (universalSincKernel UniversalSinc.fixedScale) (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext u
    rfl
  rw [heq]
  exact h

theorem actualCorrelationSource_bounded :
    ∃ M : ℝ, 0 < M ∧ ∀ u, |actualCorrelationSource u| ≤ M := by
  obtain ⟨M, hM⟩ := actualCorrelationKernel_continuous.norm.bddAbove_range_of_hasCompactSupport
    actualCorrelationKernel_supported.hasCompactSupport.norm
  refine ⟨|M| + 1, by positivity, fun u => ?_⟩
  have hMu : ‖actualCorrelationKernel u‖ ≤ M := hM (Set.mem_range_self u)
  exact (Complex.abs_re_le_norm _).trans (hMu.trans (by linarith [le_abs_self M]))

theorem actualCorrelationWeight_uniform_bound (M t : ℝ) (hM : 0 ≤ M)
    (hb : ∀ u, |actualCorrelationSource u| ≤ M) (n : ℕ) (hn : 0 < n) :
    |actualCorrelationWeight t n| ≤
      M * Real.exp ((2 * UniversalSinc.fixedScale - t) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hz : actualCorrelationSource (t - Real.log n) = 0
  · simp only [actualCorrelationWeight, hz, zero_div, abs_zero]
    positivity
  have hkernel : actualCorrelationKernel (t - Real.log n) ≠ 0 := by
    intro h
    apply hz
    simp [actualCorrelationSource, h]
  have hs := actualCorrelationKernel_supported
    (subset_closure (show t - Real.log n ∈ Function.support actualCorrelationKernel from hkernel))
  have hlog : t - 2 * UniversalSinc.fixedScale ≤ Real.log n := by linarith [hs.2]
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.2 hnR)]
  have hexp : Real.exp ((t - 2 * UniversalSinc.fixedScale) / 2) ≤ Real.sqrt n := by
    rw [hsqrt]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    |actualCorrelationWeight t n| = |actualCorrelationSource (t - Real.log n)| / Real.sqrt n := by
      rw [actualCorrelationWeight, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ M / Real.sqrt n := div_le_div_of_nonneg_right (hb _) (Real.sqrt_nonneg _)
    _ ≤ M / Real.exp ((t - 2 * UniversalSinc.fixedScale) / 2) :=
      div_le_div_of_nonneg_left hM (Real.exp_pos _) hexp
    _ = M * Real.exp ((2 * UniversalSinc.fixedScale - t) / 2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

def actualCorrelationHigherPrimePowers (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t),
    higherPrimePowerCoefficient n * actualCorrelationWeight t n

theorem actualCorrelationHigherPrimePowers_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t, |actualCorrelationHigherPrimePowers t| ≤ C := by
  obtain ⟨M, hM, hbound⟩ := actualCorrelationSource_bounded
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K' := |K| + 1
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hcheb (x : ℝ) : Chebyshev.psi x - Chebyshev.theta x ≤ K' * Real.sqrt x :=
    (hK x).trans (mul_le_mul_of_nonneg_right (by dsimp [K']; linarith [le_abs_self K])
      (Real.sqrt_nonneg x))
  refine ⟨M * K' * Real.exp (2 * UniversalSinc.fixedScale), by positivity, fun t => ?_⟩
  let A := M * Real.exp ((2 * UniversalSinc.fixedScale - t) / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    |actualCorrelationHigherPrimePowers t| ≤
        ∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t),
          |higherPrimePowerCoefficient n * actualCorrelationWeight t n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t), higherPrimePowerCoefficient n * A := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (higherPrimePowerCoefficient_nonneg n)]
      exact mul_le_mul_of_nonneg_left
        (actualCorrelationWeight_uniform_bound M t hM.le hbound n (Finset.mem_Ioc.mp hn).1)
        (higherPrimePowerCoefficient_nonneg n)
    _ = A * (Chebyshev.psi (Real.exp (t + 2 * UniversalSinc.fixedScale)) -
        Chebyshev.theta (Real.exp (t + 2 * UniversalSinc.fixedScale))) := by
      rw [← Finset.sum_mul, actualCorrelationCutoff_exact, higherPrimePowerCoefficient_sum]
      ring
    _ ≤ A * (K' * Real.sqrt (Real.exp (t + 2 * UniversalSinc.fixedScale))) :=
      mul_le_mul_of_nonneg_left (hcheb _) hA
    _ = M * K' * Real.exp (2 * UniversalSinc.fixedScale) := by
      have hsqrt : Real.sqrt (Real.exp (t + 2 * UniversalSinc.fixedScale)) =
          Real.exp ((t + 2 * UniversalSinc.fixedScale) / 2) := by
        calc
          _ = Real.exp (Real.log (Real.sqrt (Real.exp (t + 2 * UniversalSinc.fixedScale)))) :=
            (Real.exp_log (Real.sqrt_pos.2 (Real.exp_pos _))).symm
          _ = _ := by rw [Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
      rw [hsqrt]
      dsimp [A]
      calc
        _ = M * K' * (Real.exp ((2 * UniversalSinc.fixedScale - t) / 2) *
            Real.exp ((t + 2 * UniversalSinc.fixedScale) / 2)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem actualCorrelationPrimeField_split_prime_powers (t : ℝ) :
    actualCorrelationPrimeField t =
      (∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t) with n.Prime,
        Real.log n * actualCorrelationWeight t n) + actualCorrelationHigherPrimePowers t := by
  rw [actualCorrelationPrimeField_eq_weighted_vonMangoldt]
  unfold actualCorrelationHigherPrimePowers
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [higherPrimePowerCoefficient, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [higherPrimePowerCoefficient, hp]

open CCM

private theorem actualDensity_compact :
    HasCompactSupport (universalSincSource UniversalSinc.fixedScale) := by
  apply HasCompactSupport.intro (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    isCompact_Icc
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h =>
    hx (universalSincSource_support UniversalSinc.fixedScale_pos h))

theorem actualCorrelationIntegerDrive_hasDerivAt (t : ℝ) :
    HasDerivAt actualCorrelationIntegerDrive
      (∫ x : ℝ, deriv (universalSincSource UniversalSinc.fixedScale) x *
        nativeOriginalIntegerDrive (t - x)) t := by
  have hconv : actualCorrelationIntegerDrive =
      universalSincSource UniversalSinc.fixedScale ⋆[ContinuousLinearMap.mul ℝ ℝ]
        nativeOriginalIntegerDrive := by
    funext u
    exact actualCorrelationIntegerDrive_eq_sourceConvolution u
  rw [hconv]
  exact actualDensity_compact.hasDerivAt_convolution_left _
    ((universalSincSource_contDiff UniversalSinc.fixedScale_pos).of_le (by norm_num))
    nativeOriginalIntegerDrive_continuous.locallyIntegrable t

theorem actualCorrelationIntegerDrive_deriv (t : ℝ) :
    deriv actualCorrelationIntegerDrive t =
      ∫ x : ℝ, deriv (universalSincSource UniversalSinc.fixedScale) x *
        nativeOriginalIntegerDrive (t - x) :=
  (actualCorrelationIntegerDrive_hasDerivAt t).deriv

private theorem actualCompactConvolution_rapid_bound
    (g : ℝ → ℝ) (hg : Continuous g)
    (hsupp : tsupport g ⊆ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |∫ x : ℝ, g x * nativeOriginalIntegerDrive (t - x)| ≤
        C * Real.exp (-A * t) := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)))
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  let V := ∫ x : ℝ, |g x|
  have hV : 0 ≤ V := integral_nonneg (fun _ => abs_nonneg _)
  obtain ⟨C,hC,T,hT,hU⟩ := nativeOriginalIntegerDrive_rapid_bound A hA
  refine ⟨(V + 1) * C * Real.exp (A * UniversalSinc.fixedScale), by positivity,
    T + UniversalSinc.fixedScale, add_nonneg hT UniversalSinc.fixedScale_pos.le, ?_⟩
  intro t ht
  let B := C * Real.exp (A * UniversalSinc.fixedScale) * Real.exp (-A * t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ x : ℝ, |g x * nativeOriginalIntegerDrive (t - x)| ≤ |g x| * B := by
    intro x
    by_cases hx : x ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
    · have htx : T ≤ t - x := by linarith [hx.2]
      have he : Real.exp (-A * (t - x)) ≤
          Real.exp (A * UniversalSinc.fixedScale) * Real.exp (-A * t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hx.2]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |nativeOriginalIntegerDrive (t - x)| ≤ C * Real.exp (-A * (t - x)) := hU _ htx
        _ ≤ B := by
          dsimp [B]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hC.le
    · have hz : g x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
      simp only [hz, zero_mul, abs_zero, le_refl]
  calc
    |∫ x : ℝ, g x * nativeOriginalIntegerDrive (t - x)| ≤
        ∫ x : ℝ, |g x * nativeOriginalIntegerDrive (t - x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, |g x| * B := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun x => abs_nonneg _))
        (hgi.abs.mul_const B) (ae_of_all _ hpoint)
    _ = V * B := by rw [integral_mul_const]
    _ ≤ (V + 1) * B := mul_le_mul_of_nonneg_right (by linarith) hB
    _ = ((V + 1) * C * Real.exp (A * UniversalSinc.fixedScale)) *
        Real.exp (-A * t) := by dsimp [B]; ring

/-- The first derivative of the literal drive has every fixed exponential decay rate.
    Differentiation falls on the fixed compact density; no inverse estimate is used. -/
theorem actualCorrelationIntegerDrive_deriv_rapid_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |deriv actualCorrelationIntegerDrive t| ≤ C * Real.exp (-A * t) := by
  have hq : ContDiff ℝ 1 (universalSincSource UniversalSinc.fixedScale) :=
    (universalSincSource_contDiff UniversalSinc.fixedScale_pos).of_le (by norm_num)
  obtain ⟨C,hC,T,hT,hbound⟩ := actualCompactConvolution_rapid_bound
    (deriv (universalSincSource UniversalSinc.fixedScale))
    (hq.continuous_deriv le_rfl)
    (tsupport_deriv_subset.trans (universalSincSource_support UniversalSinc.fixedScale_pos))
    A hA
  refine ⟨C,hC,T,hT,?_⟩
  intro t ht
  rw [actualCorrelationIntegerDrive_deriv]
  exact hbound t ht

theorem actualFlatMobiusTest_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt actualFlatMobiusTest
      (-(deriv actualCorrelationIntegerDrive (-Real.log r) +
          actualCorrelationIntegerDrive (-Real.log r) / 2) /
        (r * Real.sqrt r)) r := by
  have hU := (actualCorrelationIntegerDrive_hasDerivAt (-Real.log r)).comp r
    (Real.hasDerivAt_log hr.ne').neg
  have hs := Real.hasDerivAt_sqrt hr.ne'
  have h := hU.div hs (Real.sqrt_pos.mpr hr).ne'
  have hformula :
      ((∫ x : ℝ, deriv (universalSincSource UniversalSinc.fixedScale) x *
          nativeOriginalIntegerDrive (-Real.log r - x)) * -(r⁻¹) * Real.sqrt r -
          actualCorrelationIntegerDrive (-Real.log r) * (1 / (2 * Real.sqrt r))) /
        Real.sqrt r ^ 2 =
      -(deriv actualCorrelationIntegerDrive (-Real.log r) +
          actualCorrelationIntegerDrive (-Real.log r) / 2) / (r * Real.sqrt r) := by
    rw [← actualCorrelationIntegerDrive_deriv]
    have hs2 := Real.sq_sqrt hr.le
    field_simp [hr.ne', (Real.sqrt_pos.mpr hr).ne']
    simp only [Real.sq_sqrt hr.le]
    ring
  exact h.congr_deriv hformula

theorem actualFlatMobiusTest_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    actualFlatMobiusTest r = 0 := by
  simp [actualFlatMobiusTest, Real.sqrt_eq_zero_of_nonpos hr]

end ActualSourceBounds


section LiteralSampling
open Set Filter
open scoped Convolution

open CCM

theorem actualCorrelationIntegerDrive_contDiff_one :
    ContDiff ℝ 1 actualCorrelationIntegerDrive := by
  have hq : HasCompactSupport (universalSincSource UniversalSinc.fixedScale) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h =>
        hx (universalSincSource_support UniversalSinc.fixedScale_pos h)))
  have he : actualCorrelationIntegerDrive =
      universalSincSource UniversalSinc.fixedScale ⋆[ContinuousLinearMap.mul ℝ ℝ]
        nativeOriginalIntegerDrive := by
    funext t
    exact actualCorrelationIntegerDrive_eq_sourceConvolution t
  rw [he]
  exact hq.contDiff_convolution_left _
    ((universalSincSource_contDiff UniversalSinc.fixedScale_pos).of_le (by norm_num))
    nativeOriginalIntegerDrive_continuous.locallyIntegrable

private theorem rapid_at_neg_log {g : ℝ → ℝ} {C T r : ℝ}
    (h : ∀ t, T ≤ t → |g t| ≤ C * Real.exp (-(3:ℝ) * t))
    (hr : 0 < r) (hsmall : r ≤ Real.exp (-T)) :
    |g (-Real.log r)| ≤ C * r ^ 3 := by
  have ht : T ≤ -Real.log r := by
    have := Real.log_le_log hr hsmall
    rw [Real.log_exp] at this
    linarith
  have he : Real.exp (-(3:ℝ) * (-Real.log r)) = r ^ 3 := by
    rw [show -(3:ℝ) * (-Real.log r) = (3:ℕ) * Real.log r by ring,
      Real.exp_nat_mul, Real.exp_log hr]
  simpa only [he] using h _ ht

/-- Literal source estimates imply quadratic vanishing and a linearly vanishing
    derivative near the origin. These are fixed-source regularity estimates. -/
theorem actualFlatMobiusTest_origin_bounds :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      |actualFlatMobiusTest r| ≤ C * r ^ 2 ∧
      |deriv actualFlatMobiusTest r| ≤ C * r := by
  obtain ⟨C0,hC0,T0,hT0,h0⟩ := actualCorrelationIntegerDrive_rapid_bound 3 (by norm_num)
  obtain ⟨C1,hC1,T1,hT1,h1⟩ := actualCorrelationIntegerDrive_deriv_rapid_bound 3 (by norm_num)
  refine ⟨C0+C1, min 1 (min (Real.exp (-T0)) (Real.exp (-T1))), by positivity,
    lt_min (by norm_num) (lt_min (Real.exp_pos _) (Real.exp_pos _)), ?_⟩
  intro r hr hδ
  have hr1 : r ≤ 1 := hδ.trans (min_le_left _ _)
  have hr0 : r ≤ Real.exp (-T0) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r ≤ Real.exp (-T1) := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu := rapid_at_neg_log h0 hr hr0
  have hd := rapid_at_neg_log h1 hr hr2
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hrs : r ≤ Real.sqrt r := by
    have hsq := Real.sq_sqrt hr.le
    nlinarith [Real.sqrt_nonneg r]
  constructor
  · rw [actualFlatMobiusTest, abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    calc
      |actualCorrelationIntegerDrive (-Real.log r)| ≤ C0*r^3 := hu
      _ = C0*r^2*r := by ring
      _ ≤ (C0+C1)*r^2*r := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)) hr.le
      _ ≤ (C0+C1)*r^2*Real.sqrt r := mul_le_mul_of_nonneg_left hrs (by positivity)
  · rw [(actualFlatMobiusTest_hasDerivAt hr).deriv, abs_div, abs_neg,
      abs_of_pos (mul_pos hr hs)]
    apply (div_le_iff₀ (mul_pos hr hs)).mpr
    calc
      |deriv actualCorrelationIntegerDrive (-Real.log r) +
          actualCorrelationIntegerDrive (-Real.log r)/2| ≤
          |deriv actualCorrelationIntegerDrive (-Real.log r)| +
            |actualCorrelationIntegerDrive (-Real.log r)|/2 := by
              simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] using
                abs_add_le (deriv actualCorrelationIntegerDrive (-Real.log r))
                  (actualCorrelationIntegerDrive (-Real.log r)/2)
      _ ≤ C1*r^3 + C0*r^3/2 := by linarith
      _ ≤ (C0+C1)*r^3 := by nlinarith [mul_nonneg hC0.le (pow_nonneg hr.le 3)]
      _ = (C0+C1)*r^2*r := by ring
      _ ≤ (C0+C1)*r^2*Real.sqrt r := mul_le_mul_of_nonneg_left hrs (by positivity)
      _ = (C0+C1)*r*(r*Real.sqrt r) := by ring


private theorem actualFlatMobiusTest_hasDerivAt_negative {r : ℝ} (hr : r < 0) :
    HasDerivAt actualFlatMobiusTest 0 r := by
  apply (hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hr] with u hu
  exact actualFlatMobiusTest_zero_of_nonpos hu.le

theorem actualFlatMobiusTest_hasDerivAt_zero :
    HasDerivAt actualFlatMobiusTest 0 0 := by
  obtain ⟨C,δ,hC,hδ,hb⟩ := actualFlatMobiusTest_origin_bounds
  have hz := actualFlatMobiusTest_zero_of_nonpos (le_refl (0:ℝ))
  have hn : ∀ᶠ r : ℝ in 𝓝 0, |r| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (show ∀ᶠ r : ℝ in 𝓝 0, r ∈ Metric.ball (0:ℝ) δ from Metric.ball_mem_nhds 0 hδ)
  have hl : Tendsto (fun r : ℝ => actualFlatMobiusTest r / r) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm' (hn.mono (fun r hr => ?_))
      (show Tendsto (fun r : ℝ => C * |r|) (𝓝 0) (𝓝 0) from by
        simpa using tendsto_const_nhds.mul (continuous_abs.tendsto (0:ℝ)))
    rw [Real.norm_eq_abs]
    by_cases hp : 0 < r
    · have hb0 := (hb r hp (by simpa [abs_of_pos hp] using hr.le)).1
      rw [abs_div, abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      nlinarith
    · rw [actualFlatMobiusTest_zero_of_nonpos (le_of_not_gt hp), zero_div, abs_zero]
      positivity
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, hz, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hl.mono_left nhdsWithin_le_nhds

theorem actualFlatMobiusTest_contDiff_one : ContDiff ℝ 1 actualFlatMobiusTest := by
  have hdiff : Differentiable ℝ actualFlatMobiusTest := by
    intro r
    rcases lt_trichotomy r 0 with hn | hz | hp
    · exact (actualFlatMobiusTest_hasDerivAt_negative hn).differentiableAt
    · subst r; exact actualFlatMobiusTest_hasDerivAt_zero.differentiableAt
    · exact (actualFlatMobiusTest_hasDerivAt hp).differentiableAt
  apply contDiff_one_iff_deriv.mpr
  refine ⟨hdiff, continuous_iff_continuousAt.mpr ?_⟩
  intro r
  rcases lt_trichotomy r 0 with hn | hz | hp
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hn] with u hu
    exact (actualFlatMobiusTest_hasDerivAt_negative hu).deriv
  · subst r
    rw [ContinuousAt, actualFlatMobiusTest_hasDerivAt_zero.deriv]
    obtain ⟨C,δ,hC,hδ,hb⟩ := actualFlatMobiusTest_origin_bounds
    have he : ∀ᶠ r : ℝ in 𝓝 0, |r| < δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (show ∀ᶠ r : ℝ in 𝓝 0, r ∈ Metric.ball (0:ℝ) δ from Metric.ball_mem_nhds 0 hδ)
    apply squeeze_zero_norm' (he.mono (fun r hr => ?_))
      (show Tendsto (fun r : ℝ => C * |r|) (𝓝 0) (𝓝 0) from by
        simpa using tendsto_const_nhds.mul (continuous_abs.tendsto (0:ℝ)))
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy r 0 with hn | hz | hp
    · rw [(actualFlatMobiusTest_hasDerivAt_negative hn).deriv, abs_zero]
      positivity
    · subst r
      simp only [actualFlatMobiusTest_hasDerivAt_zero.deriv, abs_zero, mul_zero, le_refl]
    · simpa only [abs_of_pos hp] using (hb r hp (by simpa [abs_of_pos hp] using hr.le)).2
  · have hl : ContinuousAt (fun u : ℝ => -Real.log u) r := (Real.continuousAt_log hp.ne').neg
    have hc := actualCorrelationIntegerDrive_contDiff_one.continuous
    have hd := actualCorrelationIntegerDrive_contDiff_one.continuous_deriv le_rfl
    have he : ContinuousAt (fun u : ℝ =>
        -(deriv actualCorrelationIntegerDrive (-Real.log u) +
          actualCorrelationIntegerDrive (-Real.log u)/2) / (u * Real.sqrt u)) r :=
      ((hd.continuousAt.comp hl).add ((hc.continuousAt.comp hl).div_const 2)).neg.div
        (continuousAt_id.mul Real.continuous_sqrt.continuousAt) (by positivity)
    apply he.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hp] with u hu
    exact (actualFlatMobiusTest_hasDerivAt hu).deriv


/-- A fixed upper collar sufficient for bounded variation; the exact half-history
    cutoff used elsewhere remains unchanged. -/
theorem actualFlatMobiusTest_zero_above {r : ℝ}
    (hr : Real.exp (2 * UniversalSinc.fixedScale) < r) : actualFlatMobiusTest r = 0 := by
  have ht : -Real.log r + 2 * UniversalSinc.fixedScale < 0 := by
    have h := Real.log_lt_log (Real.exp_pos _) hr
    rw [Real.log_exp] at h
    linarith
  have hf : nativeHistoryCutoff (2 * UniversalSinc.fixedScale) (-Real.log r) = 0 := by
    unfold nativeHistoryCutoff
    exact Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht)
  unfold actualFlatMobiusTest actualCorrelationIntegerDrive
  rw [nativeComplexIntegerDrive_eq_history_sum actualCorrelationKernel_supported le_rfl, hf]
  simp [nativeIntegerDriveCoefficient]

theorem actualFlatMobiusTest_at_upper_collar :
    actualFlatMobiusTest (Real.exp (2 * UniversalSinc.fixedScale)) = 0 := by
  have hf : nativeHistoryCutoff (2 * UniversalSinc.fixedScale)
      (-Real.log (Real.exp (2 * UniversalSinc.fixedScale))) = 1 := by
    simp [nativeHistoryCutoff]
  unfold actualFlatMobiusTest actualCorrelationIntegerDrive
  rw [nativeComplexIntegerDrive_eq_history_sum actualCorrelationKernel_supported le_rfl, hf]
  simp [nativeIntegerDriveCoefficient, Finset.sum_range_succ]

theorem actualFlatMobiusTest_hasCompactSupport : HasCompactSupport actualFlatMobiusTest := by
  apply HasCompactSupport.intro (K := Icc 0 (Real.exp (2 * UniversalSinc.fixedScale))) isCompact_Icc
  intro r hr
  by_cases hn : r ≤ 0
  · exact actualFlatMobiusTest_zero_of_nonpos hn
  · apply actualFlatMobiusTest_zero_above
    by_contra hb
    exact hr ⟨(lt_of_not_ge hn).le, le_of_not_gt hb⟩

open CCM

def actualFlatSamplingMass : ℝ := ∫ r : ℝ, actualFlatMobiusTest r

def actualFlatSamplingSum (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊Real.exp (2 * UniversalSinc.fixedScale) * y⌋₊,
    actualFlatMobiusTest ((n:ℝ)/y)

def actualFlatSamplingRemainder (y : ℝ) : ℝ :=
  actualFlatSamplingSum y - actualFlatSamplingMass * y

private theorem actualFlatMobiusTest_deriv_bounded :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, |deriv actualFlatMobiusTest r| ≤ M := by
  have hc := actualFlatMobiusTest_contDiff_one.continuous_deriv le_rfl
  obtain ⟨M,hM⟩ := actualFlatMobiusTest_hasCompactSupport.deriv.isCompact.bddAbove_image
    hc.abs.continuousOn
  refine ⟨|M|+1, by positivity, ?_⟩
  intro r
  by_cases hr : r ∈ tsupport (deriv actualFlatMobiusTest)
  · exact (hM (mem_image_of_mem _ hr)).trans ((le_abs_self M).trans (by linarith))
  · rw [image_eq_zero_of_notMem_tsupport hr, abs_zero]
    positivity

/-- Uniform source-only bound for the literal integer sampling remainder.
    The mass and scale factors are explicit; no Mobius cancellation is assumed. -/
theorem actualFlatSamplingRemainder_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → |actualFlatSamplingRemainder y| ≤ C := by
  obtain ⟨M,hM,hbound⟩ := actualFlatMobiusTest_deriv_bounded
  let B := Real.exp (2 * UniversalSinc.fixedScale)
  have hB : 0 < B := Real.exp_pos _
  refine ⟨M*B, mul_pos hM hB, ?_⟩
  intro y hy
  let f : ℝ → ℝ := fun z => actualFlatMobiusTest (z/y)
  have hf : ContDiff ℝ 1 f :=
    actualFlatMobiusTest_contDiff_one.comp (contDiff_id.div_const y)
  have hb : 0 ≤ B*y := (mul_pos hB hy).le
  have hfb : f (B*y) = 0 := by
    dsimp [f]
    rw [mul_div_cancel_right₀ B hy.ne']
    exact actualFlatMobiusTest_at_upper_collar
  have houtside : ∀ z : ℝ, z ∉ Ioc 0 (B*y) → f z = 0 := by
    intro z hz
    by_cases hn : z ≤ 0
    · exact actualFlatMobiusTest_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hn hy.le)
    · apply actualFlatMobiusTest_zero_above
      apply (lt_div_iff₀ hy).mpr
      by_contra h
      exact hz ⟨lt_of_not_ge hn,le_of_not_gt h⟩
  have he : (∫ z : ℝ in Ioc 0 (B*y), f z) = actualFlatSamplingMass*y := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
    dsimp [f]
    rw [Measure.integral_comp_div, abs_of_pos hy, smul_eq_mul]
    unfold actualFlatSamplingMass
    ring
  have hd : ∀ z : ℝ, deriv f z = deriv actualFlatMobiusTest (z/y) / y := by
    intro z
    have h := ((actualFlatMobiusTest_contDiff_one.differentiable (by norm_num) (z/y)).hasDerivAt).comp z
      ((hasDerivAt_id z).div_const y)
    simpa only [f, Function.comp_def, id_eq, one_div, mul_one, one_mul, div_eq_mul_inv] using h.deriv
  have hdb : ∀ z : ℝ, |deriv f z| ≤ M/y := by
    intro z
    rw [hd, abs_div, abs_of_pos hy]
    exact div_le_div_of_nonneg_right (hbound _) hy.le
  have hdi : IntegrableOn (fun z => |deriv f z|) (Ioc 0 (B*y)) :=
    ((hf.continuous_deriv le_rfl).abs.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hci : IntegrableOn (fun _ : ℝ => M/y) (Ioc 0 (B*y)) :=
    (continuous_const.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have ha := nativeIntegerAbel_discrepancy_bound hb hf hfb
  rw [he] at ha
  change |actualFlatSamplingRemainder y| ≤ M*B
  calc
    _ ≤ ∫ z : ℝ in Ioc 0 (B*y), |deriv f z| := ha
    _ ≤ ∫ z : ℝ in Ioc 0 (B*y), M/y := integral_mono hdi hci hdb
    _ = M*B := by
      rw [← intervalIntegral.integral_of_le hb, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp

theorem actualFlatSamplingSum_eq_mass_add_remainder (y : ℝ) :
    actualFlatSamplingSum y = actualFlatSamplingMass*y + actualFlatSamplingRemainder y := by
  unfold actualFlatSamplingRemainder
  ring

/-- The diagonal of the genuine-Mobius product kernel is unconditionally O(sqrt x).
    The remaining rank-one plus off-diagonal lower bound is still not supplied. -/
theorem actualFlatSamplingDiagonal_sqrt_bound (T : ℝ) (hT : 0 < T) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 0 < x →
      |aliasDiagonal actualFlatSamplingRemainder x ⌊Real.sqrt (T*x)⌋₊| ≤ D*Real.sqrt x := by
  obtain ⟨C,hC,hR⟩ := actualFlatSamplingRemainder_bounded
  refine ⟨C*Real.sqrt T, by positivity, ?_⟩
  intro x hx
  exact abs_aliasDiagonal_le_sqrt _ hT hx hC.le (fun y hy => hR y ((by positivity : 0 < 1/T).trans_le hy))


/-- The source-coded finite collar retains every nonzero natural-number sample.
    The included zero sample is zero by the literal definition. -/
theorem actualFlatSamplingSum_eq_tsum (y : ℝ) (hy : 0 < y) :
    actualFlatSamplingSum y = ∑' n : ℕ, actualFlatMobiusTest ((n:ℝ)/y) := by
  unfold actualFlatSamplingSum
  symm
  apply tsum_eq_sum
  intro n hn
  have hf : ⌊Real.exp (2 * UniversalSinc.fixedScale)*y⌋₊ < n := by
    simp only [Finset.mem_Icc] at hn
    omega
  exact actualFlatMobiusTest_zero_above ((lt_div_iff₀ hy).mpr (Nat.lt_of_floor_lt hf))

/-- The formerly abstract bounded-remainder premise is discharged for the literal
    fixed source. Neither one-sided lower bound in this equivalence is asserted. -/
theorem actualFlatSampling_eventual_lower_iff (T : ℝ) (hT : 0 < T) :
    HasEventualSqrtLower (fun x =>
      mobiusPoissonQuadratic actualFlatSamplingSum x ⌊Real.sqrt (T*x)⌋₊) ↔
    HasEventualSqrtLower (fun x =>
      mobiusPoissonRankOne actualFlatSamplingMass x ⌊Real.sqrt (T*x)⌋₊ +
      mobiusPoissonOffDiagonal actualFlatSamplingRemainder x ⌊Real.sqrt (T*x)⌋₊) := by
  obtain ⟨C,hC,hR⟩ := actualFlatSamplingRemainder_bounded
  exact eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal
    actualFlatSamplingSum actualFlatSamplingRemainder actualFlatSamplingMass hT hC.le
    actualFlatSamplingSum_eq_mass_add_remainder
    (fun y hy => hR y ((by positivity : 0 < 1/T).trans_le hy))

end LiteralSampling


private theorem sum_eq_of_common_finite_support
    (s u : Finset ℕ) (f : ℕ → ℝ)
    (hs : ∀ n, n ∉ s → f n = 0) (hu : ∀ n, n ∉ u → f n = 0) :
    ∑ n ∈ s, f n = ∑ n ∈ u, f n := by
  have hleft : (∑ n ∈ s, f n) = ∑ n ∈ s ∪ u, f n :=
    Finset.sum_subset Finset.subset_union_left (fun n _ hn => hs n hn)
  have hright : (∑ n ∈ u, f n) = ∑ n ∈ s ∪ u, f n :=
    Finset.sum_subset Finset.subset_union_right (fun n _ hn => hu n hn)
  exact hleft.trans hright.symm

/-- The complete ordinary-integer sampling sum is exactly the finite history
sum. Its zero term and both outer tails vanish for the actual fixed source. -/
theorem actualFlatSamplingSum_eq_hyperbola_history
    (t : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    actualFlatSamplingSum (Real.exp t / ((a : ℝ) * (b : ℝ))) =
      Real.sqrt (Real.exp t) *
        ∑ c ∈ Ioc 0 (actualCorrelationCutoff t / 2),
          actualCorrelationLogarithmicTest t (a * b * c) := by
  let x : ℝ := Real.exp t
  let y : ℝ := x / ((a : ℝ) * (b : ℝ))
  let B : ℝ := Real.exp (2 * CCM.UniversalSinc.fixedScale)
  let M : ℕ := actualCorrelationCutoff t / 2
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hx : 0 < x := Real.exp_pos t
  have hy : 0 < y := div_pos hx (mul_pos haR hbR)
  have hB : 0 < B := Real.exp_pos _
  have harg (c : ℕ) : (c : ℝ) / y = ((a * b * c : ℕ) : ℝ) / Real.exp t := by
    dsimp [y, x]
    simp only [div_div_eq_mul_div, Nat.cast_mul]
    ring
  let f : ℕ → ℝ := fun c => actualFlatMobiusTest ((c : ℝ) / y)
  have hs : ∀ c, c ∉ Icc 0 ⌊B * y⌋₊ → f c = 0 := by
    intro c hc
    have hcN : ⌊B*y⌋₊ < c := by
      simp only [mem_Icc, Nat.zero_le, true_and, not_le] at hc
      exact hc
    have hcR : B*y < (c : ℝ) := (Nat.floor_lt (mul_pos hB hy).le).mp hcN
    apply actualFlatMobiusTest_zero_above
    change B < (c : ℝ) / y
    exact (lt_div_iff₀ hy).mpr hcR
  have hu : ∀ c, c ∉ Ioc 0 M → f c = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · subst c
      simpa only [f, Nat.cast_zero, zero_div] using
        (actualFlatMobiusTest_zero_of_nonpos (le_refl (0 : ℝ)))
    have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
    have hcM : M < c := by
      simp only [mem_Ioc, hcpos, true_and, not_le] at hc
      exact hc
    have hab : 0 < a*b := Nat.mul_pos ha hb
    have hprod : 0 < a*b*c := Nat.mul_pos hab hcpos
    have hlarge : actualCorrelationCutoff t / 2 < a*b*c :=
      hcM.trans_le (Nat.le_mul_of_pos_left c hab)
    dsimp [f]
    rw [harg, ← actualFlatMobiusTest_normalization t (a*b*c) hprod,
      actualCorrelationLogarithmicTest_half_support t _ hlarge, mul_zero]
  have he := sum_eq_of_common_finite_support (Icc 0 ⌊B*y⌋₊) (Ioc 0 M) f hs hu
  change (∑ c ∈ Icc 0 ⌊B*y⌋₊, f c) = _
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hprod : 0 < a*b*c := Nat.mul_pos (Nat.mul_pos ha hb) (mem_Ioc.mp hc).1
  dsimp [f]
  rw [harg, actualFlatMobiusTest_normalization t (a*b*c) hprod]

/-- Exact source-and-normalization adapter. The natural square-root cutoff is
retained literally; no real-floor cutoff identity or arithmetic bound is assumed. -/
theorem actualCorrelationLongTerm_eq_sampling_quadratic (t : ℝ) :
    Real.sqrt (Real.exp t) *
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) =
      mobiusPoissonQuadratic actualFlatSamplingSum (Real.exp t)
        (Nat.sqrt (actualCorrelationCutoff t / 2)) := by
  have hsets (N : ℕ) : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  unfold hyperbolaT mobiusPoissonQuadratic
  simp only [hsets (Nat.sqrt (actualCorrelationCutoff t / 2))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hap : 0 < a := (Finset.mem_Icc.mp ha).1
  have hbp : 0 < b := (Finset.mem_Icc.mp hb).1
  rw [actualFlatSamplingSum_eq_hyperbola_history t a b hap hbp]
  unfold mobiusR
  simp only [ArithmeticFunction.intCoe_apply]
  ring

/-- The literal natural cutoff is bounded directly. No equality between natural
    square roots and a real-floor detector cutoff is assumed. -/
theorem actualCorrelationNativeCutoff_sqrt_bound (t : ℝ) :
    ((Nat.sqrt (actualCorrelationCutoff t / 2) : ℕ) : ℝ) ≤
      Real.sqrt (Real.exp (2 * CCM.UniversalSinc.fixedScale)/2) * Real.sqrt (Real.exp t) := by
  have hsq : (((Nat.sqrt (actualCorrelationCutoff t / 2) : ℕ) : ℝ))^2 ≤
      (((actualCorrelationCutoff t / 2 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (actualCorrelationCutoff t / 2)
  have hdiv : (((actualCorrelationCutoff t / 2 : ℕ)) : ℝ) ≤
      (actualCorrelationCutoff t : ℝ)/2 := by
    simpa only [Nat.cast_ofNat] using (Nat.cast_div_le (m := actualCorrelationCutoff t) (n := 2) :
      (((actualCorrelationCutoff t / 2 : ℕ)) : ℝ) ≤ (actualCorrelationCutoff t : ℝ)/(2:ℕ))
  have hcut : (actualCorrelationCutoff t : ℝ) ≤ Real.exp (t + 2*CCM.UniversalSinc.fixedScale) :=
    Nat.floor_le (Real.exp_pos _).le
  have htotal : (((Nat.sqrt (actualCorrelationCutoff t / 2) : ℕ) : ℝ))^2 ≤
      (Real.exp (2*CCM.UniversalSinc.fixedScale)/2)*Real.exp t := by
    calc
      _ ≤ (((actualCorrelationCutoff t / 2 : ℕ)) : ℝ) := hsq
      _ ≤ (actualCorrelationCutoff t : ℝ)/2 := hdiv
      _ ≤ Real.exp (t + 2*CCM.UniversalSinc.fixedScale)/2 := by linarith
      _ = _ := by rw [Real.exp_add]; ring
  have hroot := Real.sqrt_le_sqrt htotal
  rw [Real.sqrt_sq (Nat.cast_nonneg _), Real.sqrt_mul (by positivity)] at hroot
  exact hroot

/-- Uniform all-time diagonal control at the literal sharpened native cutoff. -/
theorem actualCorrelationNativeDiagonal_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      |aliasDiagonal actualFlatSamplingRemainder (Real.exp t)
        (Nat.sqrt (actualCorrelationCutoff t / 2))| ≤ D*Real.sqrt (Real.exp t) := by
  obtain ⟨C,hC,hR⟩ := actualFlatSamplingRemainder_bounded
  refine ⟨C*Real.sqrt (Real.exp (2*CCM.UniversalSinc.fixedScale)/2), by positivity, ?_⟩
  intro t
  have hcount := abs_aliasDiagonal_le_count actualFlatSamplingRemainder (Real.exp t) C
    (Nat.sqrt (actualCorrelationCutoff t / 2)) hC.le (by
      intro a ha
      have ha0 : (0:ℝ)<a := by exact_mod_cast (mem_Icc.mp ha).1
      exact hR _ (div_pos (Real.exp_pos t) (sq_pos_of_pos ha0)))
  exact hcount.trans (by
    have h := mul_le_mul_of_nonneg_left (actualCorrelationNativeCutoff_sqrt_bound t) hC.le
    simpa only [mul_assoc] using h)

/-- The exact native long term is the normalized complete rank-one/off-diagonal
    expression plus its separately controlled literal diagonal. -/
theorem actualCorrelationLongTerm_eq_normalized_combined (t : ℝ) :
    hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) =
      (mobiusPoissonRankOne actualFlatSamplingMass (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2)) +
        mobiusPoissonOffDiagonal actualFlatSamplingRemainder (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2))) / Real.sqrt (Real.exp t) +
      aliasDiagonal actualFlatSamplingRemainder (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2)) / Real.sqrt (Real.exp t) := by
  have h := actualCorrelationLongTerm_eq_sampling_quadratic t
  rw [mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal
    actualFlatSamplingSum actualFlatSamplingRemainder actualFlatSamplingMass
    (Real.exp t) _ actualFlatSamplingSum_eq_mass_add_remainder] at h
  rw [← add_div]
  apply (eq_div_iff (Real.sqrt_pos.mpr (Real.exp_pos t)).ne').mpr
  simpa only [mul_comm] using h

/-- Exact eventual lower-bound equivalence at the unchanged natural native cutoff.
    Constants precede observation time. Both lower-bound propositions remain OPEN;
    the only discarded term has an unconditional fixed normalized bound. -/
theorem actualCorrelationLongTerm_eventual_lower_iff_combined :
    (∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      -C ≤ hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)) ↔
    (∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      -C ≤ (mobiusPoissonRankOne actualFlatSamplingMass (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2)) +
        mobiusPoissonOffDiagonal actualFlatSamplingRemainder (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2))) / Real.sqrt (Real.exp t)) := by
  obtain ⟨D,hD,hdiag⟩ := actualCorrelationNativeDiagonal_bound
  have hd (t : ℝ) :
      |aliasDiagonal actualFlatSamplingRemainder (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2)) / Real.sqrt (Real.exp t)| ≤ D := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (Real.exp_pos t))]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (Real.exp_pos t))).mpr (hdiag t)
  constructor
  · rintro ⟨C,hC,T0,hbound⟩
    refine ⟨C+D, add_pos hC hD, T0, ?_⟩
    intro t ht
    have h := hbound t ht
    rw [actualCorrelationLongTerm_eq_normalized_combined] at h
    have hu := (abs_le.mp (hd t)).2
    linarith
  · rintro ⟨C,hC,T0,hbound⟩
    refine ⟨C+D, add_pos hC hD, T0, ?_⟩
    intro t ht
    have h := hbound t ht
    rw [actualCorrelationLongTerm_eq_normalized_combined]
    have hl := (abs_le.mp (hd t)).1
    linarith


section ActualPositiveMass
open Set Filter Complex OPICAFollowup
open scoped Convolution

open CCM OPICAFollowup

/-- The actual integer drive's exceptional damping value is its removable
    continuation, not the totalized zeta-prime product at the pole. -/
theorem nativeOriginalIntegerDriveLaplace_half :
    nativeOriginalIntegerDriveLaplace (1/2:ℂ) =
      UniversalSinc.product UniversalSinc.fixedScale (I*(1/2)) := by
  have hevent : nativeOriginalIntegerDriveLaplace =ᶠ[𝓝[≠] (1/2:ℂ)]
      forwardKernelEntireContinuation 0 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (0:ℝ) < (1/2:ℂ).re))] with z hz hpos
    have hz' : z ≠ (1/2:ℂ) := by simpa using hz
    rw [nativeOriginalIntegerDriveLaplace,
      nativeOriginalIntegerDrive_complexLaplace hpos hz',
      forwardKernelEntireContinuation_agrees 0 0 (by simp) hz']
    simp only [forwardKernelTransformGerm, pow_zero, mul_one,
      sourceFamilyLaplace, sourceOrderFamily, nativeOriginalSourceLaplace]
    ring
  have hleft := (nativeOriginalIntegerDriveLaplace_analyticAt
    (by norm_num : (0:ℝ) < (1/2:ℂ).re)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1/2:ℂ) ≤ 𝓝 (1/2:ℂ))
  have hright := (forwardKernelEntireContinuation_analyticAt 0 0 (1/2)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1/2:ℂ) ≤ 𝓝 (1/2:ℂ))
  exact (tendsto_nhds_unique hleft (hright.congr' hevent.symm)).trans
    (forwardKernelEntireContinuation_diagonal_half 0)

open CCM

def actualSourceHalfMass : ℝ :=
  ∫ x : ℝ, Real.exp (-x/2) * universalSincSource UniversalSinc.fixedScale x

theorem actualSourceHalfMass_integrable :
    Integrable (fun x : ℝ => Real.exp (-x/2) *
      universalSincSource UniversalSinc.fixedScale x) := by
  exact ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-x/2))).mul
    (universalSincSource_contDiff UniversalSinc.fixedScale_pos).continuous).integrable_of_hasCompactSupport
      (UniversalSinc.originalDensityCandidate_hasCompactSupport UniversalSinc.fixedScale_pos).mul_left

theorem actualSourceHalfMass_eq_product :
    (actualSourceHalfMass : ℂ) =
      UniversalSinc.product UniversalSinc.fixedScale (I*(1/2)) := by
  rw [← paperFT_universalSincSource UniversalSinc.fixedScale_pos]
  unfold actualSourceHalfMass Zeta23.paperFT
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have he : I*(I*(1/2))*(x:ℂ) = ((-x/2:ℝ):ℂ) := by
    push_cast
    calc
      _ = (I*I)*(x:ℂ)/2 := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [he]
  ring

theorem actualSourceHalfMass_pos : 0 < actualSourceHalfMass := by
  let q := universalSincSource UniversalSinc.fixedScale
  let c := Real.exp (-UniversalSinc.fixedScale/2)
  have hq : Integrable q :=
    UniversalSinc.integrable_originalDensityCandidate UniversalSinc.fixedScale_pos
  have hpoint (x : ℝ) : c * q x ≤ Real.exp (-x/2)*q x := by
    by_cases hx : x ∈ Set.Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
    · apply mul_le_mul_of_nonneg_right _ (universalSincSource_nonneg UniversalSinc.fixedScale_pos x)
      exact Real.exp_le_exp.mpr (by linarith [hx.2])
    · have hz : q x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (universalSincSource_support UniversalSinc.fixedScale_pos h))
      simp [hz]
  have hbound := integral_mono (hq.const_mul c) actualSourceHalfMass_integrable hpoint
  rw [integral_const_mul, universalSincSource_integral_one UniversalSinc.fixedScale_pos,
    mul_one] at hbound
  exact (Real.exp_pos _).trans_le hbound

theorem nativeOriginalIntegerDrive_half_integral :
    (∫ t : ℝ, Real.exp (-t/2)*nativeOriginalIntegerDrive t) = actualSourceHalfMass := by
  have hc : (∫ t : ℝ, Real.exp (-t/2)*nativeOriginalIntegerDrive t : ℝ) =
      nativeOriginalIntegerDriveLaplace (1/2) := by
    rw [← integral_complex_ofReal]
    unfold nativeOriginalIntegerDriveLaplace
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [hc, nativeOriginalIntegerDriveLaplace_half, actualSourceHalfMass_eq_product]

open CCM

theorem actualFlatSamplingMass_eq_dampedDrive :
    actualFlatSamplingMass =
      ∫ t : ℝ, Real.exp (-t/2)*actualCorrelationIntegerDrive t := by
  have himg : (fun t : ℝ => Real.exp (-t)) '' Set.univ = Set.Ioi 0 := by
    ext r
    constructor
    · rintro ⟨t, _, rfl⟩
      exact Real.exp_pos _
    · intro hr
      refine ⟨-Real.log r, Set.mem_univ _, ?_⟩
      simpa using Real.exp_log hr
  have hsub := integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => Real.exp (-t)) (f' := fun t => -Real.exp (-t))
    MeasurableSet.univ
    (fun t _ => (by simpa using ((hasDerivAt_id t).neg.exp)))
    (fun x _ y _ h => neg_injective (Real.exp_injective h)) actualFlatMobiusTest
  rw [himg, Measure.restrict_univ] at hsub
  have hall : (∫ r : ℝ in Set.Ioi 0, actualFlatMobiusTest r) = actualFlatSamplingMass := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    exact actualFlatMobiusTest_zero_of_nonpos (le_of_not_gt hr)
  rw [hall] at hsub
  rw [hsub]
  apply integral_congr_ae
  filter_upwards with t
  have he : Real.exp (-t) = Real.exp (-t/2)*Real.exp (-t/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : Real.sqrt (Real.exp (-t)) = Real.exp (-t/2) := by
    rw [he, Real.sqrt_mul_self (Real.exp_pos _).le]
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul,
    actualFlatMobiusTest, Real.log_exp, neg_neg, hroot]
  rw [he]
  field_simp

theorem actualCorrelationIntegerDrive_half_integral :
    (∫ t : ℝ, Real.exp (-t/2)*actualCorrelationIntegerDrive t) = actualSourceHalfMass^2 := by
  let q : ℝ → ℝ := fun x => Real.exp (-x/2)*universalSincSource UniversalSinc.fixedScale x
  let u : ℝ → ℝ := fun t => Real.exp (-t/2)*nativeOriginalIntegerDrive t
  have huC := nativeCausalComplexDamping_integrable
    (w := (1/2:ℂ)) (by norm_num) nativeOriginalIntegerDrive_integrable
    (fun t ht => nativeOriginalIntegerDrive_zero_of_neg ht)
  have heC : nativeCausalComplexDamping (1/2:ℂ) nativeOriginalIntegerDrive =
      fun t : ℝ => (u t:ℂ) := by
    funext t
    dsimp [nativeCausalComplexDamping,u]
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [heC] at huC
  have hu : Integrable u := by simpa using huC.re
  have hpoint (t : ℝ) : Real.exp (-t/2)*actualCorrelationIntegerDrive t =
      (q ⋆[ContinuousLinearMap.mul ℝ ℝ] u) t := by
    rw [actualCorrelationIntegerDrive_eq_sourceConvolution, ← integral_const_mul,
      convolution_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [ContinuousLinearMap.mul_apply',q,u]
    have he : Real.exp (-t/2) = Real.exp (-x/2)*Real.exp (-(t-x)/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  simp_rw [hpoint]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) actualSourceHalfMass_integrable hu]
  change actualSourceHalfMass * (∫ t : ℝ, Real.exp (-t/2)*nativeOriginalIntegerDrive t) = _
  rw [nativeOriginalIntegerDrive_half_integral, pow_two]

theorem actualFlatSamplingMass_eq_sourceHalfMass_sq :
    actualFlatSamplingMass = actualSourceHalfMass^2 := by
  rw [actualFlatSamplingMass_eq_dampedDrive, actualCorrelationIntegerDrive_half_integral]

theorem actualFlatSamplingMass_pos : 0 < actualFlatSamplingMass := by
  rw [actualFlatSamplingMass_eq_sourceHalfMass_sq]
  exact sq_pos_of_pos actualSourceHalfMass_pos

end ActualPositiveMass

/-! Exact conditional RH consequence. The arithmetic premise remains OPEN. -/
section ConditionalRH
open MeasureTheory Complex Set Filter
open scoped Topology Convolution ComplexConjugate
open CCM ExceptionalZero

private abbrev k : ℝ → ℂ := universalSincKernel UniversalSinc.fixedScale
private theorem k_eq : k = originalSincTest UniversalSinc.fixedScale := rfl
private theorem kc : ContDiff ℝ 2 k :=
  (contDiff_originalSincTest UniversalSinc.fixedScale_pos).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
private theorem ks : HasCompactSupport k :=
  hasCompactSupport_originalSincTest UniversalSinc.fixedScale_pos
private theorem ke (x : ℝ) : k (-x) = k x :=
  originalSincTest_even UniversalSinc.fixedScale_pos x
private theorem kr (x : ℝ) : conj (k x) = k x := by
  change conj (universalSincKernel UniversalSinc.fixedScale x) = universalSincKernel UniversalSinc.fixedScale x
  rw [universalSincKernel_eq_real _ UniversalSinc.fixedScale_pos]
  exact Complex.conj_ofReal _

/-- Literal original pair test, including its exact translation. -/
theorem actualCorrelationKernel_weilTest_translate (t u : ℝ) :
    EF.weilTest (translateRight (universalSincKernel UniversalSinc.fixedScale) t)
      (universalSincKernel UniversalSinc.fixedScale) u = actualCorrelationKernel (u-t) := by
  change EF.weilTest (translateRight k t) k u = actualCorrelationKernel (u-t)
  unfold EF.weilTest EF.tilde translateRight
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_add_right_eq_self
    (fun x : ℝ => k (x-t) * conj (k (-(u-x)))) t]
  unfold actualCorrelationKernel
  apply integral_congr_ae
  filter_upwards with x
  rw [add_sub_cancel_right, kr, ke]
  congr 1
  congr 1
  ring

private theorem Hc : ContDiff ℝ 2 actualCorrelationKernel := by
  have h := EF.weilTest_contDiff kc kc.continuous ks
  have he : EF.weilTest k k = actualCorrelationKernel := by
    funext u
    have htr : translateRight (universalSincKernel UniversalSinc.fixedScale) 0 =
        universalSincKernel UniversalSinc.fixedScale := by
      funext x
      simp [ExceptionalZero.translateRight]
    simpa only [htr,sub_zero] using actualCorrelationKernel_weilTest_translate 0 u
  rwa [he] at h
private theorem He (x : ℝ) : actualCorrelationKernel (-x) = actualCorrelationKernel x := by
  exact convolution_neg_of_neg_eq (L:=ContinuousLinearMap.mul ℝ ℂ)
    (Filter.Eventually.of_forall ke) (Filter.Eventually.of_forall ke)

private theorem Hp : paperFT actualCorrelationKernel (I/2)=0 ∧
    paperFT actualCorrelationKernel (-I/2)=0 := by
  have he : EF.weilTest k k = actualCorrelationKernel := by
    funext u
    have htr : translateRight (universalSincKernel UniversalSinc.fixedScale) 0 =
        universalSincKernel UniversalSinc.fixedScale := by
      funext x
      simp [ExceptionalZero.translateRight]
    simpa only [htr,sub_zero] using actualCorrelationKernel_weilTest_translate 0 u
  rw [← he]
  rw [EF.paperFT_weilTest kc.continuous kc.continuous ks ks,
      EF.paperFT_weilTest kc.continuous kc.continuous ks ks]
  have h := paperFT_originalSincTest_elementary_pair UniversalSinc.fixedScale_pos
  change paperFT k (I/2)=0 ∧ paperFT k (-I/2)=0 at h
  simp only [h.1,h.2,zero_mul,and_self]

def actualCorrelationArch (t : ℝ) : ℝ :=
  ((1/(2*Real.pi):ℂ) * ∫ r : ℝ,
    Complex.exp (I*(r:ℂ)*(t:ℂ)) * paperFT actualCorrelationKernel (r:ℂ) *
      (EF.gammaBracket r:ℂ)).re

/-- The complete original correlation equals its actual archimedean term
    minus both literal prime histories. Neither history is silently dropped. -/
theorem actualCorrelation_explicit_formula (a : ℝ) :
    fixedOriginalSincCorrelationReal a = actualCorrelationArch (2*a) -
      actualCorrelationPrimeField (2*a) - actualCorrelationPrimeField (-(2*a)) := by
  have h := zeta_W_eq_literatureRHS_weilTest
    (contDiff_translateRight kc (2*a)) kc.continuous
    (hasCompactSupport_translateRight ks (2*a)) ks
  have he : EF.weilTest (translateRight k (2*a)) k =
      translateRight actualCorrelationKernel (2*a) := by
    funext u
    exact actualCorrelationKernel_weilTest_translate (2*a) u
  change zetaZeroConfig.W (translateRight k (2*a)) k = _ at h
  rw [he,EF.literatureRHS] at h
  simp only [paperFT_translateRight,Hp.1,Hp.2,mul_zero,zero_add,zero_sub] at h
  have hp : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n:ℝ):ℂ) *
      (translateRight actualCorrelationKernel (2*a) (Real.log n) +
       translateRight actualCorrelationKernel (2*a) (-Real.log n))) =
      nativeComplexPrimeField actualCorrelationKernel (2*a) +
        nativeComplexPrimeField actualCorrelationKernel (-(2*a)) := by
    unfold nativeComplexPrimeField
    rw [← (nativeComplexPrimeField_summable actualCorrelationKernel_supported (t:=2*a)).tsum_add
      (nativeComplexPrimeField_summable actualCorrelationKernel_supported (t:=-(2*a)))]
    apply tsum_congr
    intro n
    unfold translateRight nativePrimeCoefficient
    have he1 : Real.log n - 2*a = -(2*a-Real.log n) := by ring
    have he2 : -Real.log n - 2*a = -(2*a)-Real.log n := by ring
    rw [he1,He,he2,mul_add]
  rw [hp] at h
  have hr := congrArg Complex.re h
  change fixedOriginalSincCorrelationReal a = _ at hr
  simp only [Complex.add_re,Complex.neg_re] at hr
  unfold actualCorrelationArch actualCorrelationPrimeField
  linarith

/-- The fixed-source archimedean correction has one uniform constant,
    independent of every physical translation. -/
theorem actualCorrelationArch_uniform_bound :
    ∃ C : ℝ, 0<C ∧ ∀ t : ℝ, |actualCorrelationArch t| ≤ C := by
  let g : ℝ → ℂ := fun r => paperFT actualCorrelationKernel (r:ℂ)*(EF.gammaBracket r:ℂ)
  have hi : Integrable g := nativeWeilArch_fourier_integrable Hc
    actualCorrelationKernel_supported.hasCompactSupport
  let C : ℝ := ‖(1/(2*Real.pi):ℂ)‖ * ∫ r : ℝ, ‖g r‖
  have hC : 0≤C := mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨C+1,by linarith,?_⟩
  intro t
  have hphase (r : ℝ) : ‖Complex.exp (I*(r:ℂ)*(t:ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp
  have hb : |actualCorrelationArch t|≤C := by
    unfold actualCorrelationArch
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖∫ r : ℝ, Complex.exp (I*(r:ℂ)*(t:ℂ))*paperFT actualCorrelationKernel (r:ℂ)*
          (EF.gammaBracket r:ℂ)‖ ≤
        ∫ r : ℝ, ‖Complex.exp (I*(r:ℂ)*(t:ℂ))*paperFT actualCorrelationKernel (r:ℂ)*
          (EF.gammaBracket r:ℂ)‖ := norm_integral_le_integral_norm _
      _ = ∫ r : ℝ, ‖g r‖ := by
        apply integral_congr_ae
        filter_upwards with r
        rw [mul_assoc,norm_mul,hphase,one_mul]
  linarith

/-- The reflected history vanishes once its complete source support is past. -/
theorem actualCorrelationPrimeField_reflected_zero (t : ℝ)
    (ht : 2*UniversalSinc.fixedScale < t) : actualCorrelationPrimeField (-t)=0 := by
  unfold actualCorrelationPrimeField nativeComplexPrimeField
  have hz : (∑' n : ℕ, (nativePrimeCoefficient n:ℂ)*actualCorrelationKernel (-t-Real.log n))=0 := by
    suffices hh : ∀ n : ℕ, (nativePrimeCoefficient n:ℂ)*actualCorrelationKernel (-t-Real.log n)=0 by
      simp_rw [hh]
      exact tsum_zero
    intro n
    by_cases hn : n=0
    · simp [hn,nativePrimeCoefficient]
    · have hn1 : 1≤n := Nat.one_le_iff_ne_zero.mpr hn
      have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn1)
      have hs : actualCorrelationKernel (-t-Real.log n)=0 :=
        image_eq_zero_of_notMem_tsupport (by
          intro hm
          have hh := (actualCorrelationKernel_supported hm).1
          linarith)
      rw [hs,mul_zero]
  rw [hz]
  rfl

/-- The only unproved premise is the exact eventual arithmetic lower bound. -/
theorem riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower
    (hbound : ∃ C : ℝ, 0<C ∧ ∃ T : ℝ, ∀ t : ℝ, T≤t →
      -C ≤ hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t/2)) :
    RiemannHypothesis := by
  obtain ⟨C,hC,T,hT⟩ := hbound
  obtain ⟨D,hD,S,hS,hsmall⟩ := actualCorrelationPrimeField_add_longTerm_rapid_bound 1 (by norm_num)
  obtain ⟨B,hB,harch⟩ := actualCorrelationArch_uniform_bound
  have hlow (a : ℝ) (ha : max (max T S) (2*UniversalSinc.fixedScale+1)≤2*a) :
      -(B+D+C)≤fixedOriginalSincCorrelationReal a := by
    have ht := (le_max_left T S).trans ((le_max_left (max T S) _).trans ha)
    have hs := (le_max_right T S).trans ((le_max_left (max T S) _).trans ha)
    have hpos : 0≤2*a := hS.trans hs
    have he : Real.exp (-(1:ℝ)*(2*a))≤1 := Real.exp_le_one_iff.mpr (by linarith)
    have he' := mul_le_mul_of_nonneg_left he hD.le
    have hp := (abs_le.mp (hsmall (2*a) hs)).2
    have hb := hT (2*a) ht
    have ha' : 2*UniversalSinc.fixedScale<2*a := by
      have hx := (le_max_right (max T S) _).trans ha
      linarith
    rw [actualCorrelation_explicit_formula,actualCorrelationPrimeField_reflected_zero (2*a) ha']
    have har := (abs_le.mp (harch (2*a))).1
    linarith
  have hline : ∀ ρ : zetaZeroConfig.carrier, (ρ:ℂ).re=1/2 := by
    intro ρ
    by_contra hoff
    have hd : 0 < |(ρ:ℂ).re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    obtain ⟨a,ha,hvalue⟩ :=
      (fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
        ρ hoff hd (max (max T S) (2*UniversalSinc.fixedScale+1)) (B+D+C)).2
    have hApos : 0≤max (max T S) (2*UniversalSinc.fixedScale+1) :=
      (by linarith [UniversalSinc.fixedScale_pos] : 0≤2*UniversalSinc.fixedScale+1).trans (le_max_right _ _)
    have hlo := hlow a (by linarith)
    norm_num at hvalue
    linarith
  intro s hz htriv hs1
  have hm : s∈zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact hline ⟨s,hm⟩

end ConditionalRH

end Zeta23.OPICARound4

