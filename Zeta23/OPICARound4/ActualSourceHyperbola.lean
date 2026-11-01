import Zeta23.OPICARound4.MobiusHyperbola
import Zeta23.CCM.OriginalSincNativeConvolution
import Zeta23.CCM.NativeIntegerDriveFiniteOrderBounds

/-!
# Exact hyperbola decomposition of the literal original correlation source

The source is the unchanged fixed-scale kernel self-convolution. All prime
powers are retained, and its actual compact support supplies the finite cutoff.
This module proves exact source identities and inherited integer-drive bounds.
It supplies no signed inverse estimate and assumes no RH premise.
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


end Zeta23.OPICARound4

