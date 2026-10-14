import Zeta23.CCM.NativeCompletionIntegerKernel

/-!
# The actual causal completion equation before prime-field L2 membership

Finite histories on each causal time interval justify every interchange.
The prime field is used only as its literal continuous causal function.
Consequently a * X = c * U is established before, and independently of,
any global square-integrability or range assertion about X.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped BigOperators

namespace Zeta23.CCM

private theorem causal_product_integrable {g f : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ s : ℝ, s < 0 → g s = 0)
    (hf : Continuous f) (hf0 : ∀ s : ℝ, s < 0 → f s = 0) (t : ℝ) :
    Integrable (fun s : ℝ => g s * f (t - s)) := by
  have hc : Continuous (fun s : ℝ => f (t - s)) :=
    hf.comp (continuous_const.sub continuous_id)
  have hi : IntegrableOn (fun s : ℝ => g s * f (t - s)) (Icc 0 t) :=
    hg.integrableOn.mul_continuousOn hc.continuousOn isCompact_Icc
  apply (hi.integrable_indicator measurableSet_Icc).congr
  filter_upwards with s
  by_cases hs : s ∈ Icc 0 t
  · simp only [indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hcases : s < 0 ∨ t < s := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hs
    rcases hcases with hneg | hafter
    · rw [hg0 s hneg, zero_mul]
    · rw [hf0 _ (by linarith), mul_zero]

/-- A local finite Fubini theorem for the unchanged integer translates.
The right factor has no global integrability hypothesis. -/
theorem nativeIntegerTranslate_causal_convolution_comm {g f : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ s : ℝ, s < 0 → g s = 0)
    (hf : Continuous f) (hf0 : ∀ s : ℝ, s < 0 → f s = 0) (t : ℝ) :
    (∫ s : ℝ, nativeIntegerTranslateAction g s * f (t - s)) =
      ∫ s : ℝ, g s * nativeIntegerTranslateAction f (t - s) := by
  let history := range (⌊Real.exp t⌋₊ + 1)
  have hleft : (fun s : ℝ => nativeIntegerTranslateAction g s * f (t - s)) =
      fun s => ∑ n ∈ history,
        nativeIntegerCoefficient n * g (s - Real.log n) * f (t - s) := by
    funext s
    by_cases hs : s ≤ t
    · rw [nativeIntegerTranslateAction_eq_causal_history_at_horizon hg0 hs, Finset.sum_mul]
    · rw [hf0 _ (by linarith), mul_zero]
      simp only [mul_zero, sum_const_zero]
  have hright : (fun s : ℝ => g s * nativeIntegerTranslateAction f (t - s)) =
      fun s => ∑ n ∈ history,
        nativeIntegerCoefficient n * (g s * f ((t - Real.log n) - s)) := by
    funext s
    by_cases hs : s < 0
    · rw [hg0 s hs, zero_mul]
      simp only [zero_mul, mul_zero, sum_const_zero]
    · rw [nativeIntegerTranslateAction_eq_causal_history_at_horizon hf0
        (show t - s ≤ t by linarith [le_of_not_gt hs]), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [show (t - s) - Real.log n = (t - Real.log n) - s by ring]
      ring
  have hleftInt (n : ℕ) : Integrable (fun s : ℝ =>
      nativeIntegerCoefficient n * g (s - Real.log n) * f (t - s)) := by
    by_cases hn : n = 0
    · simp [hn, nativeIntegerCoefficient]
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hgshift : Integrable (fun s : ℝ => g (s - Real.log n)) :=
      hg.comp_sub_right (Real.log n)
    have hgc : ∀ s : ℝ, s < 0 → g (s - Real.log n) = 0 := by
      intro s hs
      exact hg0 _ (by linarith)
    simpa only [mul_assoc] using
      (causal_product_integrable hgshift hgc hf hf0 t).const_mul (nativeIntegerCoefficient n)
  have hrightInt (n : ℕ) : Integrable (fun s : ℝ =>
      nativeIntegerCoefficient n * (g s * f ((t - Real.log n) - s))) :=
    (causal_product_integrable hg hg0 hf hf0 (t - Real.log n)).const_mul
      (nativeIntegerCoefficient n)
  rw [hleft, hright, integral_finsetSum _ (fun n _ => hleftInt n),
    integral_finsetSum _ (fun n _ => hrightInt n)]
  apply Finset.sum_congr rfl
  intro n _
  have hfactor : (fun s : ℝ => nativeIntegerCoefficient n * g (s - Real.log n) * f (t - s)) =
      fun s => nativeIntegerCoefficient n * (g (s - Real.log n) * f (t - s)) := by
    funext s
    ring
  rw [hfactor, integral_const_mul, integral_const_mul]
  congr 1
  have hshift : (fun s : ℝ => g (s - Real.log n) * f (t - s)) =
      fun s => (fun u : ℝ => g u * f ((t - Real.log n) - u)) (s - Real.log n) := by
    funext s
    congr 2
    ring
  rw [hshift]
  exact integral_sub_right_eq_self
    (fun u : ℝ => g u * f ((t - Real.log n) - u)) (Real.log n) (μ := (volume : Measure ℝ))

theorem nativeOriginalPrimeField_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativeOriginalPrimeField t = 0 :=
  nativePrimeField_frozen_causal nativeOriginalSource_supported ht.le

/-- The actual equation, established as an equality of literal pointwise
integrals before placing the prime field in any Hilbert space. -/
theorem nativeCompletedInput_equation (t : ℝ) :
    (∫ s : ℝ, nativePositiveCompletion s * nativeOriginalPrimeField (t - s)) =
      nativeCompletedInput t := by
  simp_rw [nativePositiveCompletion_eq_integerTranslateCorrection]
  rw [nativeIntegerTranslate_causal_convolution_comm nativeCompletionCorrection_integrable
    (fun _ hs => nativeCompletionCorrection_zero_of_neg hs)
    nativeOriginalPrimeField_continuous (fun _ hs => nativeOriginalPrimeField_zero_of_neg hs)]
  unfold nativeCompletedInput
  apply integral_congr_ae
  filter_upwards with s
  rw [show nativeIntegerTranslateAction nativeOriginalPrimeField (t - s) =
      nativeOriginalIntegerDrive (t - s) from
        nativeIntegerTranslateAction_primeField_eq_integerDriveField
          nativeOriginalSource_supported (t - s)]

theorem nativeCompletedInput_equation_integrable (t : ℝ) :
    Integrable (fun s : ℝ => nativePositiveCompletion s * nativeOriginalPrimeField (t - s)) :=
  causal_product_integrable nativePositiveCompletion_integrable
    (fun _ hs => nativePositiveCompletion_eq_zero_of_neg hs)
    nativeOriginalPrimeField_continuous (fun _ hs => nativeOriginalPrimeField_zero_of_neg hs) t

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerTranslate_causal_convolution_comm
#print axioms Zeta23.CCM.nativeOriginalPrimeField_zero_of_neg
#print axioms Zeta23.CCM.nativeCompletedInput_equation
#print axioms Zeta23.CCM.nativeCompletedInput_equation_integrable
