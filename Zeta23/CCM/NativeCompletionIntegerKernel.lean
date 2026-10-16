import Zeta23.CCM.NativeCompletedInput
import Zeta23.CCM.NativeFloorCompletionSource

/-!
# The literal floor kernel is the integer completion of c

The inclusive floor convention is derived by summing the actual signed
causal correction kernel with the unchanged square-root integer weights.
This is a pointwise kernel identity, before any convolution with X or any
global Hilbert-space assumption on X.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped BigOperators

namespace Zeta23.CCM

/-- The completed input uses exactly the previously constructed native
rational kernel, so its existing multiplier calculation applies directly. -/
theorem nativeCompletionCorrection_eq_rationalKernel :
    nativeCompletionCorrection = nativeRationalCausalKernel := rfl

theorem nativeIntegerTranslateAction_eq_causal_history_at_horizon {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, t < 0 → f t = 0) {t T : ℝ} (ht : t ≤ T) :
    nativeIntegerTranslateAction f t =
      ∑ n ∈ range (⌊Real.exp T⌋₊ + 1), nativeIntegerCoefficient n * f (t - Real.log n) := by
  unfold nativeIntegerTranslateAction
  apply tsum_eq_sum
  intro n hn
  have hnlarge : ⌊Real.exp T⌋₊ < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  have hnreal : Real.exp T < (n : ℝ) := Nat.lt_of_floor_lt hnlarge
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos T).trans hnreal
  have hlog : T < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hnreal
  rw [hf _ (by linarith), mul_zero]

theorem nativeIntegerTranslateAction_eq_causal_history {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, t < 0 → f t = 0) (t : ℝ) :
    nativeIntegerTranslateAction f t =
      ∑ n ∈ range (⌊Real.exp t⌋₊ + 1), nativeIntegerCoefficient n * f (t - Real.log n) :=
  nativeIntegerTranslateAction_eq_causal_history_at_horizon hf le_rfl

theorem nativeCompletionCorrection_integer_term {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (hlog : Real.log n ≤ t) :
    nativeIntegerCoefficient n * nativeCompletionCorrection (t - Real.log n) =
      -Real.exp (-(t / 2)) + 2 * (n : ℝ) * Real.exp (-(3 * t / 2)) := by
  rw [nativeCompletionCorrection_eq_rationalKernel]
  convert nativeRationalCausalKernel_weighted_atom (Nat.pos_of_ne_zero hn) hlog using 1 <;> ring

theorem nativeCompletionCorrection_integer_sum_eq (t : ℝ) :
    nativeIntegerTranslateAction nativeCompletionCorrection t =
      -(⌊Real.exp t⌋₊ : ℝ) * Real.exp (-(t / 2)) +
        (⌊Real.exp t⌋₊ : ℝ) * ((⌊Real.exp t⌋₊ : ℝ) + 1) * Real.exp (-(3 * t / 2)) := by
  rw [nativeCompletionCorrection_eq_rationalKernel,
    nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion]
  by_cases ht : 0 ≤ t
  · rw [nativePositiveCompletion, if_pos ht]
    have hE : Real.exp (-(t / 2)) = Real.exp (-(3 * t / 2)) * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hE]
    ring
  · have hfloor : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (lt_of_not_ge ht))
    rw [nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht), hfloor]
    norm_num

/-- Exact actual a = c * N, including every entering-integer seam. The
identity reuses the prior literal-kernel construction rather than proving
the same floor-sum algebra independently a second time. -/
theorem nativePositiveCompletion_eq_integerTranslateCorrection (t : ℝ) :
    nativePositiveCompletion t = nativeIntegerTranslateAction nativeCompletionCorrection t := by
  rw [nativeCompletionCorrection_eq_rationalKernel]
  exact (nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion t).symm

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerTranslateAction_eq_causal_history
#print axioms Zeta23.CCM.nativeCompletionCorrection_eq_rationalKernel
#print axioms Zeta23.CCM.nativeCompletionCorrection_integer_term
#print axioms Zeta23.CCM.nativePositiveCompletion_eq_integerTranslateCorrection
