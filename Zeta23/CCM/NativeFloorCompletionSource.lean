import Zeta23.CCM.NativeIntegerPrimeConvolution
import Zeta23.CCM.NativePositiveCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The floor completion is the actual integer action on its causal kernel

The rational causal kernel is defined explicitly. Its weighted integer
translates have a finite inclusive floor cutoff at every time, and sum to
the previously defined native positive floor completion. This identification
does not establish a Laplace formula, a strict mass bound, a completed-source
equation, an inverse, or global Hilbert-space membership of an output.
-/

noncomputable section

namespace Zeta23.CCM

open Filter Finset
open scoped Topology BigOperators

/-- The original endpoint completion kernel `c(t)` with its causal convention. -/
def nativeRationalCausalKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then -Real.exp (-(t / 2)) + 2 * Real.exp (-(3 * t / 2)) else 0

theorem nativeRationalCausalKernel_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativeRationalCausalKernel t = 0 := by
  simp [nativeRationalCausalKernel, not_le.mpr ht]

theorem nativeRationalCausalKernel_zero : nativeRationalCausalKernel 0 = 1 := by
  norm_num [nativeRationalCausalKernel]

/-- Actual integer action is locally finite despite the kernel's infinite
right tail: causality supplies the cutoff instead of compact support. -/
theorem nativeRationalCausalKernel_integerAction_eq_sum (t : ℝ) :
    nativeIntegerTranslateAction nativeRationalCausalKernel t =
      ∑ n ∈ range (⌊Real.exp t⌋₊ + 1),
        nativeIntegerCoefficient n * nativeRationalCausalKernel (t - Real.log n) := by
  unfold nativeIntegerTranslateAction
  apply tsum_eq_sum
  intro n hn
  have hcut : ⌊Real.exp t⌋₊ < n := by
    simp only [mem_range, not_lt] at hn
    omega
  have hexp : Real.exp t < (n : ℝ) := Nat.lt_of_floor_lt hcut
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hexp
  have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  rw [nativeRationalCausalKernel_zero_of_neg (by linarith), mul_zero]

theorem nativeRationalCausalKernel_integerAction_summable (t : ℝ) :
    Summable (fun n : ℕ => nativeIntegerCoefficient n *
      nativeRationalCausalKernel (t - Real.log n)) := by
  apply summable_of_ne_finset_zero (s := range (⌊Real.exp t⌋₊ + 1))
  intro n hn
  have hcut : ⌊Real.exp t⌋₊ < n := by
    simp only [mem_range, not_lt] at hn
    omega
  have hexp : Real.exp t < (n : ℝ) := Nat.lt_of_floor_lt hcut
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hexp
  have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  rw [nativeRationalCausalKernel_zero_of_neg (by linarith), mul_zero]

/-- The square-root weights are paid using the actual exponential/log identities. -/
theorem nativeRationalCausalKernel_weighted_atom {t : ℝ} {n : ℕ}
    (hn : 0 < n) (hactive : Real.log (n : ℝ) ≤ t) :
    nativeIntegerCoefficient n * nativeRationalCausalKernel (t - Real.log n) =
      -Real.exp (-(t / 2)) + 2 * Real.exp (-(3 * t / 2)) * (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnreal)
  have hehalf : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnreal]
    congr 1
    ring
  have hethree : Real.exp (3 * Real.log (n : ℝ) / 2) =
      (n : ℝ) * Real.sqrt n := by
    rw [show 3 * Real.log (n : ℝ) / 2 = Real.log (n : ℝ) + Real.log (n : ℝ) / 2 by ring,
      Real.exp_add, Real.exp_log hnreal, hehalf]
  have hfirst : Real.exp (-((t - Real.log n) / 2)) =
      Real.exp (-(t / 2)) * Real.sqrt n := by
    rw [show -((t - Real.log n) / 2) = -(t / 2) + Real.log n / 2 by ring,
      Real.exp_add, hehalf]
  have hsecond : Real.exp (-(3 * (t - Real.log n) / 2)) =
      Real.exp (-(3 * t / 2)) * ((n : ℝ) * Real.sqrt n) := by
    rw [show -(3 * (t - Real.log n) / 2) = -(3 * t / 2) + 3 * Real.log n / 2 by ring,
      Real.exp_add, hethree]
  unfold nativeIntegerCoefficient nativeRationalCausalKernel
  rw [if_pos (sub_nonneg.mpr hactive), hfirst, hsecond]
  field_simp

private theorem native_sum_range_shifted_natCast (N : ℕ) :
    (∑ n ∈ range N, ((n : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The completion really equals `c*N`, including each entering-integer seam. -/
theorem nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion (t : ℝ) :
    nativeIntegerTranslateAction nativeRationalCausalKernel t = nativePositiveCompletion t := by
  by_cases ht : 0 ≤ t
  · rw [nativeRationalCausalKernel_integerAction_eq_sum]
    rw [sum_range_succ']
    have hzero : nativeIntegerCoefficient 0 *
        nativeRationalCausalKernel (t - Real.log ((0 : ℕ) : ℝ)) = 0 := by
      simp [nativeIntegerCoefficient]
    rw [hzero, add_zero]
    have hatoms :
        (∑ n ∈ range ⌊Real.exp t⌋₊,
          nativeIntegerCoefficient (n + 1) *
            nativeRationalCausalKernel (t - Real.log (n + 1))) =
        ∑ n ∈ range ⌊Real.exp t⌋₊,
          (-Real.exp (-(t / 2)) +
            2 * Real.exp (-(3 * t / 2)) * ((n : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n + 1 ≤ ⌊Real.exp t⌋₊ := Nat.succ_le_of_lt (mem_range.mp hn)
      have hle : ((n + 1 : ℕ) : ℝ) ≤ Real.exp t := by
        have hcast : ((n + 1 : ℕ) : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by
          exact_mod_cast hnle
        exact hcast.trans (Nat.floor_le (Real.exp_pos t).le)
      have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤ t :=
        (Real.log_le_iff_le_exp hnpos).mpr hle
      simpa only [Nat.cast_add, Nat.cast_one] using
        nativeRationalCausalKernel_weighted_atom (Nat.succ_pos n) hlog
    rw [hatoms]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range,
      nsmul_eq_mul, native_sum_range_shifted_natCast]
    have hepoch : Real.exp (-(t / 2)) = Real.exp (-(3 * t / 2)) * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hepoch]
    unfold nativePositiveCompletion
    rw [if_pos ht]
    ring
  · have htneg : t < 0 := lt_of_not_ge ht
    have hfloor : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr htneg)
    rw [nativeRationalCausalKernel_integerAction_eq_sum,
      nativePositiveCompletion_eq_zero_of_neg htneg]
    simp [hfloor, nativeIntegerCoefficient]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeRationalCausalKernel_weighted_atom
#print axioms Zeta23.CCM.nativeRationalCausalKernel_integerAction_summable
#print axioms Zeta23.CCM.nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion
