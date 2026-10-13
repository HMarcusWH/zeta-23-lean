import Zeta23.CCM.NativeIntegerPrimeSource
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

/-!
# Actual weighted native fields and their finite local histories

These fields use the unchanged integer lattice and von Mangoldt
coefficients. A compact-source support theorem makes every local sum finite,
before any global norm or Hilbert-space membership is assumed. The source
parameter is explicit: the eventual fixed `j = P² q` binding is not proved
by this module, and neither is the analytic convolution equation `N * X = U`.
-/

noncomputable section

namespace Zeta23.CCM

open Filter Finset
open scoped Topology BigOperators

/-- Exact compact-source support, rather than a numerical tail tolerance. -/
def NativeSourceSupported (s : ℝ) (j : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∉ Set.Icc (-s) s → j x = 0

/-- The native prime-power field; the zero and unit coefficients vanish. -/
def nativePrimeField (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, nativePrimeCoefficient n * j (t - Real.log n)

/-- The native logarithmic integer drive with its actual square-root weight. -/
def nativeIntegerDriveField (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, nativeIntegerDriveCoefficient n * j (t - Real.log n)

/-- The true inclusive entering-integer cutoff on a bounded time history. -/
def nativeHistoryCutoff (s T : ℝ) : ℕ := ⌊Real.exp (T + s)⌋₊

theorem nativeSourceTranslate_zero_above_history {s T t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t ≤ T) {n : ℕ}
    (hn : nativeHistoryCutoff s T < n) : j (t - Real.log n) = 0 := by
  have hexp : Real.exp (T + s) < (n : ℝ) := Nat.lt_of_floor_lt hn
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hexp
  have hlog : T + s < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  apply hj
  intro hmem
  have hlower := hmem.1
  linarith

/-- One finite cutoff works for every time at or before the selected horizon. -/
theorem nativePrimeField_eq_history_sum {s T t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t ≤ T) :
    nativePrimeField j t =
      ∑ n ∈ range (nativeHistoryCutoff s T + 1),
        nativePrimeCoefficient n * j (t - Real.log n) := by
  unfold nativePrimeField
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff s T < n := by
    simp only [mem_range, not_lt] at hn
    omega
  rw [nativeSourceTranslate_zero_above_history hj ht hcut, mul_zero]

theorem nativeIntegerDriveField_eq_history_sum {s T t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t ≤ T) :
    nativeIntegerDriveField j t =
      ∑ n ∈ range (nativeHistoryCutoff s T + 1),
        nativeIntegerDriveCoefficient n * j (t - Real.log n) := by
  unfold nativeIntegerDriveField
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff s T < n := by
    simp only [mem_range, not_lt] at hn
    omega
  rw [nativeSourceTranslate_zero_above_history hj ht hcut, mul_zero]

theorem nativePrimeField_summable {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) :
    Summable (fun n : ℕ => nativePrimeCoefficient n * j (t - Real.log n)) := by
  apply summable_of_ne_finset_zero (s := range (nativeHistoryCutoff s t + 1))
  intro n hn
  have hcut : nativeHistoryCutoff s t < n := by
    simp only [mem_range, not_lt] at hn
    omega
  rw [nativeSourceTranslate_zero_above_history hj le_rfl hcut, mul_zero]

theorem nativeIntegerDriveField_summable {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) :
    Summable (fun n : ℕ => nativeIntegerDriveCoefficient n * j (t - Real.log n)) := by
  apply summable_of_ne_finset_zero (s := range (nativeHistoryCutoff s t + 1))
  intro n hn
  have hcut : nativeHistoryCutoff s t < n := by
    simp only [mem_range, not_lt] at hn
    omega
  rw [nativeSourceTranslate_zero_above_history hj le_rfl hcut, mul_zero]

/-- Compact-source local finiteness permits continuity without any global
integrability assumption on the native output. -/
theorem nativePrimeField_continuous {s : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (hjcont : Continuous j) :
    Continuous (nativePrimeField j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        nativePrimeCoefficient n * j (u - Real.log n)) := by
    fun_prop
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t < t + 1 by linarith)] with u hu
  exact nativePrimeField_eq_history_sum hj hu

theorem nativeIntegerDriveField_continuous {s : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (hjcont : Continuous j) :
    Continuous (nativeIntegerDriveField j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        nativeIntegerDriveCoefficient n * j (u - Real.log n)) := by
    fun_prop
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t < t + 1 by linarith)] with u hu
  exact nativeIntegerDriveField_eq_history_sum hj hu

theorem nativeSourceTranslate_zero_before_firstPrime {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t < Real.log 2 - s) {n : ℕ}
    (hn : 2 ≤ n) : j (t - Real.log n) = 0 := by
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  apply hj
  intro hmem
  have hlower := hmem.1
  linarith

theorem nativePrimeField_zero_before_firstPrime {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t < Real.log 2 - s) :
    nativePrimeField j t = 0 := by
  have hterm : ∀ n : ℕ, nativePrimeCoefficient n * j (t - Real.log n) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [nativeSourceTranslate_zero_before_firstPrime hj ht hn, mul_zero]
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl <;> simp [nativePrimeCoefficient]
  simp only [nativePrimeField, hterm, tsum_zero]

theorem nativeIntegerDriveField_zero_before_firstPrime {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) (ht : t < Real.log 2 - s) :
    nativeIntegerDriveField j t = 0 := by
  have hterm : ∀ n : ℕ, nativeIntegerDriveCoefficient n * j (t - Real.log n) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [nativeSourceTranslate_zero_before_firstPrime hj ht hn, mul_zero]
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl <;> simp [nativeIntegerDriveCoefficient]
  simp only [nativeIntegerDriveField, hterm, tsum_zero]

/-- Before the second distinct integer atom can enter, only the unchanged
prime-two coefficient contributes. No ground or range premise is used. -/
theorem nativePrimeField_eq_firstPrime_atom {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j)
    (hgap : 2 * s < Real.log 3 - Real.log 2)
    (ht : t ≤ Real.log 2 + s) :
    nativePrimeField j t = Real.log 2 / Real.sqrt 2 * j (t - Real.log 2) := by
  have hterm : ∀ n : ℕ, n ≠ 2 → nativePrimeCoefficient n * j (t - Real.log n) = 0 := by
    intro n hn
    by_cases hsmall : n < 2
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl <;> simp [nativePrimeCoefficient]
    · have hn3 : 3 ≤ n := by omega
      have hlog : Real.log 3 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      have hzero : j (t - Real.log n) = 0 := by
        apply hj
        intro hmem
        have hlower := hmem.1
        linarith
      rw [hzero, mul_zero]
  unfold nativePrimeField
  rw [tsum_eq_single 2 hterm]
  unfold nativePrimeCoefficient
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

theorem nativeIntegerDriveField_eq_firstPrime_atom {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j)
    (hgap : 2 * s < Real.log 3 - Real.log 2)
    (ht : t ≤ Real.log 2 + s) :
    nativeIntegerDriveField j t = Real.log 2 / Real.sqrt 2 * j (t - Real.log 2) := by
  have hterm : ∀ n : ℕ, n ≠ 2 → nativeIntegerDriveCoefficient n * j (t - Real.log n) = 0 := by
    intro n hn
    by_cases hsmall : n < 2
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl <;> simp [nativeIntegerDriveCoefficient]
    · have hn3 : 3 ≤ n := by omega
      have hlog : Real.log 3 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      have hzero : j (t - Real.log n) = 0 := by
        apply hj
        intro hmem
        have hlower := hmem.1
        linarith
      rw [hzero, mul_zero]
  unfold nativeIntegerDriveField
  rw [tsum_eq_single 2 hterm]
  simp [nativeIntegerDriveCoefficient]

theorem native_frozenSource_firstPrime_spacing :
    2 * (1 / 4096 : ℝ) < Real.log 3 - Real.log 2 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at hlog
  norm_num at hlog
  linarith

theorem nativePrimeField_frozen_firstPrime_atom {t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported (1 / 4096) j)
    (ht : t ≤ Real.log 2 + 1 / 4096) :
    nativePrimeField j t = Real.log 2 / Real.sqrt 2 * j (t - Real.log 2) :=
  nativePrimeField_eq_firstPrime_atom hj native_frozenSource_firstPrime_spacing ht

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePrimeField_eq_history_sum
#print axioms Zeta23.CCM.nativeIntegerDriveField_eq_history_sum
#print axioms Zeta23.CCM.nativePrimeField_zero_before_firstPrime
#print axioms Zeta23.CCM.nativeIntegerDriveField_zero_before_firstPrime
#print axioms Zeta23.CCM.nativePrimeField_frozen_firstPrime_atom
#print axioms Zeta23.CCM.nativePrimeField_continuous
