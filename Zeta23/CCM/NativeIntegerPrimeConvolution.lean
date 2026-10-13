import Zeta23.CCM.NativeIntegerPrimeField
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The native integer translate action on the actual prime field

The operator below sums actual integer translates. It is not defined using
divisor coefficients merely to make the compatibility equation tautological.
Compact-source local finiteness justifies regrouping its double sum, then
the unchanged weighted divisor identity proves `N * X = U` pointwise.
There is no global integrability, completion, inversion or range assumption.
The fixed-source density and its `j = P²q` identification remain separate.
-/

noncomputable section

namespace Zeta23.CCM

open Filter Finset
open scoped Topology BigOperators

/-- The actual integer translate action with the native square-root weights. -/
def nativeIntegerTranslateAction (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, nativeIntegerCoefficient m * f (t - Real.log m)

/-- A multiplication-indexed source summand used only for regrouping. -/
def nativeIntegerPrimePairTerm (j : ℝ → ℝ) (t : ℝ) (p : ℕ × ℕ) : ℝ :=
  nativeIntegerCoefficient p.1 * nativePrimeCoefficient p.2 *
    j (t - Real.log (p.1 * p.2))

theorem native_frozenSource_causal_gap_pos :
    0 < Real.log 2 - (1 / 4096 : ℝ) := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog
  linarith

/-- The specified source width gives an actual causal history for the prime
field. Causality is established before any Hilbert-space assertion. -/
theorem nativePrimeField_frozen_causal {t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported (1 / 4096) j) (ht : t ≤ 0) :
    nativePrimeField j t = 0 :=
  nativePrimeField_zero_before_firstPrime hj (ht.trans_lt native_frozenSource_causal_gap_pos)

theorem nativeIntegerDriveField_frozen_causal {t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported (1 / 4096) j) (ht : t ≤ 0) :
    nativeIntegerDriveField j t = 0 :=
  nativeIntegerDriveField_zero_before_firstPrime hj (ht.trans_lt native_frozenSource_causal_gap_pos)

theorem nativeIntegerPrimePairTerm_eq_translate (j : ℝ → ℝ) (t : ℝ) (m n : ℕ) :
    nativeIntegerPrimePairTerm j t (m, n) =
      nativeIntegerCoefficient m *
        (nativePrimeCoefficient n * j ((t - Real.log m) - Real.log n)) := by
  by_cases hm : m = 0
  · subst m
    simp [nativeIntegerPrimePairTerm, nativeIntegerCoefficient]
  by_cases hn : n = 0
  · subst n
    simp [nativeIntegerPrimePairTerm, nativePrimeCoefficient]
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have harg : t - Real.log ((m * n : ℕ) : ℝ) =
      (t - Real.log m) - Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hmreal hnreal]
    ring
  simp only [nativeIntegerPrimePairTerm, harg, mul_assoc]

/-- Every nonzero double summand lies in an explicit finite rectangle. -/
theorem nativeIntegerPrimePair_summable {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) : Summable (nativeIntegerPrimePairTerm j t) := by
  apply summable_of_ne_finset_zero
    (s := range (nativeHistoryCutoff s t + 1) ×ˢ range (nativeHistoryCutoff s t + 1))
  rintro ⟨m, n⟩ hnot
  by_cases hm : m = 0
  · subst m
    simp [nativeIntegerPrimePairTerm, nativeIntegerCoefficient]
  by_cases hn : n = 0
  · subst n
    simp [nativeIntegerPrimePairTerm, nativePrimeCoefficient]
  have hprod : nativeHistoryCutoff s t < m * n := by
    simp only [mem_product, mem_range, not_and_or, not_lt] at hnot
    rcases hnot with hmcut | hncut
    · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hn))
    · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm))
  unfold nativeIntegerPrimePairTerm
  rw [nativeSourceTranslate_zero_above_history hj le_rfl hprod, mul_zero]

/-- Each multiplication fiber gives the actual logarithmic integer-drive
coefficient. The infinite zero fiber is handled by its zero weights. -/
theorem nativeIntegerPrimePair_fiber (j : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n},
      nativeIntegerPrimePairTerm j t p.val) =
        nativeIntegerDriveCoefficient n * j (t - Real.log n) := by
  by_cases hn : n = 0
  · subst n
    have hpzero : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
        nativeIntegerPrimePairTerm j t p.val = 0 := by
      rintro ⟨⟨m, d⟩, hp⟩
      have hmd : m * d = 0 := by simpa using hp
      rcases Nat.mul_eq_zero.mp hmd with hm | hd
      · subst m
        simp [nativeIntegerPrimePairTerm, nativeIntegerCoefficient]
      · subst d
        simp [nativeIntegerPrimePairTerm, nativePrimeCoefficient]
    simp [hpzero, nativeIntegerDriveCoefficient]
  rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by
    ext p
    simp [hn]]
  rw [Finset.tsum_subtype' n.divisorsAntidiagonal (nativeIntegerPrimePairTerm j t)]
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (nativeIntegerCoefficient p.1 * nativePrimeCoefficient p.2) *
          j (t - Real.log n) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold nativeIntegerPrimePairTerm
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ n.divisorsAntidiagonal,
        nativeIntegerCoefficient p.1 * nativePrimeCoefficient p.2) *
          j (t - Real.log n) := by rw [Finset.sum_mul]
    _ = nativeIntegerDriveCoefficient n * j (t - Real.log n) := by
      rw [Nat.sum_divisorsAntidiagonal', native_weighted_dirichlet_identity]

theorem nativeIntegerPrime_inner_sum (j : ℝ → ℝ) (t : ℝ) (m : ℕ) :
    (∑' n : ℕ, nativeIntegerPrimePairTerm j t (m, n)) =
      nativeIntegerCoefficient m * nativePrimeField j (t - Real.log m) := by
  simp_rw [nativeIntegerPrimePairTerm_eq_translate]
  rw [tsum_mul_left]
  rfl

/-- The actual outer integer action is summable for the compact prime source,
without assuming that its inverse output belongs to a damped Hilbert space. -/
theorem nativeIntegerTranslateAction_summable_primeField {s t : ℝ} {j : ℝ → ℝ}
    (hj : NativeSourceSupported s j) :
    Summable (fun m : ℕ =>
      nativeIntegerCoefficient m * nativePrimeField j (t - Real.log m)) := by
  have hsum := (nativeIntegerPrimePair_summable hj (t := t)).prod
  exact hsum.congr (nativeIntegerPrime_inner_sum j t)

/-- Exact local native compatibility, proved from unchanged integer translates
and the full weighted divisor law. This is the pointwise equation `N*X=U`. -/
theorem nativeIntegerTranslateAction_primeField_eq_integerDriveField
    {s : ℝ} {j : ℝ → ℝ} (hj : NativeSourceSupported s j) (t : ℝ) :
    nativeIntegerTranslateAction (nativePrimeField j) t = nativeIntegerDriveField j t := by
  have hpair := nativeIntegerPrimePair_summable hj (t := t)
  calc
    nativeIntegerTranslateAction (nativePrimeField j) t =
        ∑' m : ℕ, ∑' n : ℕ, nativeIntegerPrimePairTerm j t (m, n) := by
      unfold nativeIntegerTranslateAction
      apply tsum_congr
      intro m
      exact (nativeIntegerPrime_inner_sum j t m).symm
    _ = ∑' p : ℕ × ℕ, nativeIntegerPrimePairTerm j t p := hpair.tsum_prod.symm
    _ = ∑' n : ℕ, nativeIntegerDriveCoefficient n * j (t - Real.log n) := by
      have hfiber := hpair.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
      have hdrive : HasSum
          (fun n : ℕ => nativeIntegerDriveCoefficient n * j (t - Real.log n))
          (∑' p : ℕ × ℕ, nativeIntegerPrimePairTerm j t p) := by
        simpa only [nativeIntegerPrimePair_fiber] using hfiber
      exact hdrive.tsum_eq.symm
    _ = nativeIntegerDriveField j t := rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerPrimePair_fiber
#print axioms Zeta23.CCM.nativeIntegerTranslateAction_summable_primeField
#print axioms Zeta23.CCM.nativeIntegerTranslateAction_primeField_eq_integerDriveField
#print axioms Zeta23.CCM.nativePrimeField_frozen_causal
