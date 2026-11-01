import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Exact finite arithmetic only. No estimate for the actual source is assumed or proved. -/
noncomputable section
open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Zeta23.OPICARound4

def mobiusR : ArithmeticFunction ℝ := ArithmeticFunction.moebius

theorem arithmetic_sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f - g) n = f n - g n := rfl

theorem weighted_convolution (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, (f * g) n * w n) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, f a * g b * w (a * b) := by
  simp only [ArithmeticFunction.mul_apply, sum_mul]
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n,
    f x.1 * g x.2 * w n
  · refine sum_congr rfl fun n hn => ?_
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (mem_Ioc.mp hn).1.ne'
      (mem_Ioc.mp hn).2]
  · simp_rw [sum_filter]
    rw [sum_comm, sum_product]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    have hab : 0 < a * b := Nat.mul_pos (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
    by_cases hN : a * b ≤ N
    · simp [sum_ite_eq, mem_Ioc, hab, hN]
    · have hz : w (a * b) = 0 := hw _ (Nat.lt_of_not_ge hN)
      simp [sum_ite_eq, mem_Ioc, hab, hN, hz]

theorem weighted_mobius_inverse (w : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ b ∈ Ioc 0 N, ∑ c ∈ Ioc 0 N, (mobiusR b) * w (b * c)) = w 1 := by
  have h := weighted_convolution mobiusR (ArithmeticFunction.zeta : ArithmeticFunction ℝ) w N hw
  have hmu : mobiusR * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  rw [hmu] at h
  simp only [ArithmeticFunction.one_apply, ite_mul, one_mul, zero_mul] at h
  have hz : ∀ c ∈ Ioc 0 N, (ArithmeticFunction.zeta : ArithmeticFunction ℝ) c = 1 := by
    intro c hc
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, (mem_Ioc.mp hc).1.ne']
  have hmem : 1 ∈ Ioc 0 N := mem_Ioc.mpr ⟨Nat.zero_lt_one, hN⟩
  calc
    _ = ∑ b ∈ Ioc 0 N, ∑ c ∈ Ioc 0 N,
        mobiusR b * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) c * w (b * c) := by
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      rw [hz c hc, mul_one]
    _ = w 1 := by simpa only [sum_ite_eq', if_pos hmem] using h.symm

def arithmeticTruncation (f : ArithmeticFunction ℝ) (Y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ Y then f n else 0, by simp⟩

theorem arithmeticTruncation_apply (f : ArithmeticFunction ℝ) (Y n : ℕ) :
    arithmeticTruncation f Y n = if n ≤ Y then f n else 0 := rfl

theorem arithmeticTruncation_sum (f : ArithmeticFunction ℝ) (w : ℕ → ℝ)
    (Y N : ℕ) (hYN : Y ≤ N) :
    (∑ n ∈ Ioc 0 N, arithmeticTruncation f Y n * w n) =
      ∑ n ∈ Ioc 0 Y, f n * w n := by
  calc
    _ = ∑ n ∈ Ioc 0 Y, arithmeticTruncation f Y n * w n := by
      symm
      apply sum_subset (Ioc_subset_Ioc le_rfl hYN)
      intro n hn hnY
      have hnlt : Y < n := by
        by_contra h
        exact hnY (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, Nat.le_of_not_gt h⟩)
      simp [arithmeticTruncation_apply, Nat.not_le.mpr hnlt]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [arithmeticTruncation_apply, if_pos (mem_Ioc.mp hn).2]

theorem tail_square_vanishes (f : ArithmeticFunction ℝ) (N n : ℕ) (hn : n ≤ N) :
    ((f - arithmeticTruncation f (Nat.sqrt N)) *
      (f - arithmeticTruncation f (Nat.sqrt N))) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases h₁ : p.1 ≤ Nat.sqrt N
  · simp [arithmetic_sub_apply, arithmeticTruncation_apply, h₁]
  by_cases h₂ : p.2 ≤ Nat.sqrt N
  · simp [arithmetic_sub_apply, arithmeticTruncation_apply, h₂]
  have hprod : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ n := by
    rw [← hp'.1]
    exact Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.lt_of_not_ge h₁))
      (Nat.succ_le_of_lt (Nat.lt_of_not_ge h₂))
  exact False.elim ((Nat.not_lt_of_ge (hprod.trans hn)) (Nat.lt_succ_sqrt N))

theorem tail_square_convolution_vanishes (f g : ArithmeticFunction ℝ)
    (N n : ℕ) (hn : n ≤ N) :
    (((f - arithmeticTruncation f (Nat.sqrt N)) *
      (f - arithmeticTruncation f (Nat.sqrt N))) * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  have hp' := Nat.mem_divisorsAntidiagonal.mp hp
  have hp₁ : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2) ⟨p.2, hp'.1.symm⟩
  rw [tail_square_vanishes f N p.1 (hp₁.trans hn), zero_mul]

theorem mobius_hyperbola_coefficient (N n : ℕ) (hn : n ≤ N) :
    mobiusR n = 2 * arithmeticTruncation mobiusR (Nat.sqrt N) n -
      ((arithmeticTruncation mobiusR (Nat.sqrt N) *
        arithmeticTruncation mobiusR (Nat.sqrt N)) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
  let s := arithmeticTruncation mobiusR (Nat.sqrt N)
  let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hinv : mobiusR * z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have halg : (mobiusR - s) * (mobiusR - s) * z = mobiusR - (s + s) + s * s * z := by
    calc
      _ = mobiusR * (mobiusR * z) - (s * (mobiusR * z) + s * (mobiusR * z)) +
          s * s * z := by ring
      _ = _ := by rw [hinv]; ring
  have hzero := tail_square_convolution_vanishes mobiusR z N n hn
  change ((mobiusR - s) * (mobiusR - s) * z) n = 0 at hzero
  rw [halg] at hzero
  simp only [ArithmeticFunction.add_apply, arithmetic_sub_apply] at hzero
  change mobiusR n = 2 * s n - (s * s * z) n
  calc
    mobiusR n = (mobiusR n - (s n + s n) + (s * s * z) n) +
      (2 * s n - (s * s * z) n) := by ring
    _ = _ := by rw [hzero, zero_add]

theorem weighted_triple_convolution (f g h : ArithmeticFunction ℝ) (w : ℕ → ℝ)
    (N : ℕ) (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, ((f * g) * h) n * w n) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, ∑ c ∈ Ioc 0 N,
        f a * g b * h c * w (a * b * c) := by
  rw [mul_assoc, weighted_convolution f (g * h) w N hw]
  apply sum_congr rfl
  intro a ha
  have hscaled : ∀ n, N < n → w (a * n) = 0 := by
    intro n hn
    exact hw _ (hn.trans_le (Nat.le_mul_of_pos_left n (mem_Ioc.mp ha).1))
  calc
    _ = f a * (∑ b ∈ Ioc 0 N, (g * h) b * w (a * b)) := by
      simp only [mul_sum, mul_assoc]
    _ = f a * (∑ b ∈ Ioc 0 N, ∑ c ∈ Ioc 0 N, g b * h c * w (a * (b * c))) := by
      rw [weighted_convolution g h (fun n => w (a * n)) N hscaled]
    _ = _ := by simp only [mul_sum, mul_assoc]

def hyperbolaU (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, mobiusR n * w n

def hyperbolaE (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 (Nat.sqrt N), mobiusR n * w n

def hyperbolaT (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ Ioc 0 (Nat.sqrt N), ∑ b ∈ Ioc 0 (Nat.sqrt N),
    mobiusR a * mobiusR b * (∑ c ∈ Ioc 0 N, w (a * b * c))

theorem truncated_convolution_is_hyperbolaT (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, ((arithmeticTruncation mobiusR (Nat.sqrt N) *
      arithmeticTruncation mobiusR (Nat.sqrt N)) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n * w n) = hyperbolaT w N := by
  let s := arithmeticTruncation mobiusR (Nat.sqrt N)
  rw [weighted_triple_convolution]
  · calc
      (∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, ∑ c ∈ Ioc 0 N,
          s a * s b * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) c * w (a * b * c)) =
        ∑ a ∈ Ioc 0 N, s a * (∑ b ∈ Ioc 0 N, s b * (∑ c ∈ Ioc 0 N, w (a * b * c))) := by
          simp only [mul_sum]
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          apply sum_congr rfl
          intro c hc
          have hc₀ : c ≠ 0 := (mem_Ioc.mp hc).1.ne'
          simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hc₀, mul_assoc]
      _ = ∑ a ∈ Ioc 0 (Nat.sqrt N), mobiusR a *
          (∑ b ∈ Ioc 0 N, s b * (∑ c ∈ Ioc 0 N, w (a * b * c))) :=
        arithmeticTruncation_sum mobiusR _ _ _ (Nat.sqrt_le_self N)
      _ = hyperbolaT w N := by
        unfold hyperbolaT
        apply sum_congr rfl
        intro a ha
        rw [show (∑ b ∈ Ioc 0 N, s b * (∑ c ∈ Ioc 0 N, w (a * b * c))) =
            ∑ b ∈ Ioc 0 (Nat.sqrt N), mobiusR b * (∑ c ∈ Ioc 0 N, w (a * b * c)) from
          arithmeticTruncation_sum mobiusR _ _ _ (Nat.sqrt_le_self N)]
        simp only [mul_sum, mul_assoc]
  · exact hw

theorem finite_mobius_hyperbola (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    hyperbolaU w N = 2 * hyperbolaE w N - hyperbolaT w N := by
  unfold hyperbolaU hyperbolaE
  calc
    _ = ∑ n ∈ Ioc 0 N, (2 * arithmeticTruncation mobiusR (Nat.sqrt N) n -
          ((arithmeticTruncation mobiusR (Nat.sqrt N) *
            arithmeticTruncation mobiusR (Nat.sqrt N)) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) * w n := by
      apply sum_congr rfl
      intro n hn
      rw [← mobius_hyperbola_coefficient N n (mem_Ioc.mp hn).2]
    _ = 2 * (∑ n ∈ Ioc 0 N, arithmeticTruncation mobiusR (Nat.sqrt N) n * w n) -
        (∑ n ∈ Ioc 0 N, ((arithmeticTruncation mobiusR (Nat.sqrt N) *
          arithmeticTruncation mobiusR (Nat.sqrt N)) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n * w n) := by
      simp only [sub_mul, sum_sub_distrib, mul_sum, mul_assoc]
    _ = _ := by
      rw [arithmeticTruncation_sum mobiusR w (Nat.sqrt N) N (Nat.sqrt_le_self N),
        truncated_convolution_is_hyperbolaT w N hw]

/-- The exact logarithmic test obtained after expanding genuine von Mangoldt coefficients. -/
def finiteLogarithmicTest (w : ℕ → ℝ) (N a : ℕ) : ℝ :=
  ∑ b ∈ Ioc 0 N, Real.log b * w (a * b)

theorem finiteLogarithmicTest_support (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    ∀ a, N < a → finiteLogarithmicTest w N a = 0 := by
  intro a ha
  unfold finiteLogarithmicTest
  apply sum_eq_zero
  intro b hb
  rw [hw _ (ha.trans_le (Nat.le_mul_of_pos_right a (mem_Ioc.mp hb).1)), mul_zero]

/-- Exact finite flattening of the genuine prime-power source, without a positivity premise. -/
theorem vonMangoldt_weighted_is_hyperbolaU (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n * w n) =
      hyperbolaU (finiteLogarithmicTest w N) N := by
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
  rw [weighted_convolution _ _ w N hw]
  unfold hyperbolaU finiteLogarithmicTest mobiusR
  simp only [mul_sum, ArithmeticFunction.log_apply, mul_assoc]

/-- Hyperbola decomposition of the exact weighted prime-power source. This is an equality,
    not an estimate of the signed boundary form. -/
theorem finite_vonMangoldt_hyperbola (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n * w n) =
      2 * hyperbolaE (finiteLogarithmicTest w N) N -
        hyperbolaT (finiteLogarithmicTest w N) N := by
  rw [vonMangoldt_weighted_is_hyperbolaU w N hw]
  exact finite_mobius_hyperbola _ N (finiteLogarithmicTest_support w N hw)

theorem hyperbolaT_one (w : ℕ → ℝ) : hyperbolaT w 1 = w 1 := by
  norm_num [hyperbolaT, mobiusR]

/-- A signed test can make the exact genuine-Möbius finite form negative. Thus the
    algebraic identity by itself cannot be promoted to positivity. -/
theorem hyperbolaT_negative_test :
    hyperbolaT (fun n => if n = 1 then -1 else 0) 1 < 0 := by
  rw [hyperbolaT_one]
  norm_num


theorem finiteLogarithmicTest_half_support (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    ∀ a, N / 2 < a → finiteLogarithmicTest w N a = 0 := by
  intro a ha
  unfold finiteLogarithmicTest
  apply sum_eq_zero
  intro b hb
  by_cases hb₁ : b = 1
  · simp [hb₁]
  have hb₂ : 2 ≤ b := Nat.succ_le_of_lt
    (lt_of_le_of_ne (mem_Ioc.mp hb).1 (Ne.symm hb₁))
  have hNa : N < a * 2 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp ha
  rw [hw _ (hNa.trans_le (Nat.mul_le_mul_left a hb₂)), mul_zero]

theorem hyperbolaU_shrink (w : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (hw : ∀ n, M < n → w n = 0) :
    hyperbolaU w N = hyperbolaU w M := by
  unfold hyperbolaU
  symm
  apply sum_subset (Ioc_subset_Ioc le_rfl hMN)
  intro n hn hnM
  have hnlt : M < n := by
    by_contra h
    exact hnM (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, Nat.le_of_not_gt h⟩)
  rw [hw n hnlt, mul_zero]

/-- The logarithmic factor kills b=1, so the true outer Möbius support is N/2.
    This preserves the original N in the logarithmic test and uses sqrt(N/2)
    for the hyperbola cutoff. -/
theorem finite_vonMangoldt_hyperbola_half (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n * w n) =
      2 * hyperbolaE (finiteLogarithmicTest w N) (N / 2) -
        hyperbolaT (finiteLogarithmicTest w N) (N / 2) := by
  rw [vonMangoldt_weighted_is_hyperbolaU w N hw,
    hyperbolaU_shrink _ (N / 2) N (Nat.div_le_self N 2)
      (finiteLogarithmicTest_half_support w N hw)]
  exact finite_mobius_hyperbola _ _ (finiteLogarithmicTest_half_support w N hw)


end Zeta23.OPICARound4
