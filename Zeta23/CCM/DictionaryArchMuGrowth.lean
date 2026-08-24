import Zeta23.CCM.DictionaryArchWeight
import Mathlib.Analysis.PSeries

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators

/-! # Sublinear control of the vertical digamma difference

For the source bridge we need an integrable majorant after multiplying by the
quadratically decaying source transform.  A square-root bound is enough and is
proved directly from the positive-abscissa series; no asymptotic formula is
assumed.
-/

/-- The summable `a^{-3/2}` weight attached to the positive abscissae
`a_m = m + 1/4`. -/
def archHalfWeight (m : ℕ) : ℝ :=
  (archSeriesAbscissa m ^ (3 / 2 : ℝ))⁻¹

/-- The positive-abscissa half-power weights are summable. -/
theorem summable_archHalfWeight : Summable archHalfWeight := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [Real.summable_nat_rpow_inv]
    norm_num
  refine Summable.of_norm_bounded_eventually hp ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hna : (n : ℝ) ≤ archSeriesAbscissa n := by
    unfold archSeriesAbscissa
    norm_num
  have hp0 : (0 : ℝ) ≤ (3 / 2 : ℝ) := by norm_num
  have hr := Real.rpow_le_rpow hn0 hna hp0
  have hposn : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by
    positivity
  have hposa : 0 < archSeriesAbscissa n ^ (3 / 2 : ℝ) := by
    have := archSeriesAbscissa_pos n
    positivity
  dsimp [archHalfWeight]
  rw [Real.norm_eq_abs, abs_of_pos hposa, Real.norm_eq_abs, abs_of_pos hposn]
  exact inv_le_inv₀ hposn.le hr

/-- Algebraic positive form of one digamma difference summand. -/
theorem archDigammaAllTerm_eq_sq_div
    (t : ℝ) (m : ℕ) :
    archDigammaAllTerm t m =
      t ^ 2 /
        (archSeriesAbscissa m * (archSeriesAbscissa m ^ 2 + t ^ 2)) := by
  unfold archDigammaAllTerm archSeriesAbscissa
  have ha : (0 : ℝ) < (m : ℝ) + 1 / 4 := by positivity
  have hden : ((m : ℝ) + 1 / 4) ^ 2 + t ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hden]
  ring

/-- Each positive-abscissa digamma term is nonnegative. -/
theorem archDigammaAllTerm_nonneg (t : ℝ) (m : ℕ) :
    0 ≤ archDigammaAllTerm t m := by
  rw [archDigammaAllTerm_eq_sq_div]
  positivity

/-- Interpolation bound `x²/(1+x²) ≤ √x` in the normalization needed by the
positive-abscissa series. -/
theorem archDigammaAllTerm_le_sqrt_weight
    (t : ℝ) (m : ℕ) :
    archDigammaAllTerm t m ≤ Real.sqrt |t| * archHalfWeight m := by
  let a : ℝ := archSeriesAbscissa m
  have ha : 0 < a := archSeriesAbscissa_pos m
  have hs : 0 ≤ |t| := abs_nonneg t
  have hsqrt : 0 ≤ Real.sqrt |t| := Real.sqrt_nonneg _
  have hasqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqta : (Real.sqrt a) ^ 2 = a := by simpa using Real.sq_sqrt ha.le
  have hsqtt : (Real.sqrt |t|) ^ 2 = |t| := by simpa using Real.sq_sqrt hs
  rw [archDigammaAllTerm_eq_sq_div]
  dsimp [archHalfWeight]
  have ha32 : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha.le]
    simp [Real.sqrt_eq_rpow]
  rw [ha32]
  by_cases hta : |t| ≤ a
  · have ht2 : t ^ 2 = |t| ^ 2 := by nlinarith [sq_abs t]
    have hdenpos : 0 < a * (a ^ 2 + t ^ 2) := by positivity
    have hsimple :
        t ^ 2 / (a * (a ^ 2 + t ^ 2)) ≤ t ^ 2 / (a * a ^ 2) := by
      gcongr
      nlinarith [sq_nonneg t]
    have hroot : Real.sqrt |t| ≤ Real.sqrt a := Real.sqrt_le_sqrt hta
    have hcubic : (Real.sqrt |t|) ^ 3 ≤ (Real.sqrt a) ^ 3 := by
      exact pow_le_pow_left₀ hsqrt hroot 3
    have hgoal :
        t ^ 2 / (a * a ^ 2) ≤ Real.sqrt |t| * (a * Real.sqrt a)⁻¹ := by
      rw [div_eq_mul_inv]
      have hdena : 0 < a * a ^ 2 := by positivity
      have hdenr : 0 < a * Real.sqrt a := by positivity
      rw [← le_div_iff₀ hdena]
      field_simp [ha.ne', hasqrt.ne']
      nlinarith [hcubic, hsqta, hsqtt, sq_abs t]
    exact hsimple.trans hgoal
  · have hat : a ≤ |t| := le_of_not_ge hta
    have hdenpos : 0 < a * (a ^ 2 + t ^ 2) := by positivity
    have hleone :
        t ^ 2 / (a * (a ^ 2 + t ^ 2)) ≤ 1 / a := by
      rw [div_le_iff₀ hdenpos]
      have ha2 : 0 < a := ha
      field_simp [ha.ne']
      nlinarith [sq_nonneg t, sq_nonneg a]
    have hroot : Real.sqrt a ≤ Real.sqrt |t| := Real.sqrt_le_sqrt hat
    have hright : 1 / a ≤ Real.sqrt |t| * (a * Real.sqrt a)⁻¹ := by
      have hden : 0 < a * Real.sqrt a := by positivity
      rw [le_mul_inv_iff₀ hden]
      field_simp [ha.ne', hasqrt.ne']
      nlinarith [hroot, hsqta]
    exact hleone.trans hright

/-- The whole positive-abscissa series grows at most like `sqrt |t|`. -/
theorem tsum_archDigammaAllTerm_le_sqrt
    (t : ℝ) :
    (∑' m : ℕ, archDigammaAllTerm t m) ≤
      Real.sqrt |t| * ∑' m : ℕ, archHalfWeight m := by
  have hs := summable_archDigammaAllTerm t
  have hw := summable_archHalfWeight
  have hmul : Summable (fun m : ℕ => Real.sqrt |t| * archHalfWeight m) :=
    hw.const_mul _
  calc
    (∑' m : ℕ, archDigammaAllTerm t m) ≤
        ∑' m : ℕ, Real.sqrt |t| * archHalfWeight m :=
      hs.tsum_le_tsum (fun m => archDigammaAllTerm_le_sqrt_weight t m) hmul
    _ = Real.sqrt |t| * ∑' m : ℕ, archHalfWeight m := by
      rw [tsum_mul_left]

/-- Sublinear square-root growth of the gamma-density difference. -/
theorem mu_sub_mu_zero_le_sqrt (τ : ℝ) :
    Zeta23.mu τ - Zeta23.mu 0 ≤
      (1 / (2 * Real.pi)) *
        (Real.sqrt |τ / 2| * ∑' m : ℕ, archHalfWeight m) := by
  rw [mu_sub_mu_zero_eq_archDigammaAllSeries]
  gcongr
  exact tsum_archDigammaAllTerm_le_sqrt (τ / 2)

end Zeta23.CCM
