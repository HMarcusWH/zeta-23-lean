import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.Floor
import Zeta23.OPICARound2.FilteredClassicalComparison

/-!
# Exact arithmetic of the four-column filtered baseline

These declarations check the literal coefficients and periodic Abel budget.
They do not identify the budget with the actual filtered native L2 residual:
that analytic transport and its source-visible zero lower bound are separate
obligations. In particular the rational comparison below is not the S06
regional zero-exclusion theorem.
-/

namespace Zeta23.OPICARound2

open Finset

/-- The fixed trial, indexed by `n = i + 1`. -/
def baselineCoefficients : Fin 4 → ℚ := ![1, -1, -1, -(2 / 3)]

/-- The actual integer-cell classical residual, before period reduction. -/
def baselineCellResidual (n : ℕ) : ℚ :=
  1 - (n : ℚ) + (n / 2 : ℕ) + (n / 3 : ℕ) + (2 / 3 : ℚ) * (n / 4 : ℕ)

/-- The twelve literal residual values, including the cell at zero. -/
def baselinePeriod (n : ℕ) : ℚ :=
  match n % 12 with
  | 0 => 1
  | 4 => 2 / 3
  | 5 => -(1 / 3)
  | 6 => 2 / 3
  | 7 => -(1 / 3)
  | 8 => 1 / 3
  | 9 => 1 / 3
  | 10 => 1 / 3
  | 11 => -(2 / 3)
  | _ => 0

theorem baseline_pole_moment_zero :
    ∑ i : Fin 4, baselineCoefficients i / ((i.val + 1 : ℕ) : ℚ) = 0 := by
  norm_num [baselineCoefficients, Fin.sum_univ_succ]

theorem baseline_cell_periodic (n : ℕ) :
    baselineCellResidual (n + 12) = baselineCellResidual n := by
  have h2 : (n + 12) / 2 = n / 2 + 6 := by omega
  have h3 : (n + 12) / 3 = n / 3 + 4 := by omega
  have h4 : (n + 12) / 4 = n / 4 + 3 := by omega
  simp only [baselineCellResidual, h2, h3, h4, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem baseline_period_periodic (n : ℕ) :
    baselinePeriod (n + 12) = baselinePeriod n := by
  have hmod : (n + 12) % 12 = n % 12 := by omega
  simp only [baselinePeriod, hmod]

theorem baseline_first_period (n : ℕ) (hn : n < 12) :
    baselineCellResidual n = baselinePeriod n := by
  interval_cases n <;> norm_num [baselineCellResidual, baselinePeriod]

/-- The squared period has the claimed exact mean. -/
theorem baseline_period_square_sum :
    ∑ n ∈ range 12, baselinePeriod n ^ 2 = (26 / 9 : ℚ) := by
  norm_num [baselinePeriod, sum_range_succ]

theorem baseline_period_square_mean :
    (∑ n ∈ range 12, baselinePeriod n ^ 2) / 12 = (13 / 54 : ℚ) := by
  rw [baseline_period_square_sum]
  norm_num

/-- Every initial centered sum in one period has the required Abel upper. -/
theorem baseline_centered_prefix_upper (r : ℕ) (hr : r ≤ 12) :
    ∑ n ∈ range r, (baselinePeriod n ^ 2 - (13 / 54 : ℚ)) ≤ (41 / 54 : ℚ) := by
  interval_cases r <;> norm_num [baselinePeriod, sum_range_succ]

theorem baseline_centered_period_zero :
    ∑ n ∈ range 12, (baselinePeriod n ^ 2 - (13 / 54 : ℚ)) = 0 := by
  norm_num [baselinePeriod, sum_range_succ]

theorem baseline_centered_prefix_attains :
    ∑ n ∈ range 1, (baselinePeriod n ^ 2 - (13 / 54 : ℚ)) = (41 / 54 : ℚ) := by
  norm_num [baselinePeriod, sum_range_succ]

/-- The finite forty-seven-cell contribution plus the two Abel-tail terms.
The analytic tail theorem is intentionally not assumed in this definition. -/
def baselineAbelBudget : ℚ :=
  (∑ n ∈ range 47, baselinePeriod (n + 1) ^ 2 *
    (1 / ((n + 1 : ℕ) : ℚ) - 1 / ((n + 2 : ℕ) : ℚ))) +
    (13 / 54 : ℚ) / 48 + (41 / 54 : ℚ) / (48 * 49)

theorem baseline_abel_budget_exact :
    baselineAbelBudget = (315384568453197375401 / 4648566756368995059600 : ℚ) := by
  norm_num [baselineAbelBudget, baselinePeriod, sum_range_succ]

theorem baseline_abel_budget_lt : baselineAbelBudget < (17 / 250 : ℚ) := by
  rw [baseline_abel_budget_exact]
  norm_num

def baselineSourceMargin : ℚ := 1 - (3 / 8 : ℚ) / 2048 - 2 / 2048 ^ 2

theorem baseline_source_margin_exact :
    baselineSourceMargin = (2096767 / 2097152 : ℚ) := by
  norm_num [baselineSourceMargin]

/-- The stated squared zero-witness lower, as an exact rational expression.
Its application to the actual source is a separate analytic theorem. -/
def baselineWitnessBudget : ℚ :=
  (8192 / 93025 : ℚ) * baselineSourceMargin ^ 2

theorem baseline_witness_budget_exact :
    baselineWitnessBudget = (4396431852289 / 49942416588800 : ℚ) := by
  norm_num [baselineWitnessBudget, baselineSourceMargin]

theorem baseline_witness_budget_pos : 0 < baselineWitnessBudget := by
  rw [baseline_witness_budget_exact]
  norm_num

theorem baseline_strict_rational_separation :
    baselineAbelBudget < (17 / 250 : ℚ) ∧
      (17 / 250 : ℚ) < baselineWitnessBudget := by
  constructor
  · exact baseline_abel_budget_lt
  · rw [baseline_witness_budget_exact]
    norm_num

theorem baseline_witness_above_decimal :
    (8803 / 100000 : ℚ) < baselineWitnessBudget := by
  rw [baseline_witness_budget_exact]
  norm_num

theorem baseline_cell_eq_period (n : ℕ) :
    baselineCellResidual n = baselinePeriod n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 12
    · exact baseline_first_period n hn
    · have he : n - 12 + 12 = n := by omega
      have hlt : n - 12 < n := by omega
      calc
        baselineCellResidual n = baselineCellResidual (n - 12) := by
          conv_lhs => rw [← he]
          exact baseline_cell_periodic (n - 12)
        _ = baselinePeriod (n - 12) := ih (n - 12) hlt
        _ = baselinePeriod n := by
          conv_rhs => rw [← he]
          exact (baseline_period_periodic (n - 12)).symm

theorem baseline_centered_prefix_periodic (n : ℕ) :
    (∑ i ∈ range (n + 12), (baselinePeriod i ^ 2 - (13 / 54 : ℚ))) =
      ∑ i ∈ range n, (baselinePeriod i ^ 2 - (13 / 54 : ℚ)) := by
  rw [Nat.add_comm n 12, sum_range_add, baseline_centered_period_zero, zero_add]
  apply sum_congr rfl
  intro i hi
  rw [Nat.add_comm 12 i, baseline_period_periodic]

theorem baseline_centered_prefix_upper_all (n : ℕ) :
    ∑ i ∈ range n, (baselinePeriod i ^ 2 - (13 / 54 : ℚ)) ≤ (41 / 54 : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 12
    · exact baseline_centered_prefix_upper n hn
    · have he : n - 12 + 12 = n := by omega
      rw [← he, baseline_centered_prefix_periodic]
      exact ih (n - 12) (by omega)

/-- The finite Abel upper uses only one-sided partial-sum control and
nonnegative decreasing weights. No infinite-series theorem is assumed. -/
theorem finite_abel_upper (a w : ℕ → ℚ) (M : ℚ)
    (hM : 0 ≤ M) (hw : ∀ n, 0 ≤ w n)
    (hdec : ∀ n, w (n + 1) ≤ w n)
    (hA : ∀ n, ∑ i ∈ range n, a i ≤ M) (N : ℕ) :
    ∑ i ∈ range N, a i * w i ≤ M * w 0 := by
  cases N with
  | zero => simpa using mul_nonneg hM (hw 0)
  | succ n =>
    have hparts := sum_range_by_parts w a (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
    have hrepr : (∑ i ∈ range (n + 1), a i * w i) =
        w n * (∑ i ∈ range (n + 1), a i) +
          ∑ i ∈ range n, (w i - w (i + 1)) * (∑ j ∈ range (i + 1), a j) := by
      calc
        _ = ∑ i ∈ range (n + 1), w i * a i := by
          apply sum_congr rfl
          intro i hi
          ring
        _ = _ := hparts
        _ = _ := by
          rw [sub_eq_add_neg, ← sum_neg_distrib]
          congr 1
          apply sum_congr rfl
          intro i hi
          ring
    have htel (m : ℕ) : ∑ i ∈ range m, (w i - w (i + 1)) = w 0 - w m := by
      induction m with
      | zero => simp
      | succ m ih => rw [sum_range_succ, ih]; ring
    rw [hrepr]
    calc
      _ ≤ w n * M + ∑ i ∈ range n, (w i - w (i + 1)) * M := by
        apply add_le_add (mul_le_mul_of_nonneg_left (hA _) (hw _))
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hA _) (sub_nonneg.mpr (hdec i))
      _ = M * w 0 := by rw [← sum_mul, htel n]; ring

def baselineTailWeight (n : ℕ) : ℚ :=
  1 / (48 + (n : ℚ)) - 1 / (49 + (n : ℚ))

theorem baselineTailWeight_eq (n : ℕ) :
    baselineTailWeight n = 1 / ((48 + (n : ℚ)) * (49 + (n : ℚ))) := by
  have h0 : (48 + (n : ℚ)) ≠ 0 := by positivity
  have h1 : (49 + (n : ℚ)) ≠ 0 := by positivity
  unfold baselineTailWeight
  field_simp
  <;> ring

theorem baselineTailWeight_nonneg (n : ℕ) : 0 ≤ baselineTailWeight n := by
  rw [baselineTailWeight_eq]
  positivity

theorem baselineTailWeight_decreasing (n : ℕ) :
    baselineTailWeight (n + 1) ≤ baselineTailWeight n := by
  rw [baselineTailWeight_eq, baselineTailWeight_eq]
  apply one_div_le_one_div_of_le
  · positivity
  · push_cast
    nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem baselineTailWeight_sum (n : ℕ) :
    ∑ i ∈ range n, baselineTailWeight i =
      (1 / 48 : ℚ) - 1 / (48 + (n : ℚ)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, baselineTailWeight]
    push_cast
    have h : (48 : ℚ) + ((n : ℚ) + 1) = 49 + (n : ℚ) := by ring
    rw [h]
    ring

theorem baselineTailWeight_sum_le (n : ℕ) :
    ∑ i ∈ range n, baselineTailWeight i ≤ (1 / 48 : ℚ) := by
  rw [baselineTailWeight_sum]
  have h : (0 : ℚ) ≤ 1 / (48 + (n : ℚ)) := by positivity
  linarith

theorem baseline_period_shift_48 (n : ℕ) :
    baselinePeriod (48 + n) = baselinePeriod n := by
  have hmod : (48 + n) % 12 = n % 12 := by omega
  simp only [baselinePeriod, hmod]

theorem baseline_periodic_abel_tail (n : ℕ) :
    ∑ i ∈ range n, baselinePeriod (48 + i) ^ 2 * baselineTailWeight i ≤
      (13 / 54 : ℚ) / 48 + (41 / 54 : ℚ) / (48 * 49) := by
  have hcenter : ∑ i ∈ range n,
      (baselinePeriod i ^ 2 - (13 / 54 : ℚ)) * baselineTailWeight i ≤
        (41 / 54 : ℚ) * baselineTailWeight 0 :=
    finite_abel_upper (fun i => baselinePeriod i ^ 2 - (13 / 54 : ℚ))
      baselineTailWeight (41 / 54) (by norm_num) baselineTailWeight_nonneg
      baselineTailWeight_decreasing baseline_centered_prefix_upper_all n
  have hmean : (13 / 54 : ℚ) * (∑ i ∈ range n, baselineTailWeight i) ≤
      (13 / 54 : ℚ) / 48 := by
    have h := mul_le_mul_of_nonneg_left (baselineTailWeight_sum_le n)
      (by norm_num : (0 : ℚ) ≤ 13 / 54)
    simpa only [div_eq_mul_inv, one_mul] using h
  have heq : (∑ i ∈ range n, baselinePeriod (48 + i) ^ 2 * baselineTailWeight i) =
      (13 / 54 : ℚ) * (∑ i ∈ range n, baselineTailWeight i) +
        ∑ i ∈ range n,
          (baselinePeriod i ^ 2 - (13 / 54 : ℚ)) * baselineTailWeight i := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [baseline_period_shift_48]
    ring
  rw [heq]
  have hb : (41 / 54 : ℚ) * baselineTailWeight 0 =
      (41 / 54 : ℚ) / (48 * 49) := by norm_num [baselineTailWeight]
  rw [hb] at hcenter
  exact add_le_add hmean hcenter

def baselineSeriesTermQ (n : ℕ) : ℚ :=
  baselinePeriod (n + 1) ^ 2 *
    (1 / ((n + 1 : ℕ) : ℚ) - 1 / ((n + 2 : ℕ) : ℚ))

def baselinePartial (n : ℕ) : ℚ := ∑ i ∈ range n, baselineSeriesTermQ i

theorem baselineSeriesTermQ_nonneg (n : ℕ) : 0 ≤ baselineSeriesTermQ n := by
  apply mul_nonneg (sq_nonneg _)
  apply sub_nonneg.mpr
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast (show n + 1 ≤ n + 2 by omega)

theorem baselinePartial_mono {n m : ℕ} (hnm : n ≤ m) :
    baselinePartial n ≤ baselinePartial m := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hnm)
    (fun i _ _ => baselineSeriesTermQ_nonneg i)

theorem baselinePartial_split_tail (n : ℕ) :
    baselinePartial (47 + n) = baselinePartial 47 +
      ∑ i ∈ range n, baselinePeriod (48 + i) ^ 2 * baselineTailWeight i := by
  unfold baselinePartial
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  have h1 : 47 + i + 1 = 48 + i := by omega
  have h2 : 47 + i + 2 = 49 + i := by omega
  simp only [baselineSeriesTermQ, h1, h2, baselineTailWeight, Nat.cast_add,
    Nat.cast_ofNat]

theorem baselinePartial_extended_le_budget (n : ℕ) :
    baselinePartial (47 + n) ≤ baselineAbelBudget := by
  rw [baselinePartial_split_tail]
  have htail := baseline_periodic_abel_tail n
  change baselinePartial 47 + _ ≤
    baselinePartial 47 + (13 / 54 : ℚ) / 48 + (41 / 54 : ℚ) / (48 * 49)
  linarith

theorem baselinePartial_le_budget (n : ℕ) : baselinePartial n ≤ baselineAbelBudget :=
  (baselinePartial_mono (show n ≤ 47 + n by omega)).trans
    (baselinePartial_extended_le_budget n)

def baselineSeriesTerm (n : ℕ) : ℝ := (baselineSeriesTermQ n : ℝ)

theorem baselineSeriesTerm_nonneg (n : ℕ) : 0 ≤ baselineSeriesTerm n := by
  change (0 : ℝ) ≤ (baselineSeriesTermQ n : ℝ)
  exact_mod_cast baselineSeriesTermQ_nonneg n

theorem baselineSeries_partial_le (n : ℕ) :
    ∑ i ∈ range n, baselineSeriesTerm i ≤ (baselineAbelBudget : ℝ) := by
  have h := baselinePartial_le_budget n
  change (∑ i ∈ range n, baselineSeriesTermQ i) ≤ baselineAbelBudget at h
  change (∑ i ∈ range n, (baselineSeriesTermQ i : ℝ)) ≤ (baselineAbelBudget : ℝ)
  exact_mod_cast h

theorem baselineSeries_summable : Summable baselineSeriesTerm :=
  summable_of_sum_range_le baselineSeriesTerm_nonneg baselineSeries_partial_le

/-- The entire classical cell series is bounded, including every uncomputed
tail cell. Identification with a physical residual integral is not assumed. -/
theorem baseline_series_abel_upper :
    (∑' n : ℕ, baselineSeriesTerm n) ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) := by
  have h := Real.tsum_le_of_sum_range_le baselineSeriesTerm_nonneg baselineSeries_partial_le
  have hbudget : (baselineAbelBudget : ℝ) =
      (315384568453197375401 / 4648566756368995059600 : ℝ) := by
    rw [baseline_abel_budget_exact]
    norm_num
  exact h.trans_eq hbudget


end Zeta23.OPICARound2

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.OPICARound2

/-- The literal floor residual on the reciprocal classical coordinate. -/
def baselineClassicalC (y : ℝ) : ℝ :=
  1 - (⌊y⌋₊ : ℝ) + (⌊y / 2⌋₊ : ℝ) + (⌊y / 3⌋₊ : ℝ) +
    (2 / 3 : ℝ) * (⌊y / 4⌋₊ : ℝ)

theorem baselineClassicalC_eq_period (y : ℝ) :
    baselineClassicalC y = (baselinePeriod ⌊y⌋₊ : ℝ) := by
  rw [← baseline_cell_eq_period]
  unfold baselineClassicalC baselineCellResidual
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast]
  push_cast
  rfl

theorem baselinePeriod_sq_le_one (n : ℕ) : (baselinePeriod n : ℝ) ^ 2 ≤ 1 := by
  have hn : n % 12 < 12 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 12 <;> norm_num [baselinePeriod, h]

theorem baselineClassicalC_sq_le_one (y : ℝ) : baselineClassicalC y ^ 2 ≤ 1 := by
  rw [baselineClassicalC_eq_period]
  exact baselinePeriod_sq_le_one _

theorem baselineClassicalC_measurable : Measurable baselineClassicalC := by
  have heq : baselineClassicalC = fun y : ℝ => (baselinePeriod ⌊y⌋₊ : ℝ) :=
    funext baselineClassicalC_eq_period
  rw [heq]
  exact (measurable_of_countable (fun n : ℕ => (baselinePeriod n : ℝ))).comp
    Nat.measurable_floor

def baselineClassicalEnergy (y : ℝ) : ℝ := baselineClassicalC y ^ 2 / y ^ 2

theorem baselineClassicalEnergy_nonneg (y : ℝ) : 0 ≤ baselineClassicalEnergy y := by
  unfold baselineClassicalEnergy
  positivity

theorem baselineClassicalEnergy_integrable : IntegrableOn baselineClassicalEnergy (Ioi 1) := by
  have hm : Measurable baselineClassicalEnergy :=
    (baselineClassicalC_measurable.pow_const 2).div (measurable_id.pow_const 2)
  have hdom : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 1 < y at hy
  rw [Real.norm_of_nonneg (baselineClassicalEnergy_nonneg y),
    Real.rpow_neg (by linarith : 0 ≤ y), Real.rpow_two]
  unfold baselineClassicalEnergy
  simpa only [one_div] using
    div_le_div_of_nonneg_right (baselineClassicalC_sq_le_one y) (sq_nonneg y)

theorem baselineClassicalEnergy_cell {n : ℕ} (hn : 1 ≤ n) :
    (∫ y : ℝ in (n : ℝ)..((n : ℝ) + 1), baselineClassicalEnergy y) =
      (baselinePeriod n : ℝ) ^ 2 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hcell : (∫ y : ℝ in (n : ℝ)..((n : ℝ) + 1), baselineClassicalEnergy y) =
      (baselinePeriod n : ℝ) ^ 2 * ∫ y : ℝ in (n : ℝ)..((n : ℝ) + 1), 1 / y ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    rw [baselineClassicalEnergy, baselineClassicalC_eq_period,
      Nat.floor_eq_on_Ico n y (Ioo_subset_Ico_self hy)]
    ring
  rw [hcell]
  congr 1
  have hpos : ∀ y ∈ uIcc (n : ℝ) ((n : ℝ) + 1), 0 < y := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    linarith [hy.1]
  have hderiv : ∀ y ∈ uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun x : ℝ => -x⁻¹) (1 / y ^ 2) y := by
    intro y hy
    simpa only [neg_neg, one_div] using! (hasDerivAt_inv (ne_of_gt (hpos y hy))).neg
  have hcont : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    exact continuousOn_const.div (continuousOn_id.pow 2) fun y hy => by
      exact pow_ne_zero 2 (ne_of_gt (hpos y hy))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

theorem baselineClassicalEnergy_intervalIntegrable (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable baselineClassicalEnergy volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact baselineClassicalEnergy_integrable.mono_set fun y hy => ha.trans_lt hy.1

theorem baselineClassicalEnergy_finite_cells (N : ℕ) :
    (∫ y : ℝ in (1 : ℝ)..((N : ℝ) + 1), baselineClassicalEnergy y) =
      ∑ i ∈ Finset.range N, baselineSeriesTerm i := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) + 1) (f := baselineClassicalEnergy)
    (n := N) (fun k hk => baselineClassicalEnergy_intervalIntegrable _ _ (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)
      (by push_cast; linarith))
  norm_num only [Nat.cast_zero, zero_add] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro k hk
  have hcell := baselineClassicalEnergy_cell (n := k + 1) (by omega)
  have hleft : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
  have hright : ((k + 1 : ℕ) : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := rfl
  rw [hleft] at hcell
  rw [hleft, hcell]
  simp only [baselineSeriesTerm, baselineSeriesTermQ]
  push_cast
  ring

/-- Identification of the convergent cell series with the actual reciprocal
coordinate integral, including all cells beyond the checked finite prefix. -/
theorem baselineClassicalEnergy_integral_eq_series :
    (∫ y : ℝ in Ioi 1, baselineClassicalEnergy y) = ∑' n : ℕ, baselineSeriesTerm n := by
  have hi := intervalIntegral_tendsto_integral_Ioi (1 : ℝ)
    (b := fun N : ℕ => (N : ℝ) + 1)
    baselineClassicalEnergy_integrable
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  simp_rw [baselineClassicalEnergy_finite_cells] at hi
  exact tendsto_nhds_unique hi baselineSeries_summable.hasSum.tendsto_sum_nat

theorem baselineClassicalEnergy_integral_upper :
    (∫ y : ℝ in Ioi 1, baselineClassicalEnergy y) ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) := by
  rw [baselineClassicalEnergy_integral_eq_series]
  exact baseline_series_abel_upper

def baselineComplexCoefficients (i : Fin 4) : ℂ := (baselineCoefficients i : ℂ)

theorem baseline_complex_pole_moment_zero :
    ∑ i : Fin 4, baselineComplexCoefficients i / ((i.val + 1 : ℕ) : ℂ) = 0 := by
  norm_num [baselineComplexCoefficients, baselineCoefficients, Fin.sum_univ_succ]

private theorem reciprocal_image_Ioi_one :
    (fun x : ℝ => x⁻¹) '' Ioi 1 = Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : 0 < x := lt_trans one_pos hx
    exact ⟨inv_pos.mpr hx0, (inv_lt_one₀ hx0).mpr hx⟩
  · intro hy
    exact ⟨y⁻¹, (one_lt_inv₀ hy.1).mpr hy.2, inv_inv y⟩

private theorem reciprocal_derivative (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
    HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioi 1) x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  simpa using! (hasDerivAt_inv (ne_of_gt hx0)).hasDerivWithinAt (s := Ioi (1 : ℝ))

theorem reciprocal_coordinate_integral (F : ℝ → ℝ) :
    (∫ x : ℝ in Ioo 0 1, F x) = ∫ y : ℝ in Ioi 1, F y⁻¹ / y ^ 2 := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (1 : ℝ)) (f := fun y : ℝ => y⁻¹) (f' := fun y : ℝ => -(y ^ 2)⁻¹)
    measurableSet_Ioi reciprocal_derivative inv_injective.injOn F
  rw [reciprocal_image_Ioi_one] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg y), smul_eq_mul]
  ring

theorem reciprocal_coordinate_integrable_iff (F : ℝ → ℝ) :
    IntegrableOn F (Ioo 0 1) ↔
      IntegrableOn (fun y : ℝ => F y⁻¹ / y ^ 2) (Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (1 : ℝ)) (f := fun y : ℝ => y⁻¹) (f' := fun y : ℝ => -(y ^ 2)⁻¹)
    measurableSet_Ioi reciprocal_derivative inv_injective.injOn F
  rw [reciprocal_image_Ioi_one] at h
  rw [h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg y), smul_eq_mul]
  ring

theorem baseline_classical_residual_reciprocal {y : ℝ} (hy : 1 < y) :
    classicalFiniteResidual baselineComplexCoefficients y⁻¹ = (baselineClassicalC y : ℂ) := by
  have hy0 : 0 < y := lt_trans one_pos hy
  have hinv : y⁻¹ ∈ Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.mpr hy0, (inv_lt_one₀ hy0).mpr hy⟩
  have hfract (n : ℕ) (hn : 1 ≤ n) :
      Int.fract (1 / ((n : ℝ) * y⁻¹)) = y / n - (⌊y / n⌋₊ : ℝ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have he : 1 / ((n : ℝ) * y⁻¹) = y / n := by field_simp
    rw [he, Int.fract, ← natCast_floor_eq_intCast_floor (by positivity : 0 ≤ y / n)]
  unfold classicalFiniteResidual
  rw [classicalChi, if_pos hinv]
  norm_num [baselineComplexCoefficients, baselineCoefficients, Fin.sum_univ_succ, classicalRho,
    hfract 1 (by omega), hfract 2 (by omega), hfract 3 (by omega), hfract 4 (by omega)]
  unfold baselineClassicalC
  simp only [Int.fract, div_eq_mul_inv, one_mul]
  rw [← natCast_floor_eq_intCast_floor hy0.le,
    ← natCast_floor_eq_intCast_floor (by positivity : 0 ≤ y * (2 : ℝ)⁻¹),
    ← natCast_floor_eq_intCast_floor (by positivity : 0 ≤ y * (3 : ℝ)⁻¹),
    ← natCast_floor_eq_intCast_floor (by positivity : 0 ≤ y * (4 : ℝ)⁻¹)]
  push_cast
  ring

theorem baseline_classical_residual_energy_integrable :
    IntegrableOn (fun x : ℝ => ‖classicalFiniteResidual baselineComplexCoefficients x‖ ^ 2)
      (Ioi 0) := by
  let F : ℝ → ℝ := fun x => ‖classicalFiniteResidual baselineComplexCoefficients x‖ ^ 2
  have heq (y : ℝ) (hy : y ∈ Ioi (1 : ℝ)) : F y⁻¹ / y ^ 2 = baselineClassicalEnergy y := by
    dsimp [F]
    rw [baseline_classical_residual_reciprocal hy, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rfl
  have h01 : IntegrableOn F (Ioo 0 1) :=
    (reciprocal_coordinate_integrable_iff F).mpr
      (baselineClassicalEnergy_integrable.congr_fun (fun y hy => (heq y hy).symm) measurableSet_Ioi)
  have h01closed : IntegrableOn F (Ioc 0 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr h01
  have h1 : IntegrableOn F (Ioi 1) := by
    apply (integrable_zero ℝ ℝ (volume.restrict (Ioi (1 : ℝ)))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [F, classicalFiniteResidual_zero_above_one baselineComplexCoefficients
      baseline_complex_pole_moment_zero hx]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact h01closed.union h1

theorem baseline_classical_residual_integral_eq_energy :
    (∫ x : ℝ in Ioi 0, ‖classicalFiniteResidual baselineComplexCoefficients x‖ ^ 2) =
      ∫ y : ℝ in Ioi 1, baselineClassicalEnergy y := by
  let F : ℝ → ℝ := fun x => ‖classicalFiniteResidual baselineComplexCoefficients x‖ ^ 2
  have hF : IntegrableOn F (Ioi 0) := baseline_classical_residual_energy_integrable
  have h01 : IntegrableOn F (Ioc 0 1) := hF.mono_set Ioc_subset_Ioi_self
  have h1 : IntegrableOn F (Ioi 1) := hF.mono_set (Ioi_subset_Ioi (by norm_num))
  have hzero : (∫ x : ℝ in Ioi 1, F x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [F, classicalFiniteResidual_zero_above_one baselineComplexCoefficients
      baseline_complex_pole_moment_zero hx]
  change (∫ x : ℝ in Ioi 0, F x) = _
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h01 h1,
    hzero, add_zero, integral_Ioc_eq_integral_Ioo, reciprocal_coordinate_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp [F]
  rw [baseline_classical_residual_reciprocal hy, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rfl

theorem baseline_classical_residual_integral_upper :
    (∫ x : ℝ in Ioi 0, ‖classicalFiniteResidual baselineComplexCoefficients x‖ ^ 2) ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) := by
  rw [baseline_classical_residual_integral_eq_energy]
  exact baselineClassicalEnergy_integral_upper


theorem baseline_native_filtered_upper :
    ‖fixedFilteredProbeResidual baselineComplexCoefficients‖ ^ 2 ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) :=
  (filtered_probe_classical_comparison baselineComplexCoefficients).trans
    baseline_classical_residual_integral_upper

theorem baseline_native_filtered_upper_lt :
    ‖fixedFilteredProbeResidual baselineComplexCoefficients‖ ^ 2 < (17 / 250 : ℝ) := by
  have h := baseline_native_filtered_upper
  have hb : (315384568453197375401 / 4648566756368995059600 : ℝ) < 17 / 250 := by norm_num
  exact h.trans_lt hb

theorem filtered_rectangle_zero_witness_lower (rho : zetaZeroConfig.carrier)
    (hr0 : (3 / 4 : ℝ) ≤ (rho : ℂ).re) (hr1 : (rho : ℂ).re ≤ 7 / 8)
    (hi0 : (1 : ℝ) ≤ |(rho : ℂ).im|) (hi1 : |(rho : ℂ).im| ≤ 2)
    {N : ℕ} (x : Fin N → ℂ) :
    (4396431852289 / 49942416588800 : ℝ) ≤ ‖fixedFilteredProbeResidual x‖ ^ 2 := by
  have hright : 1 / 2 < (rho : ℂ).re := by linarith
  have hs := fixedFilteredProbeResidual_reduced_zero_lower rho hright x
  have hr : ((rho : ℂ) - 1 / 2).re = (rho : ℂ).re - 1 / 2 := by simp
  have hi : ((rho : ℂ) - 1 / 2).im = (rho : ℂ).im := by simp
  have hl := reduced_probe_source_rectangle_lower ((rho : ℂ) - 1 / 2)
    (by rw [hr]; linarith) (by rw [hr]; linarith) (by rwa [hi]) (by rwa [hi])
  exact hl.trans hs

theorem filtered_baseline_rectangle_nonvanishing (z : ℂ)
    (hr0 : (3 / 4 : ℝ) ≤ z.re) (hr1 : z.re ≤ 7 / 8)
    (hi0 : (1 : ℝ) ≤ |z.im|) (hi1 : |z.im| ≤ 2) : riemannZeta z ≠ 0 := by
  intro hz
  have hm : z ∈ zetaZeroConfig.carrier := by
    show IsNontrivialZero z
    exact ⟨hz, by linarith, by linarith⟩
  let rho : zetaZeroConfig.carrier := ⟨z, hm⟩
  have hl := filtered_rectangle_zero_witness_lower rho hr0 hr1 hi0 hi1 baselineComplexCoefficients
  have hu := baseline_native_filtered_upper_lt
  have hn : (17 / 250 : ℝ) < 4396431852289 / 49942416588800 := by norm_num
  exact (not_lt_of_ge hl) (hu.trans hn)

/-- The left rectangle uses the actual source zeta functional-equation
reflection encoded by the inherited zero configuration. -/
theorem filtered_baseline_reflected_rectangle_nonvanishing (z : ℂ)
    (hr0 : (1 / 8 : ℝ) ≤ z.re) (hr1 : z.re ≤ 1 / 4)
    (hi0 : (1 : ℝ) ≤ |z.im|) (hi1 : |z.im| ≤ 2) : riemannZeta z ≠ 0 := by
  intro hz
  have hm : z ∈ zetaZeroConfig.carrier := by
    show IsNontrivialZero z
    exact ⟨hz, by linarith, by linarith⟩
  have hrm := zetaZeroConfig.reflect_mem z hm
  have hrr : (Zeta23.reflect z).re = 1 - z.re := by simp [Zeta23.reflect]
  have hri : (Zeta23.reflect z).im = z.im := by simp [Zeta23.reflect]
  have hnon := filtered_baseline_rectangle_nonvanishing (Zeta23.reflect z)
    (by rw [hrr]; linarith) (by rw [hrr]; linarith) (by rwa [hri]) (by rwa [hri])
  exact hnon hrm.1

/-- Exact four-column pipeline certificate. Every norm belongs to the literal
fixed B filter of the unchanged native dictionary. -/
theorem filtered_four_column_region_certificate :
    (∑ i : Fin 4, baselineComplexCoefficients i / ((i.val + 1 : ℕ) : ℂ)) = 0 ∧
    ‖fixedFilteredProbeResidual baselineComplexCoefficients‖ ^ 2 ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) ∧
    (315384568453197375401 / 4648566756368995059600 : ℝ) < 17 / 250 ∧
    (17 / 250 : ℝ) < 4396431852289 / 49942416588800 ∧
    (∀ rho : zetaZeroConfig.carrier,
      (3 / 4 : ℝ) ≤ (rho : ℂ).re → (rho : ℂ).re ≤ 7 / 8 →
      (1 : ℝ) ≤ |(rho : ℂ).im| → |(rho : ℂ).im| ≤ 2 →
      ∀ N : ℕ, ∀ x : Fin N → ℂ,
        (4396431852289 / 49942416588800 : ℝ) ≤ ‖fixedFilteredProbeResidual x‖ ^ 2) ∧
    (∀ z : ℂ, (3 / 4 : ℝ) ≤ z.re → z.re ≤ 7 / 8 →
      (1 : ℝ) ≤ |z.im| → |z.im| ≤ 2 → riemannZeta z ≠ 0) ∧
    (∀ z : ℂ, (1 / 8 : ℝ) ≤ z.re → z.re ≤ 1 / 4 →
      (1 : ℝ) ≤ |z.im| → |z.im| ≤ 2 → riemannZeta z ≠ 0) := by
  refine ⟨baseline_complex_pole_moment_zero, baseline_native_filtered_upper,
    by norm_num, by norm_num, ?_, filtered_baseline_rectangle_nonvanishing,
    filtered_baseline_reflected_rectangle_nonvanishing⟩
  intro rho hr0 hr1 hi0 hi1 N x
  exact filtered_rectangle_zero_witness_lower rho hr0 hr1 hi0 hi1 x

end Zeta23.OPICARound2
