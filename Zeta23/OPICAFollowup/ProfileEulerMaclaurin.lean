import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
Finite power-sum Euler-Maclaurin expansion (R2-S1a, R2-H1, F3; paper display S1.3).

The finite sum `∑_{1 ≤ n ≤ x} n^(-s)` keeps its right integer endpoint, and
`B₁({x}) = {x} - 1/2` takes its right endpoint value `-1/2` at integers. The proof is a
foundation proof, not an imported formula:
1. Abel summation gives the exact first-order identity for every real `x ≥ 1`;
2. `ζ(s) = s/(s-1) - 1/2 - s ∫_1^∞ B₁({t}) t^(-s-1) dt` is proved for `Re s > 1` from the
   Dirichlet series and continued to `Re s > 0`, `s ≠ 1` by holomorphy of the Mellin integral
   and the identity theorem on a star-convex domain;
3. two integrations by parts against the continuous periodic `B₂/2` and `B₃/3` (whose right
   derivatives are `B₁` and `B₂`) produce the second-order expansion with an explicit remainder
   of size `O(x^(-Re s - 2))`, uniform on bounded parameter sets.
The parameter domain `0 < Re s`, `s ≠ 1` contains the open critical strip, so it covers both
specializations `s = ρ` and `s = 1 - ρ` and every compact parameter disk inside the strip.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology

namespace Zeta23.OPICAFollowup

/-- B₁({x}) for the right-continuous fractional part: the right integer endpoint is retained. -/
def bernoulliOneRight (x : ℝ) : ℝ := Int.fract x - 1 / 2

/-- B₂({x}). -/
def bernoulliTwo (x : ℝ) : ℝ := Int.fract x ^ 2 - Int.fract x + 1 / 6

/-- B₃({x}), used for the remainder. -/
def bernoulliThree (x : ℝ) : ℝ := Int.fract x ^ 3 - 3 / 2 * Int.fract x ^ 2 + 1 / 2 * Int.fract x

/-- The right-endpoint power sum Σ_(1 ≤ n ≤ x) n^(-s). -/
def rightPowerSum (s : ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)

lemma measurable_bernoulliOneRight : Measurable bernoulliOneRight := by
  unfold bernoulliOneRight; fun_prop

lemma measurable_bernoulliTwo : Measurable bernoulliTwo := by
  unfold bernoulliTwo; fun_prop

lemma measurable_bernoulliThree : Measurable bernoulliThree := by
  unfold bernoulliThree; fun_prop

lemma abs_bernoulliOneRight_le (x : ℝ) : |bernoulliOneRight x| ≤ 1 := by
  unfold bernoulliOneRight
  have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> linarith

lemma abs_bernoulliTwo_le (x : ℝ) : |bernoulliTwo x| ≤ 1 := by
  unfold bernoulliTwo
  have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> nlinarith

lemma abs_bernoulliThree_le (x : ℝ) : |bernoulliThree x| ≤ 1 := by
  unfold bernoulliThree
  have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

lemma continuous_bernoulliTwo : Continuous bernoulliTwo := by
  have h := ContinuousOn.comp_fract (s := fun x : ℝ => x) (f := fun (_ : ℝ) (u : ℝ) => u ^ 2 - u + 1 / 6)
    (by fun_prop) continuous_id (fun _ => by norm_num)
  exact h

lemma continuous_bernoulliThree : Continuous bernoulliThree := by
  have h := ContinuousOn.comp_fract (s := fun x : ℝ => x)
    (f := fun (_ : ℝ) (u : ℝ) => u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u)
    (by fun_prop) continuous_id (fun _ => by norm_num)
  exact h

/-- The fractional part has right derivative 1 everywhere. -/
lemma hasDerivWithinAt_fract_Ioi (t : ℝ) : HasDerivWithinAt Int.fract 1 (Ioi t) t := by
  have h : HasDerivWithinAt (fun y : ℝ => y - ⌊t⌋) 1 (Ioi t) t :=
    ((hasDerivAt_id t).sub_const _).hasDerivWithinAt
  refine h.congr_of_eventuallyEq ?_ rfl
  have hmem : Ioo t (⌊t⌋ + 1 : ℝ) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (Int.lt_floor_add_one t)
  filter_upwards [hmem] with y hy
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨(Int.floor_le t).trans hy.1.le, hy.2⟩]

lemma hasDerivWithinAt_bernoulliTwo_half (t : ℝ) :
    HasDerivWithinAt (fun y => bernoulliTwo y / 2) (bernoulliOneRight t) (Ioi t) t := by
  have hg : HasDerivAt (fun u : ℝ => (u ^ 2 - u + 1 / 6) / 2) ((2 * Int.fract t - 1) / 2)
      (Int.fract t) := by
    have := (((hasDerivAt_pow 2 (Int.fract t)).sub (hasDerivAt_id _)).add_const (1 / 6)).div_const 2
    exact this.congr_deriv (by norm_num)
  have h := hg.comp_hasDerivWithinAt t (hasDerivWithinAt_fract_Ioi t)
  unfold bernoulliTwo bernoulliOneRight
  exact h.congr_deriv (by ring)

lemma hasDerivWithinAt_bernoulliThree_third (t : ℝ) :
    HasDerivWithinAt (fun y => bernoulliThree y / 3) (bernoulliTwo t) (Ioi t) t := by
  have hg : HasDerivAt (fun u : ℝ => (u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u) / 3)
      ((3 * Int.fract t ^ 2 - 3 * Int.fract t + 1 / 2) / 3) (Int.fract t) := by
    have := ((((hasDerivAt_pow 3 (Int.fract t)).sub ((hasDerivAt_pow 2 (Int.fract t)).const_mul
      (3 / 2))).add ((hasDerivAt_id (Int.fract t)).const_mul (1 / 2)))).div_const 3
    exact this.congr_deriv (by norm_num; ring)
  have h := hg.comp_hasDerivWithinAt t (hasDerivWithinAt_fract_Ioi t)
  unfold bernoulliThree bernoulliTwo
  exact h.congr_deriv (by ring)

/-- d/dt t^(-s) = -s t^(-s-1) on (0, ∞), for every complex s. -/
lemma hasDerivAt_cpow_neg (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := by
  by_cases hs : s = 0
  · subst hs
    simp only [neg_zero, Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const t 1
  · exact hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hs)

lemma sum_Icc_zero_ite (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, (if k = 0 then (0 : ℂ) else 1) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp

lemma sum_Icc_zero_mul_ite (m : ℕ) (g : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 0 m, g k * (if k = 0 then (0 : ℂ) else 1) = ∑ k ∈ Finset.Icc 1 m, g k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
  simp only [if_true, mul_zero, zero_add]
  rw [show Finset.Ioc 0 m = Finset.Icc 1 m by ext k; simp; omega]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [if_neg (by simp at hk; omega), mul_one]

lemma natFloor_eq_bernoulli {t : ℝ} (ht : 0 ≤ t) :
    ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - 1 / 2 - (bernoulliOneRight t : ℂ) := by
  have hz : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor ht
  have h : ((⌊t⌋₊ : ℕ) : ℝ) = t - 1 / 2 - bernoulliOneRight t := by
    have h' : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by rw [← hz]; norm_cast
    unfold bernoulliOneRight Int.fract
    rw [h']; ring
  have := congrArg Complex.ofReal h
  push_cast at this
  exact this

lemma continuousOn_cpow_Ici (c : ℂ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ c) (Ici a) := fun _ ht =>
  ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (ha.trans_le ht))).comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

lemma measurable_cpow_real (c : ℂ) : Measurable (fun t : ℝ => (t : ℂ) ^ c) :=
  Complex.measurable_ofReal.pow_const c

/-- Step 1 (Abel summation): the exact first-order identity for every x ≥ 1. -/
theorem rightPowerSum_abel {s : ℂ} (hs : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    rightPowerSum s x = (x : ℂ) ^ (1 - s) / (1 - s) - s / (1 - s) - 1 / 2 -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * ∫ t in Ioc 1 x, (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hf
  have hderiv (t : ℝ) (ht : 0 < t) : deriv f t = -s * (t : ℂ) ^ (-s - 1) :=
    (hasDerivAt_cpow_neg s ht).deriv
  have hdiff : ∀ t ∈ Icc 1 x, DifferentiableAt ℝ f t := fun t ht =>
    (hasDerivAt_cpow_neg s (lt_of_lt_of_le one_pos ht.1)).differentiableAt
  have hc1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Icc 1 x) :=
    (continuousOn_cpow_Ici _ one_pos).mono Icc_subset_Ici_self
  have hc0 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Icc 1 x) :=
    (continuousOn_cpow_Ici _ one_pos).mono Icc_subset_Ici_self
  have hint : IntegrableOn (deriv f) (Icc 1 x) :=
    ((hc1.const_smul (-s)).integrableOn_Icc).congr_fun (fun t ht => by
      rw [hderiv t (lt_of_lt_of_le one_pos ht.1)]; rfl) measurableSet_Icc
  have habel := sum_mul_eq_sub_integral_mul₀ (fun k => if k = 0 then (0 : ℂ) else 1) rfl x hdiff hint
  rw [sum_Icc_zero_mul_ite, sum_Icc_zero_ite] at habel
  simp_rw [sum_Icc_zero_ite] at habel
  -- the three integrals on Ioc 1 x
  have hfin : volume (Ioc (1 : ℝ) x) < ⊤ := measure_Ioc_lt_top
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Ioc 1 x) :=
    (hc1.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hI0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioc 1 x) :=
    (hc0.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hB : IntegrableOn (fun t : ℝ => (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioc 1 x) :=
    hI1.bdd_mul (c := 1) (Complex.measurable_ofReal.comp measurable_bernoulliOneRight).aestronglyMeasurable
      (Eventually.of_forall (fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bernoulliOneRight_le t))
  have hpt : EqOn (fun t => deriv f t * ((⌊t⌋₊ : ℕ) : ℂ))
      (fun t => -s * (t : ℂ) ^ (-s) + (s / 2) * (t : ℂ) ^ (-s - 1) +
        s * ((bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1))) (Ioc 1 x) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    have htt : (t : ℂ) ^ (-s - 1) * (t : ℂ) = (t : ℂ) ^ (-s) := by
      conv_rhs => rw [show -s = (-s - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one]
    simp only
    rw [hderiv t ht0, natFloor_eq_bernoulli ht0.le]
    linear_combination (-s) * htt
  have hA : IntegrableOn (fun t : ℝ => -s * (t : ℂ) ^ (-s) + (s / 2) * (t : ℂ) ^ (-s - 1)) (Ioc 1 x) :=
    (hI0.const_mul _).add (hI1.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hA (hB.const_mul _),
    integral_add (hI0.const_mul _) (hI1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at habel
  -- the two power integrals
  have hJ0 : ∫ t in Ioc 1 x, (t : ℂ) ^ (-s) = ((x : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    rw [← intervalIntegral.integral_of_le hx, integral_cpow (Or.inr ⟨fun h => hs (by
      linear_combination -h), by simp [Set.uIcc_of_le hx]⟩)]
    rw [show -s + 1 = 1 - s by ring]
    simp only [Complex.ofReal_one, Complex.one_cpow]
  have hJ1 : s * ∫ t in Ioc 1 x, (t : ℂ) ^ (-s - 1) = 1 - (x : ℂ) ^ (-s) := by
    rw [← integral_const_mul, ← intervalIntegral.integral_of_le hx]
    have hF : ∀ t ∈ uIcc 1 x, HasDerivAt (fun y : ℝ => -(y : ℂ) ^ (-s)) (s * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have := (hasDerivAt_cpow_neg s (lt_of_lt_of_le one_pos ht.1)).neg
      exact this.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((hc1.const_smul s).intervalIntegrable_of_Icc hx)]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    ring
  have hxx : (x : ℂ) ^ (-s) * (x : ℂ) = (x : ℂ) ^ (1 - s) := by
    conv_rhs => rw [show 1 - s = -s + 1 by ring]
    rw [Complex.cpow_add _ _ (by exact_mod_cast hx0.ne'), Complex.cpow_one]
  have hsum : rightPowerSum s x = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k := by
    unfold rightPowerSum; simp [hf]
  rw [hsum, habel, natFloor_eq_bernoulli hx0.le, hJ0]
  simp only [hf]
  have key : s / 2 * ∫ t in Ioc 1 x, (t : ℂ) ^ (-s - 1) = (1 - (x : ℂ) ^ (-s)) / 2 := by
    rw [← hJ1]; ring
  rw [key]
  field_simp
  linear_combination (1 - s) * 2 * hxx

/-! ### Step 2: the Euler–Maclaurin continuation of ζ to Re s > 0 -/

/-- ∫_(1,∞) B₁({t}) t^(-s-1) dt. -/
def zetaBernoulliIntegral (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1)

lemma integrableOn_bounded_mul_cpow {P : ℝ → ℝ} (hP : Measurable P) (hPb : ∀ t, |P t| ≤ 1)
    {w : ℂ} (hw : w.re < -1) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (P t : ℂ) * (t : ℂ) ^ w) (Ioi a) := by
  refine (integrableOn_Ioi_rpow_of_lt hw ha).mono'
    ((Complex.measurable_ofReal.comp hP).mul (measurable_cpow_real w)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans ht)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (ha.trans ht).le _) (hPb t)

lemma tendsto_natCast_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun N : ℕ => (((N : ℝ)) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply, neg_neg]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]

lemma rightPowerSum_natCast_eq_range {s : ℂ} (hs0 : s ≠ 0) (N : ℕ) :
    rightPowerSum s (N : ℝ) = ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s := by
  unfold rightPowerSum
  rw [Nat.floor_natCast, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.Ico_add_one_right_eq_Icc]
  simp only [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Complex.cpow_neg, one_div]

/-- On Re s > 1 the continuation formula is the limit of the finite identity. -/
lemma zeta_eq_bernoulli_of_one_lt {s : ℂ} (h : 1 < s.re) :
    riemannZeta s = s / (s - 1) - 1 / 2 - s * zetaBernoulliIntegral s := by
  have hs1 : s ≠ 1 := fun e => by rw [e] at h; simp at h
  have hs0 : s ≠ 0 := fun e => by rw [e] at h; norm_num at h
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsum : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow h]
    exact (Complex.summable_one_div_nat_cpow.mpr h).hasSum
  have hL : Tendsto (fun N : ℕ => rightPowerSum s (N : ℝ)) atTop (𝓝 (riemannZeta s)) := by
    have := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun N => ?_)
    simp only [Function.comp_apply]
    rw [rightPowerSum_natCast_eq_range hs0]
  have hint : IntegrableOn (fun t : ℝ => (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_bounded_mul_cpow measurable_bernoulliOneRight abs_bernoulliOneRight_le
      (by simp; linarith) one_pos
  have hI := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop
  have h1 := tendsto_natCast_cpow_zero (c := 1 - s) (by simp; linarith)
  have h2 := tendsto_natCast_cpow_zero (c := -s) (by simp; linarith)
  have hR : Tendsto (fun N : ℕ => (((N : ℝ)) : ℂ) ^ (1 - s) / (1 - s) - s / (1 - s) - 1 / 2 -
      (-(1 / 2) : ℂ) * (((N : ℝ)) : ℂ) ^ (-s) -
        s * ∫ t in (1 : ℝ)..N, (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1)) atTop
      (𝓝 (0 / (1 - s) - s / (1 - s) - 1 / 2 - (-(1 / 2) : ℂ) * 0 - s * zetaBernoulliIntegral s)) :=
    ((((h1.div_const _).sub tendsto_const_nhds).sub tendsto_const_nhds).sub
      (h2.const_mul _)).sub (hI.const_mul _)
  have heq : ∀ᶠ N : ℕ in atTop, rightPowerSum s (N : ℝ) =
      (((N : ℝ)) : ℂ) ^ (1 - s) / (1 - s) - s / (1 - s) - 1 / 2 -
        (-(1 / 2) : ℂ) * (((N : ℝ)) : ℂ) ^ (-s) -
          s * ∫ t in (1 : ℝ)..N, (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [rightPowerSum_abel hs1 hN', intervalIntegral.integral_of_le hN']
    have hB : bernoulliOneRight (N : ℝ) = -(1 / 2) := by
      unfold bernoulliOneRight; rw [Int.fract_natCast]; ring
    rw [hB]; push_cast; ring
  have := tendsto_nhds_unique hL (hR.congr' (heq.mono fun N hN => hN.symm))
  rw [this]
  field_simp
  ring

/-- The Bernoulli integral is a Mellin transform, holomorphic on Re s > 0. -/
lemma differentiableAt_zetaBernoulliIntegral {s : ℂ} (h0 : 0 < s.re) :
    DifferentiableAt ℂ zetaBernoulliIntegral s := by
  set g : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => (bernoulliOneRight t : ℂ)) with hg
  have hgm : Measurable g :=
    (Complex.measurable_ofReal.comp measurable_bernoulliOneRight).indicator measurableSet_Ioi
  have hgb : ∀ t, ‖g t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [hg, Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs]
      exact abs_bernoulliOneRight_le t
    · rw [hg, Set.indicator_of_notMem ht, norm_zero]; exact zero_le_one
  have heq : zetaBernoulliIntegral = fun z => mellin g (-z) := by
    funext z
    unfold zetaBernoulliIntegral mellin
    have hpt : (fun t : ℝ => (t : ℂ) ^ (-z - 1) • g t) =
        (Ioi (1 : ℝ)).indicator (fun t => (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · rw [hg, Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
      · rw [hg, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [hpt, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right zero_le_one]
  rw [heq]
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    refine (locallyIntegrable_iff.mpr (fun K hK => ?_)).locallyIntegrableOn _
    exact Measure.integrableOn_of_bounded (M := 1) hK.measure_lt_top.ne hgm.aestronglyMeasurable
      (Eventually.of_forall (fun t => hgb t))
  have htop : g =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) :=
    Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall (fun x => by
      simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]; exact hgb x))
  have hbot : g =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-((-s).re - 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx
    rw [hg, Set.indicator_of_notMem (fun h : x ∈ Ioi (1 : ℝ) => by
      simp only [mem_Ioi] at h; linarith [hx.2]), norm_zero, zero_mul]
  have hM := mellin_differentiableAt_of_isBigO_rpow (s := -s) (a := 0) (b := (-s).re - 1) hloc htop
    (by simp; linarith) hbot (by linarith)
  exact hM.comp s differentiableAt_id.neg

/-- The continuation domain: Re z > 0 minus the ray [1, ∞). It is star-convex about 1/2. -/
def zetaContinuationDomain : Set ℂ := {z | 0 < z.re ∧ (z.im ≠ 0 ∨ z.re < 1)}

lemma isOpen_zetaContinuationDomain : IsOpen zetaContinuationDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_compl_singleton.preimage Complex.continuous_im).union
      (isOpen_lt Complex.continuous_re continuous_const))

lemma starConvex_zetaContinuationDomain : StarConvex ℝ (1 / 2 : ℂ) zetaContinuationDomain := by
  intro y hy a b ha hb hab
  obtain ⟨hy0, hy1⟩ := hy
  have hre : (a • (1 / 2 : ℂ) + b • y).re = a / 2 + b * y.re := by simp; ring
  have him : (a • (1 / 2 : ℂ) + b • y).im = b * y.im := by simp
  refine ⟨?_, ?_⟩
  · rw [hre]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0] at hab ⊢; simp at hab; rw [hab]; norm_num
    · nlinarith
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · right; rw [hre, ← hb0]; rw [← hb0] at hab; simp at hab; rw [hab]; norm_num
    · rcases hy1 with h | h
      · left; rw [him]; exact mul_ne_zero hb0.ne' h
      · right; rw [hre]; nlinarith

lemma ne_one_of_mem_zetaContinuationDomain {z : ℂ} (hz : z ∈ zetaContinuationDomain) : z ≠ 1 := by
  rintro rfl; rcases hz.2 with h | h <;> simp at h

/-- The Euler–Maclaurin continuation: ζ(s) = s/(s-1) - 1/2 - s ∫_1^∞ B₁({t}) t^(-s-1) dt
for every Re s > 0, s ≠ 1. -/
theorem zeta_eq_bernoulli {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - 1 / 2 - s * zetaBernoulliIntegral s := by
  by_cases hU : s ∈ zetaContinuationDomain
  · set G : ℂ → ℂ := fun z => z / (z - 1) - 1 / 2 - z * zetaBernoulliIntegral z with hG
    have hf : AnalyticOnNhd ℂ riemannZeta zetaContinuationDomain :=
      DifferentiableOn.analyticOnNhd (fun z hz =>
        (differentiableAt_riemannZeta (ne_one_of_mem_zetaContinuationDomain hz)).differentiableWithinAt)
        isOpen_zetaContinuationDomain
    have hGa : AnalyticOnNhd ℂ G zetaContinuationDomain := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_zetaContinuationDomain
      have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_zetaContinuationDomain hz)
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => w / (w - 1)) z :=
        DifferentiableAt.div differentiableAt_id (differentiableAt_id.sub_const (1 : ℂ)) hz1
      have hd2 : DifferentiableAt ℂ (fun w : ℂ => w * zetaBernoulliIntegral w) z :=
        differentiableAt_id.mul (differentiableAt_zetaBernoulliIntegral hz.1)
      exact ((hd1.sub_const (1 / 2 : ℂ)).sub hd2).differentiableWithinAt
    have hpre : IsPreconnected zetaContinuationDomain :=
      (starConvex_zetaContinuationDomain.isPathConnected ⟨by norm_num, Or.inr (by norm_num)⟩).isConnected.isPreconnected
    have hz0 : (2 + I : ℂ) ∈ zetaContinuationDomain := ⟨by simp, Or.inl (by simp)⟩
    have hev : riemannZeta =ᶠ[𝓝 (2 + I)] G := by
      have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 + I : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hmem] with z hz
      exact zeta_eq_bernoulli_of_one_lt hz
    exact hf.eqOn_of_preconnected_of_eventuallyEq hGa hpre hz0 hev hU
  · have him : s.im = 0 := by
      by_contra h; exact hU ⟨h0, Or.inl h⟩
    have hre : 1 ≤ s.re := by
      by_contra h; exact hU ⟨h0, Or.inr (lt_of_not_ge h)⟩
    have hre' : 1 < s.re := by
      rcases eq_or_lt_of_le hre with e | e
      · exact absurd (Complex.ext (by simp [← e]) (by simp [him])) h1
      · exact e
    exact zeta_eq_bernoulli_of_one_lt hre'

/-! ### Step 3: integration by parts with the periodic Bernoulli functions -/

/-- ∫_(x,∞) P(t) t^w dt = -Q(x) x^w - w ∫_(x,∞) Q(t) t^(w-1) dt when Q is continuous with right
derivative P, both bounded by 1, and Re w < -1. -/
lemma integral_Ioi_parts {P Q : ℝ → ℝ} (hP : Measurable P) (hPb : ∀ t, |P t| ≤ 1)
    (hQc : Continuous Q) (hQb : ∀ t, |Q t| ≤ 1) (hQd : ∀ t, HasDerivWithinAt Q (P t) (Ioi t) t)
    {w : ℂ} (hw : w.re < -1) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, (P t : ℂ) * (t : ℂ) ^ w =
      -(Q x : ℂ) * (x : ℂ) ^ w - w * ∫ t in Ioi x, (Q t : ℂ) * (t : ℂ) ^ (w - 1) := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
  have hIP := integrableOn_bounded_mul_cpow hP hPb hw hx
  have hIQ := integrableOn_bounded_mul_cpow hQc.measurable hQb (w := w - 1) (by simp; linarith) hx
  set F : ℝ → ℂ := fun t => (Q t : ℂ) * (t : ℂ) ^ w with hF
  have hFTC : ∀ M : ℝ, x ≤ M → ∫ t in x..M, ((P t : ℂ) * (t : ℂ) ^ w + w * ((Q t : ℂ) * (t : ℂ) ^ (w - 1))) =
      F M - F x := by
    intro M hM
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hM ?_ (fun t ht => ?_) ?_
    · exact ((Complex.continuous_ofReal.comp hQc).continuousOn).mul
        ((continuousOn_cpow_Ici w hx).mono Icc_subset_Ici_self)
    · have ht0 : 0 < t := hx.trans ht.1
      have h1 := (hQd t).ofReal_comp
      have h2 := (hasDerivAt_ofReal_cpow_const ht0.ne' hw0).hasDerivWithinAt (s := Ioi t)
      exact (h1.mul h2).congr_deriv (by ring)
    · refine (IntegrableOn.intervalIntegrable ?_)
      rw [Set.uIcc_of_le hM]
      exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (hIP.add (hIQ.const_mul w))).mono_set
        Icc_subset_Ici_self
  have hlim1 := intervalIntegral_tendsto_integral_Ioi x hIP tendsto_id
  have hlim2 := intervalIntegral_tendsto_integral_Ioi x hIQ tendsto_id
  have hFlim : Tendsto F atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := tendsto_rpow_neg_atTop (y := -w.re) (by linarith)
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ h
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [hF]; simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hM,
      neg_neg]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hM.le _) (hQb M)
  have hcomb : Tendsto (fun M : ℝ => F M - F x - w * ∫ t in x..M, (Q t : ℂ) * (t : ℂ) ^ (w - 1))
      atTop (𝓝 (0 - F x - w * ∫ t in Ioi x, (Q t : ℂ) * (t : ℂ) ^ (w - 1))) :=
    (hFlim.sub tendsto_const_nhds).sub (hlim2.const_mul w)
  have heq : ∀ᶠ M in atTop, ∫ t in x..M, (P t : ℂ) * (t : ℂ) ^ w =
      F M - F x - w * ∫ t in x..M, (Q t : ℂ) * (t : ℂ) ^ (w - 1) := by
    filter_upwards [eventually_ge_atTop x] with M hM
    have hi1 : IntervalIntegrable (fun t => (P t : ℂ) * (t : ℂ) ^ w) volume x M := by
      refine IntegrableOn.intervalIntegrable ?_; rw [Set.uIcc_of_le hM]
      exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hIP).mono_set Icc_subset_Ici_self
    have hi2 : IntervalIntegrable (fun t => w * ((Q t : ℂ) * (t : ℂ) ^ (w - 1))) volume x M := by
      refine IntegrableOn.intervalIntegrable ?_; rw [Set.uIcc_of_le hM]
      exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (hIQ.const_mul w)).mono_set
        Icc_subset_Ici_self
    rw [← hFTC M hM, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul]
    ring
  have := tendsto_nhds_unique hlim1 (hcomb.congr' (heq.mono fun M hM => hM.symm))
  rw [this, hF]
  ring

/-! ### Step 4: the second-order expansion and the uniform remainder -/

/-- The remainder of the second-order expansion, written with B₃({x}). -/
def eulerMaclaurinRemainder (s : ℂ) (x : ℝ) : ℂ :=
  -(s * (s + 1) / 6) * (bernoulliThree x : ℂ) * (x : ℂ) ^ (-s - 2) +
    s * (s + 1) * (s + 2) / 6 * ∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)

lemma abs_bernoulliTwo_half_le (t : ℝ) : |bernoulliTwo t / 2| ≤ 1 := by
  rw [abs_div, abs_two]; linarith [abs_bernoulliTwo_le t]

lemma abs_bernoulliThree_third_le (t : ℝ) : |bernoulliThree t / 3| ≤ 1 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith [abs_bernoulliThree_le t]

/-- The exact second-order expansion with the B₃ remainder, for Re s > 0, s ≠ 1 and x ≥ 1. -/
theorem rightPowerSum_expansion {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hIB1 := integrableOn_bounded_mul_cpow measurable_bernoulliOneRight abs_bernoulliOneRight_le
    (w := -s - 1) (by simp; linarith) one_pos
  have hsplit : zetaBernoulliIntegral s =
      (∫ t in Ioc 1 x, (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1)) +
        ∫ t in Ioi x, (bernoulliOneRight t : ℂ) * (t : ℂ) ^ (-s - 1) := by
    unfold zetaBernoulliIntegral
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx]
    exact setIntegral_union (Set.disjoint_left.mpr (fun t h1 h2 => by
        simp only [mem_Ioc, mem_Ioi] at h1 h2; linarith)) measurableSet_Ioi
      (hIB1.mono_set (Set.Ioc_subset_Ioi_self)) (hIB1.mono_set (Ioi_subset_Ioi hx))
  have hp1 := integral_Ioi_parts (P := bernoulliOneRight) (Q := fun y => bernoulliTwo y / 2)
    measurable_bernoulliOneRight abs_bernoulliOneRight_le (continuous_bernoulliTwo.div_const 2)
    abs_bernoulliTwo_half_le hasDerivWithinAt_bernoulliTwo_half (w := -s - 1)
    (by simp; linarith) hx0
  have hp2 := integral_Ioi_parts (P := bernoulliTwo) (Q := fun y => bernoulliThree y / 3)
    measurable_bernoulliTwo abs_bernoulliTwo_le (continuous_bernoulliThree.div_const 3)
    abs_bernoulliThree_third_le hasDerivWithinAt_bernoulliThree_third (w := -s - 2)
    (by simp; linarith) hx0
  have e1 : (∫ t in Ioi x, ((bernoulliTwo t / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1 - 1)) =
      (∫ t in Ioi x, (bernoulliTwo t : ℂ) * (t : ℂ) ^ (-s - 2)) / 2 := by
    rw [← integral_div]; congr 1; funext t; rw [show -s - 1 - 1 = -s - 2 by ring]; push_cast; ring
  have e2 : (∫ t in Ioi x, ((bernoulliThree t / 3 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2 - 1)) =
      (∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)) / 3 := by
    rw [← integral_div]; congr 1; funext t; rw [show -s - 2 - 1 = -s - 3 by ring]; push_cast; ring
  rw [e1] at hp1
  rw [e2] at hp2
  push_cast at hp1 hp2
  have hFI := rightPowerSum_abel h1 hx
  have hz := zeta_eq_bernoulli h0 h1
  rw [hsplit] at hz
  have hneg : s / (s - 1) + s / (1 - s) = 0 := by
    rw [show s - 1 = -(1 - s) by ring, div_neg]; ring
  unfold eulerMaclaurinRemainder
  linear_combination hFI - hz + s * hp1 + (s * (s + 1) / 2) * hp2 - hneg

/-- The remainder bound: ‖R(s, x)‖ ≤ C(‖s‖) x^(-Re s - 2) on x > 0, Re s > 0. -/
theorem eulerMaclaurinRemainder_norm_le {s : ℂ} (h0 : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖eulerMaclaurinRemainder s x‖ ≤
      (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 2) := by
  have hpow : ‖(x : ℂ) ^ (-s - 2)‖ = x ^ (-s.re - 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hb : 0 ≤ x ^ (-s.re - 2) := Real.rpow_nonneg hx.le _
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s.re - 3)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hx
  have hI : ‖∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)‖ ≤ x ^ (-s.re - 2) / 2 := by
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun t ht => ?_)))).trans ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans ht)]
      have : (-s - 3).re = -s.re - 3 := by simp
      rw [this]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (hx.trans ht).le _) (abs_bernoulliThree_le t)
    · rw [integral_Ioi_rpow_of_lt (by linarith) hx, show -s.re - 3 + 1 = -s.re - 2 by ring]
      have he : -x ^ (-s.re - 2) / (-s.re - 2) = x ^ (-s.re - 2) / (s.re + 2) := by
        rw [show -s.re - 2 = -(s.re + 2) by ring, div_neg, neg_div, neg_neg]
      rw [he]
      exact div_le_div_of_nonneg_left hb (by norm_num) (by linarith)
  have hs1 : ‖s * (s + 1) / 6‖ ≤ ‖s‖ * (‖s‖ + 1) / 6 := by
    rw [norm_div, norm_mul]
    have : ‖(6 : ℂ)‖ = 6 := by simp
    rw [this]
    gcongr
    exact (norm_add_le _ _).trans (by simp)
  have hs2 : ‖s * (s + 1) * (s + 2) / 6‖ ≤ ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 6 := by
    rw [norm_div, norm_mul, norm_mul]
    have : ‖(6 : ℂ)‖ = 6 := by simp
    rw [this]
    gcongr
    · exact (norm_add_le _ _).trans (by simp)
    · exact (norm_add_le _ _).trans (by simp)
  have hB3 : ‖(bernoulliThree x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bernoulliThree_le x
  unfold eulerMaclaurinRemainder
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg, norm_mul, hpow]
  have h6 : 0 ≤ ‖s‖ * (‖s‖ + 1) / 6 := by positivity
  calc ‖s * (s + 1) / 6‖ * ‖(bernoulliThree x : ℂ)‖ * x ^ (-s.re - 2) +
        ‖s * (s + 1) * (s + 2) / 6‖ * ‖∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)‖
      ≤ ‖s‖ * (‖s‖ + 1) / 6 * 1 * x ^ (-s.re - 2) +
        ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 6 * (x ^ (-s.re - 2) / 2) := by
        gcongr
    _ = (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 2) := by ring

/-! ### Cell structure: right endpoint convention and differentiated finite sums -/

lemma natFloor_eq_of_mem_cell {n : ℕ} {y : ℝ} (hy : y ∈ Ico (n : ℝ) (n + 1)) : ⌊y⌋₊ = n :=
  Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) hy.1) |>.mpr hy

lemma fract_eq_of_mem_cell {n : ℕ} {y : ℝ} (hy : y ∈ Ico (n : ℝ) (n + 1)) : Int.fract y = y - n := by
  have h : ⌊y⌋ = (n : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
  rw [Int.fract, h]; simp

/-- The finite sum is constant on every right-closed cell `[n, n + 1)`: the right integer endpoint
is included. -/
lemma rightPowerSum_of_mem_cell (s : ℂ) {n : ℕ} {y : ℝ} (hy : y ∈ Ico (n : ℝ) (n + 1)) :
    rightPowerSum s y = ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-s) := by
  rw [rightPowerSum, natFloor_eq_of_mem_cell hy]

lemma hasDerivAt_rightPowerSum_cell (s : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    HasDerivAt (rightPowerSum s) 0 x := by
  refine (hasDerivAt_const x (∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-s))).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact rightPowerSum_of_mem_cell s (Ioo_subset_Ico_self hy)

lemma hasDerivAt_bernoulliThree_cell {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    HasDerivAt bernoulliThree (3 * bernoulliTwo x) x := by
  have hpoly : HasDerivAt (fun y : ℝ => (y - n) ^ 3 - 3 / 2 * (y - n) ^ 2 + 1 / 2 * (y - n))
      (3 * ((x - n) ^ 2 - (x - n) + 1 / 6)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - n) 1 x := (hasDerivAt_id x).sub_const _
    have h3 : HasDerivAt (fun y : ℝ => (y - n) ^ 3) (3 * (x - n) ^ 2) x := by
      simpa using h1.fun_pow 3
    have h2 : HasDerivAt (fun y : ℝ => (y - n) ^ 2) (2 * (x - n)) x := by
      simpa using h1.fun_pow 2
    exact ((h3.sub (h2.const_mul (3 / 2))).add (h1.const_mul (1 / 2))).congr_deriv (by ring)
  rw [bernoulliTwo, fract_eq_of_mem_cell (Ioo_subset_Ico_self hx)]
  refine hpoly.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [bernoulliThree, fract_eq_of_mem_cell (Ioo_subset_Ico_self hy)]

lemma hasDerivAt_integral_Ioi_tail {f : ℝ → ℂ} {a x : ℝ} (hax : a < x)
    (hf : IntegrableOn f (Ioi a)) (hfc : ContinuousOn f (Ioi a)) :
    HasDerivAt (fun y => ∫ t in Ioi y, f t) (-f x) x := by
  have hloc : ∀ y, a < y → (∫ t in Ioi y, f t) = (∫ t in Ioi a, f t) - ∫ t in a..y, f t := by
    intro y hy
    rw [intervalIntegral.integral_of_le hy.le, eq_sub_iff_add_eq, add_comm,
      ← setIntegral_union (Set.disjoint_left.mpr (fun t h1 h2 => by
        simp only [mem_Ioc, mem_Ioi] at h1 h2; linarith)) measurableSet_Ioi
        (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hy.le)),
      Ioc_union_Ioi_eq_Ioi hy.le]
  have hFTC : HasDerivAt (fun y => ∫ t in a..y, f t) (f x) x := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le).mpr
        (hf.mono_set Ioc_subset_Ioi_self)
    · exact hfc.stronglyMeasurableAtFilter isOpen_Ioi x hax
    · exact hfc.continuousAt (Ioi_mem_nhds hax)
  refine (hFTC.const_sub (∫ t in Ioi a, f t)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hax] with y hy
  exact hloc y hy

/-- The exact differentiated remainder inside every cell: R'(x) = -(s(s+1)/2) B₂({x}) x^(-s-2). -/
theorem hasDerivAt_eulerMaclaurinRemainder_cell (s : ℂ) (h0 : 0 < s.re) {n : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    HasDerivAt (eulerMaclaurinRemainder s)
      (-(s * (s + 1) / 2) * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 2)) x := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
  have hB3 : HasDerivAt (fun y : ℝ => (bernoulliThree y : ℂ)) ((3 * bernoulliTwo x : ℝ) : ℂ) x :=
    (hasDerivAt_bernoulliThree_cell hx).ofReal_comp
  have hpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 2)) ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x := by
    have h := hasDerivAt_cpow_neg (s + 2) hx0
    rw [show -(s + 2) = -s - 2 by ring] at h
    exact h
  have hf : IntegrableOn (fun t : ℝ => (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)) (Ioi (x / 2)) :=
    integrableOn_bounded_mul_cpow measurable_bernoulliThree abs_bernoulliThree_le
      (by simp; linarith) (by linarith)
  have hfc : ContinuousOn (fun t : ℝ => (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)) (Ioi (x / 2)) :=
    ((Complex.continuous_ofReal.comp continuous_bernoulliThree).continuousOn).mul
      ((continuousOn_cpow_Ici _ (by linarith : (0 : ℝ) < x / 2)).mono Ioi_subset_Ici_self)
  have hT := hasDerivAt_integral_Ioi_tail (a := x / 2) (x := x) (by linarith) hf hfc
  have hall := (((hB3.mul hpow).const_mul (-(s * (s + 1) / 6))).add
    (hT.const_mul (s * (s + 1) * (s + 2) / 6)))
  unfold eulerMaclaurinRemainder
  have hfun : (fun y : ℝ => -(s * (s + 1) / 6) * (bernoulliThree y : ℂ) * (y : ℂ) ^ (-s - 2) +
      s * (s + 1) * (s + 2) / 6 * ∫ t in Ioi y, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3)) =
      fun y => -(s * (s + 1) / 6) * ((bernoulliThree y : ℂ) * (y : ℂ) ^ (-s - 2)) +
        s * (s + 1) * (s + 2) / 6 * ∫ t in Ioi y, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3) := by
    funext y; ring
  have hx3 : (x : ℂ) ^ (-s - 2 - 1) = (x : ℂ) ^ (-s - 3) := by ring_nf
  have hx2 : (x : ℂ) ^ (-s - 2) = (x : ℂ) ^ (-s - 3) * x := by
    rw [show -s - 2 = (-s - 3) + 1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne'), Complex.cpow_one]
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  rw [hfun]
  refine hall.congr_deriv ?_
  rw [hx3, hx2]
  push_cast
  ring

/-- For fixed x ≥ 1 the remainder is holomorphic in the parameter on Re s > 0, s ≠ 1. -/
theorem differentiableOn_eulerMaclaurinRemainder {x : ℝ} (hx : 1 ≤ x) :
    DifferentiableOn ℂ (fun s => eulerMaclaurinRemainder s x) {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hE : ∀ s ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1}, eulerMaclaurinRemainder s x =
      rightPowerSum s x - riemannZeta s - (x : ℂ) ^ (1 - s) / (1 - s) +
        (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) +
          s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 := by
    intro s hs
    rw [rightPowerSum_expansion hs.1 hs.2 hx]; ring
  refine DifferentiableOn.congr (fun s hs => ?_) hE
  have hsum : DifferentiableAt ℂ (fun s => rightPowerSum s x) s := by
    unfold rightPowerSum
    refine DifferentiableAt.fun_sum (fun k hk => ?_)
    have hk1 : (k : ℂ) ≠ 0 := by
      have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      exact_mod_cast (by omega : k ≠ 0)
    exact differentiableAt_id.neg.const_cpow (Or.inl hk1)
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ (1 - s)) s :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl hx0)
  have hd2 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hx0)
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ (-s - 1)) s :=
    (differentiableAt_id.neg.sub (differentiableAt_const _)).const_cpow (Or.inl hx0)
  exact ((((hsum.sub (differentiableAt_riemannZeta hs.2)).sub
    (hd1.div ((differentiableAt_const _).sub differentiableAt_id) hs1)).add
      ((differentiableAt_const _).mul hd2)).add
        (((differentiableAt_id.mul (differentiableAt_const _)).mul hd3).div_const 2)).differentiableWithinAt

/-! ### The root -/

/-- R2-S1a / R2-H1 / F3, finite-sum Euler-Maclaurin expansion (S1.3).

For every complex `s` with `0 < Re s`, `s ≠ 1`, and every real cutoff `x ≥ 1`,
`∑_{1 ≤ n ≤ x} n^(-s) = ζ(s) + x^(1-s)/(1-s) - B₁({x}) x^(-s) - s B₂({x}) x^(-s-1)/2 + R(s,x)`,
with `B₁(u) = u - 1/2` taking its right endpoint value `-1/2` at integers, `B₂(u) = u² - u + 1/6`,
and the explicit remainder `R(s,x)` obtained by one further bounded-periodic integration by parts.
The clauses are:
1. the right integer endpoint convention for the finite sum and the periodic Bernoulli values;
2. the exact expansion;
3. `‖R(s,x)‖ ≤ C(‖s‖) x^(-Re s - 2)` with an explicit polynomial `C`, for all `x > 0`;
4. the locally uniform O-statement on every compact parameter set in the domain;
5. holomorphy of `R(·,x)` in the parameter;
6. the exact differentiated finite sums inside every cell: the finite sum is locally constant and
   `∂ₓR(s,x) = -(s(s+1)/2) B₂({x}) x^(-s-2)`. -/
theorem finite_sum_euler_maclaurin_uniform :
    (∀ (s : ℂ) (n : ℕ) (y : ℝ), y ∈ Ico (n : ℝ) (n + 1) →
      rightPowerSum s y = ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-s)) ∧
    (∀ n : ℕ, bernoulliOneRight n = -1 / 2 ∧ bernoulliTwo n = 1 / 6) ∧
    (∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
        (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
          s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ x : ℝ, 0 < x →
      ‖eulerMaclaurinRemainder s x‖ ≤
        (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 2)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | 0 < s.re ∧ s ≠ 1} → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ K, ∀ x : ℝ, 1 ≤ x →
        ‖rightPowerSum s x - (riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
          (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
            s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2)‖ ≤ C * x ^ (-s.re - 2)) ∧
    (∀ x : ℝ, 1 ≤ x →
      DifferentiableOn ℂ (fun s => eulerMaclaurinRemainder s x) {s : ℂ | 0 < s.re ∧ s ≠ 1}) ∧
    (∀ (s : ℂ) (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → HasDerivAt (rightPowerSum s) 0 x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (eulerMaclaurinRemainder s)
        (-(s * (s + 1) / 2) * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 2)) x) := by
  refine ⟨fun s n y hy => rightPowerSum_of_mem_cell s hy, fun n => ?_,
    fun s h0 h1 x hx => rightPowerSum_expansion h0 h1 hx,
    fun s h0 x hx => eulerMaclaurinRemainder_norm_le h0 hx, fun K hK hKD => ?_,
    fun x hx => differentiableOn_eulerMaclaurinRemainder hx,
    fun s n x hx => hasDerivAt_rightPowerSum_cell s hx,
    fun s h0 n x hx => hasDerivAt_eulerMaclaurinRemainder_cell s h0 hx⟩
  · simp only [bernoulliOneRight, bernoulliTwo, Int.fract_natCast]; norm_num
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    set M' := max M 0
    refine ⟨M' * (M' + 1) / 6 + M' * (M' + 1) * (M' + 2) / 12, by positivity, fun s hs x hx => ?_⟩
    have hsM : ‖s‖ ≤ M' := (hM s hs).trans (le_max_left _ _)
    have hD := hKD hs
    rw [rightPowerSum_expansion hD.1 hD.2 hx, add_sub_cancel_left]
    refine (eulerMaclaurinRemainder_norm_le hD.1 (by linarith)).trans ?_
    have hb : 0 ≤ x ^ (-s.re - 2) := Real.rpow_nonneg (by linarith) _
    gcongr

end Zeta23.OPICAFollowup
