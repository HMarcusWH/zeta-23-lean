import Zeta23.CCM.DictionaryArchSourceBridge
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped FourierTransform Interval


/-! # Diagonal archimedean entry

This first gate derives the quarter-digamma value and the exact `mu 0`
normalization from pinned Mathlib reflection and duplication formulas.
-/


/-! ## The quarter-digamma value -/

private theorem differentiableAt_Gamma_of_re_pos
    {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private theorem logDeriv_Gamma_comp_one_sub (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.Gamma (1 - w)) z =
      -Complex.digamma (1 - z) := by
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply,
    deriv_comp_const_sub]
  ring

private theorem logDeriv_Gamma_comp_add_half (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z =
      Complex.digamma (z + 1 / 2) := by
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply,
    deriv_comp_add_const]

private theorem logDeriv_Gamma_comp_two_mul (z : ℂ)
    (hz : DifferentiableAt ℂ Complex.Gamma (2 * z)) :
    logDeriv (fun w : ℂ => Complex.Gamma (2 * w)) z =
      2 * Complex.digamma (2 * z) := by
  have h := logDeriv_comp
    (f := Complex.Gamma) (g := fun w : ℂ => 2 * w) (x := z)
    hz (by fun_prop)
  rw [show (Complex.Gamma ∘ fun w : ℂ => 2 * w) =
      (fun w : ℂ => Complex.Gamma (2 * w)) from rfl,
    ← Complex.digamma_def, deriv_const_mul_id] at h
  linear_combination h

private theorem logDeriv_sin_pi_mul (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z =
      Complex.cot ((Real.pi : ℂ) * z) * (Real.pi : ℂ) := by
  have h := logDeriv_comp
    (f := Complex.sin) (g := fun w : ℂ => (Real.pi : ℂ) * w) (x := z)
    Complex.differentiableAt_sin (by fun_prop)
  rw [show (Complex.sin ∘ fun w : ℂ => (Real.pi : ℂ) * w) =
      (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) from rfl,
    Complex.logDeriv_sin, deriv_const_mul_id] at h
  exact h

private theorem complex_cot_pi_div_four :
    Complex.cot (((Real.pi / 4 : ℝ) : ℂ)) = 1 := by
  calc
    Complex.cot (((Real.pi / 4 : ℝ) : ℂ)) =
        ((Real.cot (Real.pi / 4) : ℝ) : ℂ) :=
      (Complex.ofReal_cot (Real.pi / 4)).symm
    _ = 1 := by
      rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_four,
        Real.sin_pi_div_four, div_self (by positivity)]
      norm_num

private theorem complex_sin_pi_div_four_ne_zero :
    Complex.sin (((Real.pi / 4 : ℝ) : ℂ)) ≠ 0 := by
  rw [← Complex.ofReal_sin, Complex.ofReal_ne_zero]
  rw [Real.sin_pi_div_four]
  positivity

private theorem digamma_quarter_sub_three_quarters :
    Complex.digamma (1 / 4) - Complex.digamma (3 / 4) =
      -(Real.pi : ℂ) := by
  let q : ℂ := 1 / 4
  have hqre : 0 < q.re := by simp [q]
  have h1qre : 0 < (1 - q).re := by norm_num [q]
  have hGq : Complex.Gamma q ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hqre
  have hG1q : Complex.Gamma (1 - q) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1qre
  have hdGq : DifferentiableAt ℂ Complex.Gamma q :=
    differentiableAt_Gamma_of_re_pos hqre
  have hdG1q : DifferentiableAt ℂ Complex.Gamma (1 - q) :=
    differentiableAt_Gamma_of_re_pos h1qre
  have hdComp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 - z)) q :=
    hdG1q.comp q (by fun_prop)
  have hleft :
      logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) q =
        Complex.digamma q - Complex.digamma (1 - q) := by
    rw [logDeriv_mul q hGq hG1q hdGq hdComp,
      show logDeriv Complex.Gamma q = Complex.digamma q from rfl,
      logDeriv_Gamma_comp_one_sub]
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * q) ≠ 0 := by
    rw [show (Real.pi : ℂ) * q = (((Real.pi / 4 : ℝ) : ℂ)) by
      simp [q]
      push_cast
      ring]
    exact complex_sin_pi_div_four_ne_zero
  have hright :
      logDeriv
          (fun z : ℂ => (Real.pi : ℂ) /
            Complex.sin ((Real.pi : ℂ) * z)) q =
        -(Real.pi : ℂ) := by
    rw [logDeriv_div q (by exact_mod_cast Real.pi_ne_zero) hsin
      (by fun_prop) (by fun_prop), logDeriv_sin_pi_mul]
    simp only [logDeriv_const, Pi.zero_apply, zero_sub]
    rw [show (Real.pi : ℂ) * q = (((Real.pi / 4 : ℝ) : ℂ)) by
      simp [q]
      push_cast
      ring, complex_cot_pi_div_four]
    ring
  have hfun :
      (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
        fun z : ℂ => (Real.pi : ℂ) /
          Complex.sin ((Real.pi : ℂ) * z) := by
    funext z
    exact Complex.Gamma_mul_Gamma_one_sub z
  have heq := congrArg (fun f : ℂ → ℂ => logDeriv f q) hfun
  rw [hleft, hright] at heq
  convert heq using 1 <;> norm_num [q]

private theorem logDeriv_two_cpow_one_sub_two_mul (z : ℂ) :
    logDeriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z =
      -2 * Complex.log 2 := by
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * w) z := by
    fun_prop
  have hp : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [logDeriv_apply, Complex.deriv_const_cpow hd]
  have hlin : deriv (fun w : ℂ => 1 - 2 * w) z = -2 := by
    rw [deriv_const_sub, deriv_const_mul_id]
  rw [hlin]
  field_simp [hp]

private theorem digamma_quarter_add_three_quarters :
    Complex.digamma (1 / 4) + Complex.digamma (3 / 4) =
      2 * Complex.digamma (1 / 2) - 2 * Complex.log 2 := by
  let q : ℂ := 1 / 4
  have hqre : 0 < q.re := by simp [q]
  have h3qre : 0 < (q + 1 / 2).re := by norm_num [q]
  have h2qre : 0 < (2 * q).re := by simp [q]
  have hGq : Complex.Gamma q ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hqre
  have hG3q : Complex.Gamma (q + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h3qre
  have hG2q : Complex.Gamma (2 * q) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h2qre
  have hdGq : DifferentiableAt ℂ Complex.Gamma q :=
    differentiableAt_Gamma_of_re_pos hqre
  have hdG3q : DifferentiableAt ℂ Complex.Gamma (q + 1 / 2) :=
    differentiableAt_Gamma_of_re_pos h3qre
  have hdG2q : DifferentiableAt ℂ Complex.Gamma (2 * q) :=
    differentiableAt_Gamma_of_re_pos h2qre
  have hdComp3q : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z + 1 / 2)) q :=
    hdG3q.comp q (by fun_prop)
  have hdComp2q : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (2 * z)) q :=
    hdG2q.comp q (by fun_prop)
  have hp : (2 : ℂ) ^ (1 - 2 * q) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hdp : DifferentiableAt ℂ
      (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) q :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hleft :
      logDeriv
          (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) q =
        Complex.digamma q + Complex.digamma (q + 1 / 2) := by
    rw [logDeriv_mul q hGq hG3q hdGq hdComp3q,
      show logDeriv Complex.Gamma q = Complex.digamma q from rfl,
      logDeriv_Gamma_comp_add_half]
  have hright :
      logDeriv
          (fun z : ℂ => Complex.Gamma (2 * z) *
            (2 : ℂ) ^ (1 - 2 * z) * ((Real.sqrt Real.pi : ℝ) : ℂ)) q =
        2 * Complex.digamma (2 * q) - 2 * Complex.log 2 := by
    rw [logDeriv_mul_const q ((Real.sqrt Real.pi : ℝ) : ℂ) hsqrt,
      logDeriv_mul q hG2q hp hdComp2q hdp,
      logDeriv_Gamma_comp_two_mul q hdG2q,
      logDeriv_two_cpow_one_sub_two_mul]
    ring
  have hfun :
      (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) =
        fun z : ℂ => Complex.Gamma (2 * z) *
          (2 : ℂ) ^ (1 - 2 * z) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    funext z
    exact Complex.Gamma_mul_Gamma_add_half z
  have heq := congrArg (fun f : ℂ → ℂ => logDeriv f q) hfun
  rw [hleft, hright] at heq
  convert heq using 1 <;> norm_num [q]

/-- The only special value not already present in pinned Mathlib that Phase F needs.
It is derived from reflection and duplication, not postulated. -/
theorem digamma_one_quarter :
    Complex.digamma (1 / 4) =
      -(Real.eulerMascheroniConstant : ℂ) - (Real.pi : ℂ) / 2 -
        3 * Complex.log 2 := by
  have hsub := digamma_quarter_sub_three_quarters
  have hadd := digamma_quarter_add_three_quarters
  calc
    Complex.digamma (1 / 4) =
        ((Complex.digamma (1 / 4) + Complex.digamma (3 / 4)) +
          (Complex.digamma (1 / 4) - Complex.digamma (3 / 4))) / 2 := by ring
    _ = ((2 * Complex.digamma (1 / 2) - 2 * Complex.log 2) -
          (Real.pi : ℂ)) / 2 := by
      rw [hadd, hsub]
      ring
    _ = -(Real.eulerMascheroniConstant : ℂ) - (Real.pi : ℂ) / 2 -
          3 * Complex.log 2 := by
      rw [Complex.digamma_one_half]
      ring

theorem two_pi_mul_mu_zero :
    2 * Real.pi * Zeta23.mu 0 =
      -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 -
        Real.log Real.pi := by
  have hq := congrArg Complex.re digamma_one_quarter
  have hlogTwo : (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  norm_num [Complex.div_re, hlogTwo] at hq
  rw [Zeta23.mu]
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [hq]
  field_simp [Real.pi_ne_zero]

/-! ## The two elementary finite-part integrals -/

private def archReferencePrimitive (x : ℝ) : ℝ :=
  let t := Real.exp (-x / 2)
  (-Real.log (1 + t) - Real.arctan t + (1 / 2) * Real.log (1 + t ^ 2))

private theorem archDensity_eq_exp_neg_half_div_one_sub_pow_four
    {x : ℝ} (hx : 0 < x) :
    archDensity x =
      Real.exp (-x / 2) / (1 - Real.exp (-x / 2) ^ 4) := by
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  have htlt : Real.exp (-x / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have ht4 : Real.exp (-x / 2) ^ 4 < 1 := by
    have ht0 : 0 ≤ Real.exp (-x / 2) := (Real.exp_pos _).le
    nlinarith [sq_nonneg (Real.exp (-x / 2)),
      mul_self_lt_mul_self (Real.exp_pos _).le htlt]
  have hgeom : 1 - Real.exp (-x / 2) ^ 4 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt ht4).symm
  unfold archDensity
  apply (div_eq_div_iff hden hgeom).2
  simp only [mul_sub, mul_one, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1 <;> ring

private theorem hasDerivAt_archReferencePrimitive
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt archReferencePrimitive
      ((1 - Real.exp (-x / 2)) * archDensity x) x := by
  let t : ℝ := Real.exp (-x / 2)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htlt : t < 1 := by
    dsimp [t]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have ht : HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (-t / 2) x := by
    convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;>
      simp [t] <;> ring
  have h1t : 1 + t ≠ 0 := by positivity
  have h1t2 : 1 + t ^ 2 ≠ 0 := by positivity
  have hlogOne : HasDerivAt
      (fun y : ℝ => Real.log (1 + Real.exp (-y / 2)))
      ((-t / 2) / (1 + t)) x := by
    simpa [t] using ((hasDerivAt_const x 1).add ht).log h1t
  have hatan : HasDerivAt
      (fun y : ℝ => Real.arctan (Real.exp (-y / 2)))
      ((1 / (1 + t ^ 2)) * (-t / 2)) x := by
    simpa [t] using ht.arctan
  have htSq := ht.pow 2
  have hlogSq : HasDerivAt
      (fun y : ℝ => Real.log (1 + Real.exp (-y / 2) ^ 2))
      ((2 * t * (-t / 2)) / (1 + t ^ 2)) x := by
    convert ((hasDerivAt_const x 1).add htSq).log h1t2 using 1 <;>
      simp [t] <;> ring
  unfold archReferencePrimitive
  dsimp only
  refine ((hlogOne.neg.sub hatan).add (hlogSq.const_mul (1 / 2))).congr_deriv ?_
  rw [archDensity_eq_exp_neg_half_div_one_sub_pow_four hx]
  change
    -((-t / 2) / (1 + t)) - (1 / (1 + t ^ 2)) * (-t / 2) +
        (1 / 2) * ((2 * t * (-t / 2)) / (1 + t ^ 2)) =
      (1 - t) * (t / (1 - t ^ 4))
  have h1 : 1 + t ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  have h4 : 1 - t ^ 4 ≠ 0 := by
    have ht4 : t ^ 4 < 1 := by
      nlinarith [sq_nonneg t, mul_self_lt_mul_self ht0.le htlt]
    exact sub_ne_zero.mpr (ne_of_lt ht4).symm
  field_simp [h1, h2, h4]
  ring

private theorem continuousWithinAt_archReferencePrimitive_zero :
    ContinuousWithinAt archReferencePrimitive (Ici 0) 0 := by
  apply ContinuousAt.continuousWithinAt
  unfold archReferencePrimitive
  dsimp only
  have hlogOne : 1 + Real.exp (-0 / 2) ≠ 0 := by norm_num
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hlogSq : 1 + Real.exp (-0 / 2) ^ 2 ≠ 0 := by norm_num
  fun_prop

private theorem tendsto_archReferencePrimitive_atTop :
    Tendsto archReferencePrimitive atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (nhds 0) := by
    have hlin : Tendsto (fun x : ℝ => (-1 / 2 : ℝ) * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by norm_num)
    convert Real.tendsto_exp_atBot.comp hlin using 1
    · ext x
      congr 1
      ring
  have hcont : ContinuousAt
      (fun t : ℝ =>
        -Real.log (1 + t) - Real.arctan t + (1 / 2) * Real.log (1 + t ^ 2)) 0 := by
    fun_prop (disch := norm_num)
  have h := hcont.tendsto.comp ht
  norm_num at h
  apply Tendsto.congr' _ h
  filter_upwards with x
  rfl

private theorem archReferenceIntegrand_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤ (1 - Real.exp (-x / 2)) * archDensity x := by
  have he : Real.exp (-x / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hd : 0 < Real.exp x - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  unfold archDensity
  exact mul_nonneg (sub_nonneg.mpr he)
    (div_nonneg (Real.exp_pos _).le hd.le)

theorem integrableOn_one_sub_exp_mul_archDensity_Ioi :
    IntegrableOn
      (fun x : ℝ => (1 - Real.exp (-x / 2)) * archDensity x)
      (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg
    continuousWithinAt_archReferencePrimitive_zero
    (fun x hx => hasDerivAt_archReferencePrimitive hx)
    (fun x hx => archReferenceIntegrand_nonneg hx)
    tendsto_archReferencePrimitive_atTop

theorem integral_one_sub_exp_mul_archDensity_Ioi :
    (∫ x : ℝ in Ioi 0,
      (1 - Real.exp (-x / 2)) * archDensity x) =
        Real.pi / 4 + Real.log 2 / 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    continuousWithinAt_archReferencePrimitive_zero
    (fun x hx => hasDerivAt_archReferencePrimitive hx)
    (fun x hx => archReferenceIntegrand_nonneg hx)
    tendsto_archReferencePrimitive_atTop]
  simp [archReferencePrimitive, Real.arctan_one]
  ring

private def archTailPrimitive (x : ℝ) : ℝ :=
  (-1 / 2) *
    (Real.log (Real.exp x + 1) - Real.log (Real.exp x - 1))

private theorem hasDerivAt_archTailPrimitive
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt archTailPrimitive
      (Real.exp (-x / 2) * archDensity x) x := by
  have hexp : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have hplus : Real.exp x + 1 ≠ 0 := by positivity
  have hminus : Real.exp x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have hlogPlus : HasDerivAt
      (fun y : ℝ => Real.log (Real.exp y + 1))
      (Real.exp x / (Real.exp x + 1)) x := by
    simpa using (hexp.add_const 1).log hplus
  have hlogMinus : HasDerivAt
      (fun y : ℝ => Real.log (Real.exp y - 1))
      (Real.exp x / (Real.exp x - 1)) x := by
    simpa using (hexp.sub_const 1).log hminus
  unfold archTailPrimitive
  refine ((hlogPlus.sub hlogMinus).const_mul (-1 / 2)).congr_deriv ?_
  unfold archDensity
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hhalf : Real.exp (-(x / 2)) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  field_simp [hplus, hminus, hden, Real.exp_ne_zero]
  calc
    -(Real.exp x * (Real.exp x - 1 - (Real.exp x + 1)) *
        (Real.exp x - Real.exp (-x))) =
        2 * (Real.exp x ^ 2 - 1) := by nlinarith [hcancel]
    _ = 2 * (Real.exp x + 1) * (Real.exp x - 1) *
        Real.exp (-(x / 2)) * Real.exp (x / 2) := by
      rw [show 2 * (Real.exp x + 1) * (Real.exp x - 1) *
          Real.exp (-(x / 2)) * Real.exp (x / 2) =
          2 * (Real.exp x + 1) * (Real.exp x - 1) *
            (Real.exp (-(x / 2)) * Real.exp (x / 2)) by ring,
        hhalf]
      ring

private theorem archTailIntegrand_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.exp (-x / 2) * archDensity x := by
  have hd : 0 < Real.exp x - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  unfold archDensity
  positivity

private theorem tendsto_archTailPrimitive_atTop :
    Tendsto archTailPrimitive atTop (nhds 0) := by
  let alt : ℝ → ℝ := fun x =>
    (-1 / 2) * Real.log
      ((1 + Real.exp (-x)) / (1 - Real.exp (-x)))
  have ht : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (nhds 0) := by
    have hlin : Tendsto (fun x : ℝ => (-1 : ℝ) * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by norm_num)
    convert Real.tendsto_exp_atBot.comp hlin using 1
    · ext x
      congr 1
      ring
  have hcont : ContinuousAt
      (fun t : ℝ => (-1 / 2) * Real.log ((1 + t) / (1 - t))) 0 := by
    fun_prop (disch := norm_num)
  have halt : Tendsto alt atTop (nhds 0) := by
    have h := hcont.tendsto.comp ht
    norm_num at h
    apply Tendsto.congr' _ h
    filter_upwards with x
    dsimp only [alt, Function.comp_apply]
    ring
  apply Tendsto.congr' _ halt
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hexp1 : Real.exp x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have hone : 1 - Real.exp (-x) ≠ 0 := by
    exact sub_ne_zero.mpr
      (ne_of_lt (Real.exp_lt_one_iff.mpr (by linarith))).symm
  unfold archTailPrimitive alt
  rw [← Real.log_div (by positivity) hexp1]
  congr 2
  apply (div_eq_div_iff hone hexp1).2
  field_simp [Real.exp_ne_zero]
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith

theorem integrableOn_exp_neg_half_mul_archDensity_Ioi
    {L : ℝ} (hL : 0 < L) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-x / 2) * archDensity x)
      (Ioi L) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => hasDerivAt_archTailPrimitive (hL.trans_le hx))
    (fun x hx => archTailIntegrand_nonneg (hL.trans hx))
    tendsto_archTailPrimitive_atTop

theorem integral_exp_neg_half_mul_archDensity_Ioi
    {L : ℝ} (hL : 0 < L) :
    (∫ x : ℝ in Ioi L, Real.exp (-x / 2) * archDensity x) =
      (1 / 2) * Real.log
        ((Real.exp L + 1) / (Real.exp L - 1)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => hasDerivAt_archTailPrimitive (hL.trans_le hx))
    (fun x hx => archTailIntegrand_nonneg (hL.trans hx))
    tendsto_archTailPrimitive_atTop]
  unfold archTailPrimitive
  rw [← Real.log_div (by positivity)
    (sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hL)))]
  ring

/-! ## The exact finite-part constant -/

theorem mu_zero_reference_tail_eq_neg_two_wCorrection
    {L : ℝ} (hL : 0 < L) :
    2 * Real.pi * Zeta23.mu 0 +
        2 * (∫ x : ℝ in Ioi 0,
          (1 - Real.exp (-x / 2)) * archDensity x) +
        2 * (∫ x : ℝ in Ioi L,
          Real.exp (-x / 2) * archDensity x) =
      -2 * wCorrection L := by
  rw [two_pi_mul_mu_zero,
    integral_one_sub_exp_mul_archDensity_Ioi,
    integral_exp_neg_half_mul_archDensity_Ioi hL]
  unfold wCorrection
  have hlogFour : Real.log (4 * Real.pi) =
      2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlogFour]
  ring

end Zeta23.CCM
