import Zeta23.OPICATerminal.SourceNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Set MeasureTheory Filter
namespace OPICAExtractionR1

/-- On each positive compact interval the variable cutoff can be padded to
    its right endpoint with zero truncated ramp terms. -/
theorem rampG_continuousOn_pos {a b : ℝ} (ha : 0 < a) :
    ContinuousOn rampG (Icc a b) := by
  let f : ℝ → ℝ := fun x =>
    (∑ n ∈ Finset.range (⌊b⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) -
      x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
  have hs : Continuous (fun x : ℝ => ∑ n ∈ Finset.range (⌊b⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) := by
    fun_prop
  have hlog : ContinuousOn Real.log (Icc a b) := Real.continuousOn_log.mono
    (fun x hx => by
      change x ≠ 0
      exact (ha.trans_le hx.1).ne')
  have hf : ContinuousOn f (Icc a b) := by
    exact (hs.continuousOn.sub (continuous_id.continuousOn.mul hlog)).add
      (continuous_const.mul continuous_id).continuousOn
  refine hf.congr fun x hx => ?_
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊b⌋₊ + 1) :=
    Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hx.2))
  have heq : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) =
      ∑ n ∈ Finset.range (⌊b⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0 := by
    apply Finset.sum_subset hsub
    intro n _ hn
    have hnot : ¬ n ≤ ⌊x⌋₊ := by
      intro h
      exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    have hn0 : 0 < n := by omega
    have hxn : x < (n : ℝ) := lt_of_not_ge
      (fun h => hnot ((Nat.le_floor_iff' hn0.ne').mpr h))
    have hdiv : x / (n : ℝ) ≤ 1 :=
      (div_le_iff₀ (Nat.cast_pos.mpr hn0)).mpr (by simpa using hxn.le)
    rw [max_eq_right (sub_nonpos.mpr hdiv), mul_zero]
  simp only [rampG, f, heq]

theorem window_energy_bound (g : ℝ → ℝ) {Y ε A : ℝ}
    (hY : 2 ≤ Y) (hε : 0 < ε) (hA : 0 ≤ A)
    (hc : ContinuousOn g (Icc Y (Y ^ (3 / 2 : ℝ))))
    (hb : ∀ x ∈ Icc Y (Y ^ (3 / 2 : ℝ)), g x ≤ A * x ^ (1 / 2 + ε)) :
    (∫ x in Y..Y^(3 / 2 : ℝ), (max (g x) 0)^2 / x^2)
      ≤ (A^2/(2*ε))*Y^(3*ε) := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hle : Y ≤ Y ^ (3 / 2 : ℝ) := by
    calc
      Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hpos : ∀ x ∈ Icc Y (Y ^ (3 / 2 : ℝ)), 0 < x := fun x hx => hY0.trans_le hx.1
  have hmaxcont : ContinuousOn (fun x => max (g x) 0) (Icc Y (Y ^ (3 / 2 : ℝ))) :=
    hc.sup continuousOn_const
  have hfg : ContinuousOn (fun x => (max (g x) 0)^2 / x^2) (Icc Y (Y ^ (3 / 2 : ℝ))) :=
    (hmaxcont.pow 2).div
      (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero _ (hpos x hx).ne')
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-1 + 2*ε)) (Icc Y (Y ^ (3 / 2 : ℝ))) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')).continuousWithinAt
  have hgg : ContinuousOn (fun x : ℝ => A^2 * x^(-1+2*ε)) (Icc Y (Y^(3/2:ℝ))) :=
    continuousOn_const.mul hpow
  have hfi : IntervalIntegrable (fun x => (max (g x) 0)^2 / x^2)
      MeasureTheory.volume Y (Y^(3/2:ℝ)) :=
    hfg.intervalIntegrable_of_Icc hle
  have hgi : IntervalIntegrable (fun x : ℝ => A^2 * x^(-1+2*ε))
      MeasureTheory.volume Y (Y^(3/2:ℝ)) :=
    hgg.intervalIntegrable_of_Icc hle
  have hmono :
      (∫ x in Y..Y^(3/2:ℝ), (max (g x) 0)^2 / x^2) ≤
        ∫ x in Y..Y^(3/2:ℝ), A^2 * x^(-1+2*ε) :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle hfi hgi (fun x hx => by
      have hx0 := hpos x hx
      have hmax : max (g x) 0 ≤ A * x ^ (1 / 2 + ε) :=
        max_le (hb x hx) (mul_nonneg hA (Real.rpow_nonneg hx0.le _))
      have hsq : (max (g x) 0)^2 ≤ (A*x^(1/2+ε))^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (add_nonneg (le_max_right (g x) 0) (mul_nonneg hA (Real.rpow_nonneg hx0.le (1/2+ε))))]
      calc
        (max (g x) 0)^2 / x^2 ≤ (A*x^(1/2+ε))^2 / x^2 :=
          div_le_div_of_nonneg_right hsq (sq_nonneg x)
        _ = A^2 * x^(-1+2*ε) := by
          have hp : (x^(1/2+ε:ℝ))^2 = x^((1/2+ε)*2:ℝ) := by
            rw [Real.rpow_mul hx0.le, Real.rpow_two]
          rw [mul_pow, hp, mul_div_assoc, ← Real.rpow_two x, ← Real.rpow_sub hx0,
            show ((1/2+ε:ℝ)*2-2) = -1+2*ε by ring])
  calc
    _ ≤ ∫ x in Y..Y^(3/2:ℝ), A^2 * x^(-1+2*ε) := hmono
    _ = A^2 * ((Y^(3/2:ℝ))^(2*ε) - Y^(2*ε)) / (2*ε) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1:ℝ) < -1+2*ε)),
        show (-1+2*ε+1:ℝ) = 2*ε by ring, mul_div_assoc]
    _ ≤ A^2/(2*ε)*Y^(3*ε) := by
      have he : (Y^(3/2:ℝ))^(2*ε) = Y^(3*ε) := by
        rw [← Real.rpow_mul hY0.le, show (3/2:ℝ)*(2*ε) = 3*ε by ring]
      rw [he]
      calc
        A^2 * (Y^(3*ε) - Y^(2*ε))/(2*ε) ≤ A^2*Y^(3*ε)/(2*ε) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg hY0.le _)) (sq_nonneg A))
            (by positivity)
        _ = A^2/(2*ε)*Y^(3*ε) := by ring

end OPICAExtractionR1
