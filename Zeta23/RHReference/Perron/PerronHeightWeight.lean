import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Absolute integrability of the logarithmic height majorant for a Perron weight. -/

open MeasureTheory Filter

namespace Zeta23.RHReference

noncomputable def perronLogHeightWeight (t : ℝ) : ℝ :=
  (1 + Real.log (2 + ‖t‖)) / (1 + ‖t‖ ^ 2)

theorem perronLogHeightWeight_nonneg (t : ℝ) : 0 ≤ perronLogHeightWeight t := by
  unfold perronLogHeightWeight
  have hlog : 0 ≤ Real.log (2 + ‖t‖) := Real.log_nonneg (by linarith [norm_nonneg t])
  exact div_nonneg (by linarith) (by positivity)

theorem integrable_perronLogHeightWeight : Integrable perronLogHeightWeight := by
  have hint : Integrable (fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; norm_num)
  have hdom := hint.const_mul (7 : ℝ)
  have hc : Continuous perronLogHeightWeight := by
    unfold perronLogHeightWeight
    refine (continuous_const.add ((continuous_const.add continuous_norm).log ?_)).div
      (continuous_const.add (continuous_norm.pow 2)) ?_
    · intro t
      change 2 + ‖t‖ ≠ 0
      exact (show 0 < 2 + ‖t‖ by positivity).ne'
    · intro t
      change 1 + ‖t‖ ^ 2 ≠ 0
      exact (show 0 < 1 + ‖t‖ ^ 2 by positivity).ne'
  refine hdom.mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (perronLogHeightWeight_nonneg t)]
  let s : ℝ := 1 + ‖t‖ ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := by dsimp [s]; nlinarith [sq_nonneg ‖t‖]
  have hlt : 2 + ‖t‖ ≤ 3 * s := by
    dsimp [s]
    nlinarith [sq_nonneg (‖t‖ - 1 / 2)]
  have hlog : Real.log (2 + ‖t‖) ≤ Real.log 3 + Real.log s := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hs.ne']
    exact Real.log_le_log (by positivity) hlt
  have hthree : Real.log (3 : ℝ) ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < (3 : ℝ) by norm_num)]
  have hrpow : Real.log s ≤ 4 * s ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hs.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith
  have hone : 1 ≤ s ^ (1 / 4 : ℝ) := Real.one_le_rpow hs1 (by norm_num)
  have hnum : 1 + Real.log (2 + ‖t‖) ≤ 7 * s ^ (1 / 4 : ℝ) := by linarith
  change (1 + Real.log (2 + ‖t‖)) / s ≤ 7 * s ^ (-(3 / 2 : ℝ) / 2)
  calc
    _ ≤ (7 * s ^ (1 / 4 : ℝ)) / s := div_le_div_of_nonneg_right hnum hs.le
    _ = _ := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one s, mul_assoc, ← Real.rpow_add hs]
      norm_num

theorem integrable_of_perronLogHeightWeight {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {C : ℝ} (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ t, ‖f t‖ ≤ C * perronLogHeightWeight t) : Integrable f :=
  (integrable_perronLogHeightWeight.const_mul C).mono' hf (Eventually.of_forall hbound)

theorem perronWeight_norm_le_inv_height_sq {s : ℂ} (hs : s.im ≠ 0) :
    ‖(s * (s - 1))⁻¹‖ ≤ (s.im ^ 2)⁻¹ := by
  have hmul : s.im ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [← sq_abs s.im, pow_two]
    have hm : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
    exact mul_le_mul (Complex.abs_im_le_norm s) hm (abs_nonneg _) (norm_nonneg _)
  rw [norm_inv, norm_mul]
  exact inv_anti₀ (sq_pos_of_ne_zero hs) hmul

theorem perronWeight_fixedVertical_majorant {σ : ℝ} (hzero : σ ≠ 0) (hone : σ ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖(((σ : ℂ) + t * Complex.I) * ((σ : ℂ) + t * Complex.I - 1))⁻¹‖ ≤
        K / (1 + ‖t‖ ^ 2) := by
  let a := min 1 (min |σ| |σ - 1|)
  have ha : 0 < a := lt_min zero_lt_one (lt_min (abs_pos.mpr hzero)
    (abs_pos.mpr (sub_ne_zero.mpr hone)))
  have ha1 : a ≤ 1 := min_le_left _ _
  have hasq : a ^ 2 ≤ 1 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  refine ⟨2 / a ^ 2, by positivity, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hleft : a ≤ ‖s‖ := by
    calc
      a ≤ |σ| := (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ ‖s‖ := hsr ▸ Complex.abs_re_le_norm s
  have hright : a ≤ ‖s - 1‖ := by
    calc
      a ≤ |σ - 1| := (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ ‖s - 1‖ := by simpa [hsr] using Complex.abs_re_le_norm (s - 1)
  have hmin : a ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [pow_two]
    exact mul_le_mul hleft hright ha.le (norm_nonneg _)
  have htleft : ‖t‖ ≤ ‖s‖ := by simpa [hsi, Real.norm_eq_abs] using Complex.abs_im_le_norm s
  have htright : ‖t‖ ≤ ‖s - 1‖ := by
    simpa [hsi, Real.norm_eq_abs] using Complex.abs_im_le_norm (s - 1)
  have him : ‖t‖ ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [pow_two]
    exact mul_le_mul htleft htright (norm_nonneg _) (norm_nonneg _)
  have hscale := mul_le_mul_of_nonneg_right hasq (sq_nonneg ‖t‖)
  have hlower : a ^ 2 * (1 + ‖t‖ ^ 2) / 2 ≤ ‖s‖ * ‖s - 1‖ := by linarith
  have hb : 0 < a ^ 2 * (1 + ‖t‖ ^ 2) / 2 := by positivity
  change ‖(s * (s - 1))⁻¹‖ ≤ _
  rw [norm_inv, norm_mul]
  refine (inv_anti₀ hb hlower).trans_eq ?_
  field_simp

end Zeta23.RHReference

#print axioms Zeta23.RHReference.perronLogHeightWeight_nonneg
#print axioms Zeta23.RHReference.integrable_perronLogHeightWeight
#print axioms Zeta23.RHReference.integrable_of_perronLogHeightWeight
#print axioms Zeta23.RHReference.perronWeight_norm_le_inv_height_sq
#print axioms Zeta23.RHReference.perronWeight_fixedVertical_majorant
