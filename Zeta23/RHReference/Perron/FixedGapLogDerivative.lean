import Zeta23.FromPNTPlus.StrongPNTPrefix
import Zeta23.FromPNTPlus.ZetaBounds
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Local analytic bounds used by a fixed-strip Perron contour. -/

open Complex MeasureTheory Set

namespace Zeta23.RHReference

theorem norm_logDerivative_le_of_log_growth {B : ℂ → ℂ} {M r R : ℝ}
    (hM : 0 < M) (hr : 0 < r) (hgap : r < R)
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R))
    (hnz : ∀ z ∈ Metric.closedBall 0 R, B z ≠ 0)
    (hlog : ∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
    ‖deriv B z / B z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  obtain ⟨J, hJ, hJzero, hJderiv, hJre⟩ := LogOfAnalyticFunction hr hgap hB hnz
  rw [← hJderiv z hz]
  exact BorelCaratheodoryDeriv hM hr hgap hJ.analyticOn hJzero
    (fun w hw => hJre w hw ▸ hlog w hw) hz

theorem norm_riemannZeta_le_linear_height {s : ℂ}
    (hlow : 1 / 2 ≤ s.re) (hupp : s.re ≤ 3) (hheight : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 * (2 + |s.im|) := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun he => by simp [he] at hpos
  have hs1 : s ≠ 1 := fun he => by norm_num [he] at hheight
  let I₁ := ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
  have hr : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  have hI : ‖I₁‖ ≤ 2 := by
    have hbound : ‖I₁‖ ≤ 1 / s.re := by
      simpa [hr, I₁] using ZetaBnd_aux1b 1 (by norm_num) (t := s.im) hpos
    exact hbound.trans ((div_le_iff₀ hpos).2 (by linarith))
  have hz : riemannZeta s = 1 + (-1) / (1 - s) + (-1) / 2 + s * I₁ := by
    rw [← Zeta0EqZeta (N := 1) (by norm_num) hpos hs1]
    simp [riemannZeta0, I₁, Finset.sum_range_succ, Complex.zero_cpow hs0]
  have h1s : 1 ≤ ‖1 - s‖ := hheight.trans (by
    simpa using Complex.abs_im_le_norm (1 - s))
  have hpole : ‖(-1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_neg, norm_one]
    exact (div_le_iff₀ (by linarith)).2 (by simpa using h1s)
  have hhalf : ‖(-1 : ℂ) / 2‖ ≤ 1 := by norm_num [norm_div]
  have hs : ‖s‖ ≤ 3 + |s.im| := by
    calc
      ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ := congrArg norm hr.symm
      _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ _ := by simpa [norm_mul, abs_of_pos hpos] using add_le_add_right hupp |s.im|
  have htail : ‖s * I₁‖ ≤ (3 + |s.im|) * 2 := by
    rw [norm_mul]
    exact mul_le_mul hs hI (norm_nonneg _) (by positivity)
  rw [hz]
  calc
    _ ≤ (‖(1 : ℂ) + (-1) / (1 - s) + (-1) / 2‖) + ‖s * I₁‖ := norm_add_le _ _
    _ ≤ (‖(1 : ℂ) + (-1) / (1 - s)‖ + ‖(-1 : ℂ) / 2‖) + ‖s * I₁‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖(1 : ℂ)‖ + ‖(-1 : ℂ) / (1 - s)‖) + ‖(-1 : ℂ) / 2‖) + ‖s * I₁‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ _ := by rw [norm_one]; linarith [abs_nonneg s.im]

private theorem log_ratio_of_linear_bounds {x y H A : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hH : 1 ≤ H) (hA : 1 ≤ A)
    (hu : x ≤ 16 * H) (hl : 1 / y ≤ A * (16 * H)) :
    Real.log x - Real.log y ≤ (2 + Real.log (256 * A)) * (1 + Real.log H) := by
  have hratio : x / y ≤ (256 * A) * H ^ 2 := by
    calc
      _ = x * (1 / y) := by ring
      _ ≤ (16 * H) * (A * (16 * H)) :=
        mul_le_mul hu hl (by positivity) (by linarith)
      _ = _ := by ring
  rw [← Real.log_div hx.ne' hy.ne']
  have hlog := Real.log_le_log (div_pos hx hy) hratio
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have ha : 0 ≤ Real.log (256 * A) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ Real.log H := Real.log_nonneg hH
  nlinarith [mul_nonneg ha ht]

noncomputable def perronPoint (u t : ℝ) : ℂ := (u : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem perronPoint_re (u t : ℝ) : (perronPoint u t).re = u := by simp [perronPoint]

@[simp] theorem perronPoint_im (u t : ℝ) : (perronPoint u t).im = t := by simp [perronPoint]

private theorem perronDisk_bounds {β σ t R : ℝ}
    (hgap : β < σ) (hR : R = 3 / 2 - (β + σ) / 2) (hR1 : R ≤ 1)
    (ht : 3 ≤ |t|) (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) R) :
    let v := perronPoint (3 / 2) t + w
    β < v.re ∧ v.re ≤ 3 ∧ 1 ≤ |v.im| ∧ |v.im| ≤ 1 + |t| := by
  have hn : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hwr := abs_le.mp ((Complex.abs_re_le_norm w).trans hn)
  have hwi := (Complex.abs_im_le_norm w).trans hn
  have him : |t| ≤ |t + w.im| + |w.im| := by simpa using (abs_sub (t + w.im) w.im)
  have hwm : |t + w.im| ≤ |t| + |w.im| := by simpa only [Real.norm_eq_abs] using norm_add_le t w.im
  simp only [add_re, add_im, perronPoint_re, perronPoint_im]
  exact ⟨by linarith [hwr.1], by linarith [hwr.2], by linarith, by linarith⟩

private theorem perronCenter_inverse_bound {t : ℝ} (ht : 3 ≤ |t|) :
    1 / ‖riemannZeta (perronPoint (3 / 2) t)‖ ≤
      (max 1 (‖riemannZeta (3 / 2 : ℂ)‖ ^ (3 / 4 : ℝ))) * (16 * (2 + |t|)) := by
  let H := 2 + |t|
  have hdouble : ‖riemannZeta (perronPoint (3 / 2) (2 * t))‖ ≤ 16 * H := by
    have hf : 1 ≤ |2 * t| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    have hh := norm_riemannZeta_le_linear_height (s := perronPoint (3 / 2) (2 * t))
      (by norm_num) (by norm_num) (by simpa using hf)
    simp only [perronPoint_im, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hh
    dsimp [H]
    linarith
  have hpow : ‖riemannZeta (perronPoint (3 / 2) (2 * t))‖ ^ (1 / 4 : ℝ) ≤ 16 * H := by
    calc
      _ ≤ (16 * H) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hdouble (by norm_num)
      _ ≤ (16 * H) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by dsimp [H]; linarith) (by norm_num)
      _ = _ := Real.rpow_one _
  have hInv := ZetaInvBound1 (σ := (3 / 2 : ℝ)) (t := t) (by norm_num)
  have hpoint : (3 / 2 : ℂ) + 2 * (t : ℂ) * Complex.I = perronPoint (3 / 2) (2 * t) := by
    simp [perronPoint]
  calc
    _ ≤ ‖riemannZeta (3 / 2 : ℂ)‖ ^ (3 / 4 : ℝ) *
        ‖riemannZeta (perronPoint (3 / 2) (2 * t))‖ ^ (1 / 4 : ℝ) := by
          simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hInv
          rw [hpoint] at hInv
          simpa only [perronPoint, Complex.ofReal_div, Complex.ofReal_ofNat] using hInv
    _ ≤ _ := mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg (norm_nonneg _) _)
      (zero_le_one.trans (le_max_left _ _))

theorem riemannZeta_fixedGap_logDerivative_bound {β σ : ℝ}
    (hβ : 1 / 2 ≤ β) (hgap : β < σ) (hσ : σ < 1)
    (hfree : ∀ z : ℂ, β < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u t : ℝ, σ ≤ u → 3 ≤ |t| →
      ‖deriv riemannZeta (perronPoint u t) / riemannZeta (perronPoint u t)‖ ≤
        C * (1 + Real.log (2 + |t|)) := by
  let r := 3 / 2 - σ
  let R := 3 / 2 - (β + σ) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrad : r < R := by dsimp [r, R]; linarith
  have hR : 0 < R := hr.trans hrad
  have hR1 : R ≤ 1 := by dsimp [R]; linarith
  let A := max 1 (‖riemannZeta (3 / 2 : ℂ)‖ ^ (3 / 4 : ℝ))
  have hA : 1 ≤ A := le_max_left _ _
  let M₀ := 2 + Real.log (256 * A)
  have hM₀ : 0 < M₀ := by
    have h := Real.log_nonneg (show 1 ≤ 256 * A by linarith)
    dsimp [M₀]
    linarith
  let C₀ := 16 * M₀ * R ^ 2 / (R - r) ^ 3
  let C₁ := ‖deriv riemannZeta (3 / 2 : ℂ) / riemannZeta (3 / 2 : ℂ)‖
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro u t hu ht
  let H := 2 + |t|
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  by_cases huright : (3 / 2 : ℝ) ≤ u
  · have hdirect := dlog_riemannZeta_bdd_on_vertical_lines_generalized (3 / 2) u t
        (by norm_num) huright
    have hright : ‖deriv riemannZeta (perronPoint u t) / riemannZeta (perronPoint u t)‖ ≤ C₁ := by
      convert hdirect using 1 <;> simp [perronPoint, C₁, neg_div]
    exact hright.trans ((le_max_right _ _).trans (le_mul_of_one_le_right
      (hC₀.le.trans (le_max_left _ _)) (by linarith)))
  let c := perronPoint (3 / 2) t
  let B : ℂ → ℂ := fun w => riemannZeta (c + w)
  have hstrip w (hw : w ∈ Metric.closedBall (0 : ℂ) R) :=
    perronDisk_bounds hgap rfl hR1 ht w hw
  have hnotOne w (hw : w ∈ Metric.closedBall (0 : ℂ) R) : c + w ≠ 1 := by
    intro he
    have h : 1 ≤ |(c + w).im| := (hstrip w hw).2.2.1
    norm_num [he] at h
  have hnonzero w (hw : w ∈ Metric.closedBall (0 : ℂ) R) : B w ≠ 0 :=
    hfree (c + w) (hstrip w hw).1 (hnotOne w hw)
  have hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R) := by
    intro w hw
    exact ((HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne) (c + w) (hnotOne w hw)).comp
      (analyticAt_const.add analyticAt_id)
  have hlog (w) (hw : w ∈ Metric.ball (0 : ℂ) R) :
      Real.log ‖B w‖ - Real.log ‖B 0‖ ≤ M₀ * (1 + Real.log H) := by
    have hw' := Metric.ball_subset_closedBall hw
    obtain ⟨hre, hupp, hlarge, hsmall⟩ := hstrip w hw'
    have hsize := norm_riemannZeta_le_linear_height (s := c + w) (by linarith) hupp hlarge
    have hbw : ‖B w‖ ≤ 16 * H := by
      change ‖riemannZeta (c + w)‖ ≤ _
      dsimp [H]
      linarith
    have hB0 := norm_pos_iff.mpr (hnonzero 0 (Metric.mem_closedBall_self hR.le))
    have hBw := norm_pos_iff.mpr (hnonzero w hw')
    apply log_ratio_of_linear_bounds hBw hB0 hH hA hbw
    simpa [B, c] using perronCenter_inverse_bound ht
  let z : ℂ := ((u - 3 / 2 : ℝ) : ℂ)
  have hz : z ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu' : u ≤ 3 / 2 := le_of_not_ge huright
    change ‖((u - 3 / 2 : ℝ) : ℂ)‖ ≤ 3 / 2 - σ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hu')]
    linarith
  have hpoint : c + z = perronPoint u t := by
    simp [c, z, perronPoint]
    ring
  have hdiff : deriv B z = deriv riemannZeta (perronPoint u t) := by
    change deriv (fun w => riemannZeta (c + w)) z = _
    rw [deriv_comp_const_add, hpoint]
  have hbound := norm_logDerivative_le_of_log_growth (M := M₀ * (1 + Real.log H))
       (by positivity) hr hrad hB hnonzero hlog hz
  rw [hdiff, show B z = riemannZeta (perronPoint u t) by simp [B, hpoint]] at hbound
  calc
    _ ≤ C₀ * (1 + Real.log H) := by convert hbound using 1; dsimp [C₀]; ring
    _ ≤ max C₀ C₁ * (1 + Real.log H) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)

theorem riemannZeta_fixedGap_vertical_logDerivative_bound {β σ u : ℝ}
    (hβ : 1 / 2 ≤ β) (hgap : β < σ) (hσ : σ < 1)
    (hfree : ∀ z : ℂ, β < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hu : σ ≤ u) (hu₁ : u ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv riemannZeta (perronPoint u t) / riemannZeta (perronPoint u t)‖ ≤
        C * (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC, hhigh⟩ := riemannZeta_fixedGap_logDerivative_bound hβ hgap hσ hfree
  have hcont : Continuous (fun t : ℝ =>
      ‖deriv riemannZeta (perronPoint u t) / riemannZeta (perronPoint u t)‖) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hne : perronPoint u t ≠ 1 := fun he => hu₁ (by simpa using congrArg Complex.re he)
    have hnz : riemannZeta (perronPoint u t) ≠ 0 :=
      hfree _ (by simpa using hgap.trans_le hu) hne
    have ha := (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne) (perronPoint u t) hne
    have hpre : Continuous (perronPoint u) := by unfold perronPoint; fun_prop
    exact ((ha.deriv.div ha hnz).continuousAt.comp hpre.continuousAt).norm
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).bddAbove_image hcont.continuousOn
  refine ⟨max C B, hC.trans_le (le_max_left _ _), ?_⟩
  intro t
  have hm : 1 ≤ 1 + Real.log (2 + |t|) := by
    have h := Real.log_nonneg (show 1 ≤ 2 + |t| by linarith [abs_nonneg t])
    linarith
  by_cases ht : 3 ≤ |t|
  · exact (hhigh u t hu ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have ht' : |t| ≤ 3 := le_of_lt (lt_of_not_ge ht)
    have hmemb : t ∈ Icc (-3 : ℝ) 3 := abs_le.mp ht'
    exact (hB ⟨t, hmemb, rfl⟩).trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (hC.le.trans (le_max_left _ _)) hm))

end Zeta23.RHReference

#print axioms Zeta23.RHReference.norm_logDerivative_le_of_log_growth
#print axioms Zeta23.RHReference.norm_riemannZeta_le_linear_height
#print axioms Zeta23.RHReference.riemannZeta_fixedGap_logDerivative_bound
#print axioms Zeta23.RHReference.riemannZeta_fixedGap_vertical_logDerivative_bound
