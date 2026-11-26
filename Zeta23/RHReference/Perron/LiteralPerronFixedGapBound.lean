import Zeta23.RHReference.Perron.LiteralPerronPowerBound
import Zeta23.RHReference.Perron.PerronHeightWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Supply the exact fixed-line Perron height majorant from a logarithmic
bound. The right line comes directly from absolute convergence of the
von Mangoldt L-series. The remaining analytic data are the fixed-gap
left-line logarithmic bound and horizontal decay.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology

namespace Zeta23.RHReference

private theorem verticalPoint_re (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by
  simp [Complex.mul_re]

/-- The exact denominator and an all-height logarithmic bound together
provide a common L¹ majorant for the normalized fixed line. -/
theorem literalPerronHeightKernel_log_majorant {σ C : ℝ}
    (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) (hC : 0 ≤ C)
    (hLog : ∀ t : ℝ, let s := (σ : ℂ) + t * I
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * (1 + Real.log (2 + ‖t‖))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖literalPerronHeightKernel σ t‖ ≤ B * perronLogHeightWeight t := by
  obtain ⟨K, hK, hWeight⟩ := perronWeight_fixedVertical_majorant hσ0 hσ1
  refine ⟨C * K, mul_nonneg hC hK.le, fun t => ?_⟩
  let s := (σ : ℂ) + t * I
  change ‖-deriv riemannZeta s / riemannZeta s / (s * (s - 1))‖ ≤ _
  rw [div_eq_mul_inv (-deriv riemannZeta s / riemannZeta s), norm_mul]
  have hL : 0 ≤ Real.log (2 + ‖t‖) := Real.log_nonneg (by linarith [norm_nonneg t])
  calc
    _ ≤ (C * (1 + Real.log (2 + ‖t‖))) * (K / (1 + ‖t‖ ^ 2)) :=
      mul_le_mul (hLog t) (hWeight t) (norm_nonneg _) (mul_nonneg hC (by linarith))
    _ = _ := by
      unfold perronLogHeightWeight
      ring

private theorem continuous_literalPerron_vertical {x σ : ℝ}
    (hx : 0 < x) (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1)
    (hζ : ∀ t : ℝ, riemannZeta ((σ : ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => literalPerronIntegrand x ((σ : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (σ : ℂ) + t * I
  have hs : Continuous s :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hs0 (t : ℝ) : s t ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    exact hσ0 (by simpa [s, verticalPoint_re] using hh)
  have hs1 (t : ℝ) : s t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    exact hσ1 (by simpa [s, verticalPoint_re] using hh)
  have hA (t : ℝ) : AnalyticAt ℂ riemannZeta (s t) :=
    differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton _ (hs1 t)
  have hZeta : Continuous (fun t => riemannZeta (s t)) :=
    continuous_iff_continuousAt.2 fun t => (hA t).continuousAt.comp hs.continuousAt
  have hDeriv : Continuous (fun t => deriv riemannZeta (s t)) :=
    continuous_iff_continuousAt.2 fun t => (hA t).deriv.continuousAt.comp hs.continuousAt
  have hPow : Continuous (fun t => (x : ℂ) ^ s t) :=
    hs.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hx.ne'))
  change Continuous (fun t : ℝ =>
    (-deriv riemannZeta (s t) / riemannZeta (s t)) * (x : ℂ) ^ s t / (s t * (s t - 1)))
  exact ((hDeriv.neg.div hZeta hζ).mul hPow).div (hs.mul (hs.sub continuous_const))
    (fun t => mul_ne_zero (hs0 t) (sub_ne_zero.mpr (hs1 t)))

/-- The normalized majorant gives integrability of every x-scaled
Perron integrand over the fixed vertical line. -/
theorem literalPerron_vertical_integrable_of_majorant {x σ B : ℝ}
    (hx : 0 < x) (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1)
    (hζ : ∀ t : ℝ, riemannZeta ((σ : ℂ) + t * I) ≠ 0)
    (hB : ∀ t : ℝ, ‖literalPerronHeightKernel σ t‖ ≤ B * perronLogHeightWeight t) :
    Integrable (fun t : ℝ => literalPerronIntegrand x ((σ : ℂ) + t * I)) := by
  apply integrable_of_perronLogHeightWeight
    (C := x ^ σ * B) (continuous_literalPerron_vertical hx hσ0 hσ1 hζ).aestronglyMeasurable
  intro t
  rw [norm_literalPerron_vertical_eq hx]
  calc
    _ ≤ x ^ σ * (B * perronLogHeightWeight t) :=
      mul_le_mul_of_nonneg_left (hB t) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

/-- Absolute convergence of the von Mangoldt L-series gives a uniform
logarithmic majorant on the initial line Re s = 2. -/
theorem rightLine_logDerivative_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, let s := ((2 : ℝ) : ℂ) + t * I
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * (1 + Real.log (2 + ‖t‖)) := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C := ∑' n : ℕ, ‖LSeries.term a (2 : ℂ) n‖
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C, hC, fun t => ?_⟩
  let s := ((2 : ℝ) : ℂ) + t * I
  have hs : 1 < s.re := by simp [s, verticalPoint_re]
  have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  change ‖-deriv riemannZeta s / riemannZeta s‖ ≤ _
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  change ‖∑' n : ℕ, LSeries.term a s n‖ ≤ _
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm hL
    _ = C := by
      apply tsum_congr
      intro n
      simp [LSeries.norm_term_eq, s, verticalPoint_re]
    _ ≤ _ := by
      have hlog : 0 ≤ Real.log (2 + ‖t‖) := Real.log_nonneg (by linarith [norm_nonneg t])
      exact le_mul_of_one_le_right hC (by linarith)

private theorem riemannZeta_vertical_ne_zero_of_fixedGap {β σ : ℝ}
    (hβσ : β < σ) (hσ1 : σ ≠ 1)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0) (t : ℝ) :
    riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
  apply hzero
  · simpa only [verticalPoint_re] using hβσ
  · intro he
    apply hσ1
    simpa only [verticalPoint_re, Complex.one_re] using congrArg Complex.re he

/-- A single fixed cutoff and logarithmic/edge estimates give a uniform
coefficient for the exact native literalG power bound. No RH endpoint
enters as a premise. -/
theorem fixedGap_native_literalG_power_bound {β σ C : ℝ}
    (hβ : 0 ≤ β) (hβσ : β < σ) (hσ1 : σ < 1) (hC : 0 ≤ C)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (hLog : ∀ t : ℝ, let s := (σ : ℂ) + t * I
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * (1 + Real.log (2 + ‖t‖)))
    (hBottom : ∀ x ≥ 2, Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 (-T))
      atTop (𝓝 0))
    (hTop : ∀ x ≥ 2, Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 T)
      atTop (𝓝 0)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ≥ 2,
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x| ≤ A * x ^ σ := by
  have hσ0 : σ ≠ 0 := (hβ.trans_lt hβσ).ne'
  obtain ⟨B, hB, hLeftWeight⟩ := literalPerronHeightKernel_log_majorant hσ0 hσ1.ne hC hLog
  obtain ⟨Cright, hCright, hRightLog⟩ := rightLine_logDerivative_log_bound
  obtain ⟨Bright, _, hRightWeight⟩ :=
    literalPerronHeightKernel_log_majorant (σ := 2) (by norm_num) (by norm_num) hCright hRightLog
  let ω : ℝ → ℝ := fun t => B * perronLogHeightWeight t
  have hω : Integrable ω := integrable_perronLogHeightWeight.const_mul B
  have hωpos : 0 ≤ ∫ t : ℝ, ω t :=
    integral_nonneg (fun t => mul_nonneg hB (perronLogHeightWeight_nonneg t))
  refine ⟨(1 / (2 * Real.pi)) * ∫ t : ℝ, ω t, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hVertLeft := literalPerron_vertical_integrable_of_majorant hx0 hσ0 hσ1.ne
    (riemannZeta_vertical_ne_zero_of_fixedGap hβσ hσ1.ne hzero) hLeftWeight
  have hVertRight := literalPerron_vertical_integrable_of_majorant (σ := 2) (B := Bright)
    hx0 (by norm_num) (by norm_num)
    (riemannZeta_vertical_ne_zero_of_fixedGap (by linarith) (by norm_num) hzero) hRightWeight
  have hIdentity := literalPerron_leftLine_native_centered hx0 hβ hβσ hσ1 hzero
    hVertRight hVertLeft (hBottom x hx) (hTop x hx)
  exact abs_native_centered_ramp_le_of_shift hx0 hω hLeftWeight hIdentity

#print axioms Zeta23.RHReference.literalPerronHeightKernel_log_majorant
#print axioms Zeta23.RHReference.literalPerron_vertical_integrable_of_majorant
#print axioms Zeta23.RHReference.rightLine_logDerivative_log_bound
#print axioms Zeta23.RHReference.fixedGap_native_literalG_power_bound

end Zeta23.RHReference
