import Zeta23.RHReference.Perron.LiteralPerronShift

/-!
Exact conversion of a shifted Perron identity into a native power bound.
An integrable majorant on the normalized fixed line is independent of x,
so its integral is the common constant for the centered ramp.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory

namespace Zeta23.RHReference

/-- The spectral-height kernel on a fixed line, with the x-power removed. -/
def literalPerronHeightKernel (σ t : ℝ) : ℂ :=
  let s := (σ : ℂ) + t * I
  (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1))

theorem norm_literalPerron_vertical_eq {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    ‖literalPerronIntegrand x ((σ : ℂ) + t * I)‖ =
      x ^ σ * ‖literalPerronHeightKernel σ t‖ := by
  have hreal : ((σ : ℂ) + t * I).re = σ := by simp [Complex.mul_re]
  simp only [literalPerronHeightKernel, literalPerronIntegrand, norm_div, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hreal]
  ring

theorem norm_literalPerron_verticalIntegral_le {x σ : ℝ} (hx : 0 < x)
    {ω : ℝ → ℝ} (hω : Integrable ω)
    (hMajorant : ∀ t : ℝ, ‖literalPerronHeightKernel σ t‖ ≤ ω t) :
    ‖VerticalIntegral' (literalPerronIntegrand x) σ‖ ≤
      ((1 / (2 * Real.pi)) * ∫ t : ℝ, ω t) * x ^ σ := by
  have hxpow : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le _
  have hNorm (t : ℝ) : ‖literalPerronIntegrand x ((σ : ℂ) + t * I)‖ ≤ x ^ σ * ω t := by
    rw [norm_literalPerron_vertical_eq hx]
    exact mul_le_mul_of_nonneg_left (hMajorant t) hxpow
  have hIntegral := norm_integral_le_of_norm_le (hω.const_mul (x ^ σ))
    (Eventually.of_forall hNorm)
  rw [integral_const_mul] at hIntegral
  have hC : ‖((1 : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [verticalIntegral'_eq_height_integral, norm_mul, hC]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (x ^ σ * ∫ t : ℝ, ω t) :=
      mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = _ := by ring

/-- The exact, centered native finite ramp satisfies the absolute power
estimate with the fixed height-majorant integral as its constant. -/
theorem abs_native_centered_ramp_le_of_shift {x σ : ℝ} (hx : 0 < x)
    {ω : ℝ → ℝ} (hω : Integrable ω)
    (hMajorant : ∀ t : ℝ, ‖literalPerronHeightKernel σ t‖ ≤ ω t)
    (hShift : VerticalIntegral' (literalPerronIntegrand x) σ =
      ↑((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x)) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x| ≤
      ((1 / (2 * Real.pi)) * ∫ t : ℝ, ω t) * x ^ σ := by
  have h := norm_literalPerron_verticalIntegral_le hx hω hMajorant
  simpa only [hShift, Complex.norm_real, Real.norm_eq_abs] using h

#print axioms Zeta23.RHReference.norm_literalPerron_vertical_eq
#print axioms Zeta23.RHReference.norm_literalPerron_verticalIntegral_le
#print axioms Zeta23.RHReference.abs_native_centered_ramp_le_of_shift

end Zeta23.RHReference
