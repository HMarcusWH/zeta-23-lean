import Zeta23.RHReference.Perron.LiteralPerronDirichlet
import Zeta23.RHReference.Perron.LiteralPerronRectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.LinearCombination

/-!
Taking the infinite-height limit of the exact literal Perron rectangle.
The required inputs are integrability on the two vertical lines and decay
of the two horizontal integrals. The zero-free threshold is fixed once.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Interval

namespace Zeta23.RHReference

/-- Pass from a stable finite rectangle integral to the difference of the
two full vertical integrals. -/
theorem verticalIntegral'_sub_eq_of_rectangle_limit
    {f : ℂ → ℂ} {σ c : ℝ} {r : ℂ}
    (hc : Integrable (fun t : ℝ => f (c + t * I)))
    (hσ : Integrable (fun t : ℝ => f (σ + t * I)))
    (hBottom : Tendsto (fun T : ℝ => HIntegral f σ c (-T)) atTop (𝓝 0))
    (hTop : Tendsto (fun T : ℝ => HIntegral f σ c T) atTop (𝓝 0))
    (hRect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((σ : ℂ) - T * I) ((c : ℂ) + T * I) = r) :
    VerticalIntegral' f c - VerticalIntegral' f σ = r := by
  have hRight : Tendsto (fun T : ℝ => VIntegral f c (-T) T)
      atTop (𝓝 (VerticalIntegral f c)) := by
    exact tendsto_const_nhds.smul
      (intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id)
  have hLeft : Tendsto (fun T : ℝ => VIntegral f σ (-T) T)
      atTop (𝓝 (VerticalIntegral f σ)) := by
    exact tendsto_const_nhds.smul
      (intervalIntegral_tendsto_integral hσ tendsto_neg_atTop_atBot tendsto_id)
  have hUnscaled :
      Tendsto (fun T : ℝ => RectangleIntegral f ((σ : ℂ) - T * I) ((c : ℂ) + T * I))
        atTop (𝓝 (VerticalIntegral f c - VerticalIntegral f σ)) := by
    simpa [RectangleIntegral, Complex.mul_re, Complex.mul_im] using
      ((hBottom.sub hTop).add hRight).sub hLeft
  have hScaled :
      Tendsto (fun T : ℝ => RectangleIntegral' f ((σ : ℂ) - T * I) ((c : ℂ) + T * I))
        atTop (𝓝 (VerticalIntegral' f c - VerticalIntegral' f σ)) := by
    let scale : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
    have hScale : Tendsto (fun _ : ℝ => scale) atTop (𝓝 scale) := tendsto_const_nhds
    simpa only [VerticalIntegral', RectangleIntegral', smul_sub] using
      hScale.smul hUnscaled
  have hEq : (fun T : ℝ => RectangleIntegral' f ((σ : ℂ) - T * I) ((c : ℂ) + T * I))
      =ᶠ[atTop] fun _ => r := hRect
  exact tendsto_nhds_unique hScaled (tendsto_const_nhds.congr' hEq.symm)

theorem verticalIntegral'_eq_height_integral (f : ℂ → ℂ) (σ : ℝ) :
    VerticalIntegral' f σ =
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, f (σ + t * I) := by
  change ((1 : ℂ) / (2 * (Real.pi : ℂ) * I)) * (I * _) = _
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- Exact formula for the right line in the same integrand representation
used for the rectangle. -/
theorem literalPerron_rightLine_native_sum {x : ℝ} (hx : 0 < x) :
    VerticalIntegral' (literalPerronIntegrand x) 2 =
      ↑(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) := by
  rw [verticalIntegral'_eq_height_integral]
  refine Eq.trans ?_ (rightLinePerron_eq_native_sum hx)
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    let s : ℂ := ((2 : ℝ) : ℂ) + t * I
    change literalPerronIntegrand x s = (-deriv riemannZeta s / riemannZeta s) *
      (perronRampTransform s * (x : ℂ) ^ s)
    unfold literalPerronIntegrand perronRampTransform
    ring)

/-- A single fixed zero-free side gives the exact centered ramp on the
left line, conditional on the four edge estimates needed for the limit. -/
theorem literalPerron_leftLine_native_centered {x β σ : ℝ} (hx : 0 < x)
    (hβ : 0 ≤ β) (hβσ : β < σ) (hσ1 : σ < 1)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (hRight : Integrable (fun t : ℝ => literalPerronIntegrand x (((2 : ℝ) : ℂ) + t * I)))
    (hLeft : Integrable (fun t : ℝ => literalPerronIntegrand x (σ + t * I)))
    (hBottom : Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 (-T))
      atTop (𝓝 0))
    (hTop : Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 T)
      atTop (𝓝 0)) :
    VerticalIntegral' (literalPerronIntegrand x) σ =
      ↑((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x) := by
  have hRect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' (literalPerronIntegrand x) ((σ : ℂ) - T * I)
        (((2 : ℝ) : ℂ) + T * I) = literalPerronResidue x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    let z := (σ : ℂ) - T * I
    let w := (((2 : ℝ) : ℂ) + T * I)
    have hRe : z.re < w.re := by
      simp [z, w, Complex.mul_re]
      linarith
    have hIm : z.im < w.im := by
      simp [z, w, Complex.mul_im]
      linarith
    have hOne : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, uIoo_of_lt hRe, uIoo_of_lt hIm]
      simp [z, w, Complex.mul_re, Complex.mul_im, hT, hσ1]
    exact literalPerron_rectangle_eq_residue_of_fixed_strip hx hβ hzero
      (by simpa [z, Complex.mul_re] using hβσ) hRe.le hIm.le hOne
  have hShift := verticalIntegral'_sub_eq_of_rectangle_limit hRight hLeft hBottom hTop hRect
  rw [literalPerron_rightLine_native_sum hx] at hShift
  unfold literalPerronResidue at hShift
  push_cast at hShift ⊢
  linear_combination -hShift

#print axioms Zeta23.RHReference.verticalIntegral'_sub_eq_of_rectangle_limit
#print axioms Zeta23.RHReference.literalPerron_rightLine_native_sum
#print axioms Zeta23.RHReference.literalPerron_leftLine_native_centered

end Zeta23.RHReference
