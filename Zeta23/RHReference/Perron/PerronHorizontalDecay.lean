import Zeta23.FromPNTPlus.ResidueCalcOnRectangles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A uniform reciprocal-height bound suffices for both Perron horizontal edges. -/

open Complex Filter Set
open scoped Topology Interval

namespace Zeta23.RHReference

theorem tendsto_HIntegral_zero_of_height_bound {f : ℂ → ℂ} {a b K side : ℝ}
    (hab : a ≤ b) (hside : |side| = 1)
    (hbound : ∀ t : ℝ, 3 ≤ |t| → ∀ u ∈ Icc a b,
      ‖f ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K / |t|) :
    Tendsto (fun T : ℝ => HIntegral f a b (side * T)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hdecay : Tendsto (fun t : ℝ => (b - a) * K / t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.const_mul ((b - a) * K))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdecay
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  have hT0 : 0 ≤ T := by linarith
  have hscaled : |side * T| = T := by rw [abs_mul, hside, one_mul, abs_of_nonneg hT0]
  have hpoint u (hu : u ∈ Ι a b) :
      ‖f ((u : ℂ) + ((side * T : ℝ) : ℂ) * Complex.I)‖ ≤ K / T := by
    rw [uIoc_of_le hab] at hu
    simpa only [hscaled] using hbound (side * T) (by simpa only [hscaled] using hT)
      u ⟨hu.1.le, hu.2⟩
  unfold HIntegral
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab), div_mul_eq_mul_div, mul_comm K (b - a)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const hpoint)

end Zeta23.RHReference

#print axioms Zeta23.RHReference.tendsto_HIntegral_zero_of_height_bound
