import Zeta23.RHReference.Perron.FixedGapLogDerivative
import Zeta23.RHReference.Perron.LiteralPerronPole
import Zeta23.RHReference.Perron.PerronHeightWeight
import Zeta23.RHReference.Perron.PerronHorizontalDecay

/-! Horizontal decay on the fixed zero-free strip used by the literal Perron shift. -/

open Complex Filter Set
open scoped Topology

namespace Zeta23.RHReference

theorem literalPerron_horizontal_decay_of_fixedGap {x β σ : ℝ}
    (hx : 1 ≤ x) (hβ : 1 / 2 ≤ β) (hgap : β < σ) (hσ : σ < 1)
    (hfree : ∀ z : ℂ, β < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 (-T)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 T) atTop (𝓝 0) := by
  obtain ⟨C, hC, hlog⟩ := riemannZeta_fixedGap_logDerivative_bound hβ hgap hσ hfree
  have hx' : 0 < x := by linarith
  have hb (t : ℝ) (ht : 3 ≤ |t|) (u : ℝ) (hu : u ∈ Icc σ 2) :
      ‖literalPerronIntegrand x (perronPoint u t)‖ ≤ (2 * C * x ^ 2) / |t| := by
    let s := perronPoint u t
    have htpos : 0 < |t| := by linarith
    have htnz : t ≠ 0 := abs_pos.mp htpos
    have hD := hlog u t hu.1 ht
    have hL : 1 + Real.log (2 + |t|) ≤ 2 * |t| := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 2 + |t| by positivity)]
    have hD' : ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * (2 * |t|) :=
      hD.trans (mul_le_mul_of_nonneg_left hL hC.le)
    have hP : ‖((x : ℂ) ^ s)‖ ≤ x ^ 2 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx', show s.re = u by simp [s]]
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx hu.2
    have hW : ‖(s * (s - 1))⁻¹‖ ≤ (|t| ^ 2)⁻¹ := by
      simpa only [s, perronPoint_im, sq_abs] using
        (perronWeight_norm_le_inv_height_sq (s := s) (by simpa [s] using htnz))
    have hn : ‖literalPerronIntegrand x s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ * ‖(x : ℂ) ^ s‖ * ‖(s * (s - 1))⁻¹‖ := by
      simp only [literalPerronIntegrand, norm_mul, norm_neg, norm_inv, div_eq_mul_inv]
    calc
      _ = _ := hn
      _ ≤ (C * (2 * |t|) * x ^ 2) * (|t| ^ 2)⁻¹ :=
        mul_le_mul (mul_le_mul hD' hP (norm_nonneg _) (by positivity)) hW
          (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [htpos.ne']
  have hσ2 : σ ≤ 2 := by linarith
  have go (side : ℝ) (hside : |side| = 1) :
      Tendsto (fun T : ℝ => HIntegral (literalPerronIntegrand x) σ 2 (side * T))
        atTop (𝓝 0) := tendsto_HIntegral_zero_of_height_bound hσ2 hside hb
  exact ⟨by simpa using go (-1) (by norm_num), by simpa using go 1 (by norm_num)⟩

end Zeta23.RHReference

#print axioms Zeta23.RHReference.literalPerron_horizontal_decay_of_fixedGap
