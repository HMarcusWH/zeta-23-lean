import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.ExceptionalZero.FilteredResolventMeromorphic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Real-strip nonvanishing and the actual resolvent's real-axis regularity

The N=1 Euler-Maclaurin identity already proved in the repository gives
strict negativity of the real part of zeta on the real open critical
strip. The actual zero carrier therefore has nonzero ordinates, and the
actual filtered resolvent has no real poles. No zeta nonvanishing or
integral bound is accepted as a caller premise.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped Topology

namespace Zeta23.ExceptionalZero

private def centeredFloorRemainder (σ x : ℝ) : ℂ :=
  ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ ((σ : ℂ) + 1)

private theorem centeredFloorRemainder_integral_norm_le {σ : ℝ} (hσ : 0 < σ) :
    ‖∫ x : ℝ in Ioi 1, centeredFloorRemainder σ x‖ ≤ 1 / (2 * σ) := by
  have hexp : -σ - 1 < -1 := by linarith
  have hmajor : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1),
      ‖centeredFloorRemainder σ x‖ ≤ (1 / 2 : ℝ) * x ^ (-σ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx
    unfold centeredFloorRemainder
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hnum : ‖(⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)‖ = ‖(⌊x⌋ : ℝ) + 1 / 2 - x‖ := by
      rw [show ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) =
        (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]
    rw [hnum]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le]
    rw [show -(σ + 1) = -σ - 1 by ring]
    exact mul_le_mul_of_nonneg_right (ZetaSum_aux1_3 x) (Real.rpow_nonneg hxpos.le _)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, (1 / 2 : ℝ) * x ^ (-σ - 1) :=
      norm_integral_le_of_norm_le hmajor hbound
    _ = 1 / (2 * σ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp (by norm_num : (0 : ℝ) < 1),
        Real.one_rpow]
      field_simp [hσ.ne']
      ring

/-- The real-axis open-strip value has strictly negative real part;
the quantitative bound follows from the actual N=1 remainder. -/
theorem riemannZeta_re_le_neg_div_one_sub {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re ≤ -σ / (1 - σ) := by
  have hσC : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hσC1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  have hform : riemannZeta (σ : ℂ) =
      ((1 / 2 - 1 / (1 - σ) : ℝ) : ℂ) +
        (σ : ℂ) * ∫ x : ℝ in Ioi 1, centeredFloorRemainder σ x := by
    calc
      _ = riemannZeta0 1 (σ : ℂ) :=
        (Zeta0EqZeta (N := 1) (by norm_num) (by simpa using hσ) hσC1).symm
      _ = (1 : ℂ) + (-1) / (1 - (σ : ℂ)) + (-1) / 2 +
          (σ : ℂ) * ∫ x : ℝ in Ioi 1, centeredFloorRemainder σ x := by
        norm_num [riemannZeta0, centeredFloorRemainder, Finset.sum_range_succ,
          Complex.zero_cpow hσC]
      _ = _ := by push_cast; ring
  have hre := congrArg Complex.re hform
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  have hrem : (∫ x : ℝ in Ioi 1, centeredFloorRemainder σ x).re ≤ 1 / (2 * σ) :=
    (Complex.re_le_norm _).trans (centeredFloorRemainder_integral_norm_le hσ)
  calc
    _ = 1 / 2 - 1 / (1 - σ) +
        σ * (∫ x : ℝ in Ioi 1, centeredFloorRemainder σ x).re := hre
    _ ≤ 1 / 2 - 1 / (1 - σ) + σ * (1 / (2 * σ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hrem hσ.le)
    _ = -σ / (1 - σ) := by
      field_simp [hσ.ne', sub_ne_zero.mpr hσ1.ne']
      ring

theorem riemannZeta_ne_zero_of_real_critical_strip {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) : riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  have hle := riemannZeta_re_le_neg_div_one_sub hσ hσ1
  rw [hz, Complex.zero_re] at hle
  have hneg : -σ / (1 - σ) < 0 := div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hσ1)
  exact (not_lt_of_ge hle) hneg

/-- Nonzero ordinates are proved for the repository's actual distinct
nontrivial zero carrier, rather than included in its definition. -/
theorem zetaZeroCarrier_im_ne_zero (ρ : zetaZeroConfig.carrier) : (ρ : ℂ).im ≠ 0 := by
  intro him
  have heq : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, him]
  have hz := ρ.2.1
  rw [heq] at hz
  exact riemannZeta_ne_zero_of_real_critical_strip ρ.2.2.1 ρ.2.2.2 hz

theorem filteredPolePoint_ne_ofReal (ρ : zetaZeroConfig.carrier) (p : ℝ) :
    filteredPolePoint (1 / 2 : ℂ) ρ ≠ (p : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num [filteredPolePoint, Complex.mul_im] at him
  apply zetaZeroCarrier_im_ne_zero ρ
  linarith

/-- The actual absolutely summable filtered resolvent is holomorphic at
every real point. This is the real-boundary prerequisite for a positive
Laplace argument, and does not assert signed excursions. -/
theorem analyticAt_filteredResolvent_ofReal {φ : ZeroFilter}
    (hφ : AbsolutelySummableZeroFilter φ) (p : ℝ) :
    AnalyticAt ℂ (filteredResolvent φ (1 / 2 : ℂ)) (p : ℂ) :=
  analyticAt_filteredResolvent_of_forall_ne hφ (fun ρ => filteredPolePoint_ne_ofReal ρ p)

end Zeta23.ExceptionalZero

#print axioms Zeta0EqZeta
#print axioms ZetaSum_aux1_3
#print axioms Zeta23.ExceptionalZero.riemannZeta_re_le_neg_div_one_sub
#print axioms Zeta23.ExceptionalZero.riemannZeta_ne_zero_of_real_critical_strip
#print axioms Zeta23.ExceptionalZero.zetaZeroCarrier_im_ne_zero
#print axioms Zeta23.ExceptionalZero.analyticAt_filteredResolvent_ofReal
