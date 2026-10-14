import Zeta23.CCM.OriginalSincDriveCancellation

/-!
# The actual derivative underlying the integer-drive Abel bound

The formula is derived from the actual log, square-root weight and source.
It retains both j and j' with their exact coefficients. The quantitative
integral estimate and stable Y membership remain separate obligations.
-/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.CCM

private theorem logarithmic_drive_derivative_algebra
    (x R z v w : ℝ) (hx : x ≠ 0) (hR : R ≠ 0) (hroot : R ^ 2 = x) :
    ((x⁻¹ * R - z * (1 / (2 * R))) / R ^ 2) * v +
      (z / R) * (w * (0 - x⁻¹)) =
      ((1 - z / 2) * v - z * w) / (x * R) := by
  subst x
  field_simp [hR]
  ring

theorem nativeOriginalLogDriveSummand_hasDerivAt {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (nativeOriginalLogDriveSummand t)
      (((1 - Real.log x / 2) * nativeOriginalSource (t - Real.log x) -
        Real.log x * deriv nativeOriginalSource (t - Real.log x)) /
        (x * Real.sqrt x)) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have hroot := Real.hasDerivAt_sqrt hx.ne'
  have hrootne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have harg := (hasDerivAt_const x t).sub hlog
  have hj := (nativeOriginalSource_contDiff.differentiable
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
    (t - Real.log x)).hasDerivAt
  have hsource := hj.comp x harg
  have hraw := (hlog.div hroot hrootne).mul hsource
  have hagree : nativeOriginalLogDriveSummand t =ᶠ[𝓝 x]
      (fun y : ℝ => Real.log y / Real.sqrt y *
        nativeOriginalSource (t - Real.log y)) := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact if_pos hy
  have hd := hraw.congr_of_eventuallyEq hagree.symm
  convert hd using 1
  exact (logarithmic_drive_derivative_algebra x (Real.sqrt x)
    (Real.log x) (nativeOriginalSource (t - Real.log x))
    (deriv nativeOriginalSource (t - Real.log x)) hx.ne' hrootne
    (Real.sq_sqrt hx.le)).symm

theorem nativeOriginalLogDriveSummand_deriv {t x : ℝ} (hx : 0 < x) :
    deriv (nativeOriginalLogDriveSummand t) x =
      ((1 - Real.log x / 2) * nativeOriginalSource (t - Real.log x) -
        Real.log x * deriv nativeOriginalSource (t - Real.log x)) /
        (x * Real.sqrt x) :=
  (nativeOriginalLogDriveSummand_hasDerivAt hx).deriv

/-- The exponential Jacobian cancels exactly the x in the derivative
denominator. The remaining square-root weight is paid explicitly. -/
theorem nativeOriginalLogDriveSummand_deriv_exp (t y : ℝ) :
    Real.exp y * deriv (nativeOriginalLogDriveSummand t) (Real.exp y) =
      (((1 - y / 2) * nativeOriginalSource (t - y) -
        y * deriv nativeOriginalSource (t - y)) / Real.sqrt (Real.exp y)) := by
  rw [nativeOriginalLogDriveSummand_deriv (Real.exp_pos y), Real.log_exp]
  field_simp [(Real.exp_pos y).ne', (Real.sqrt_pos.mpr (Real.exp_pos y)).ne']

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_hasDerivAt
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_deriv
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_deriv_exp
