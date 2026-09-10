import Zeta23.CCM.CanonicalApertureAnalyticPrimitives

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: complex/real aperture bridge

The complex aperture primitives are auxiliary continuation objects.  This file
locks them back to the exact production real-axis functions before any complex
source assembly is allowed downstream.

No determinant nonidentity, dense regularity, sign, or RH claim is made here.
-/

@[simp] theorem complexArchSinc_ofReal (x : ℝ) :
    complexArchSinc (x : ℂ) = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [complexArchSinc, Real.sinc_eq_dslope,
      dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx), dslope_of_ne _ hx]
    simp [slope]

@[simp] theorem complexArchSinhSlope_ofReal (x : ℝ) :
    complexArchSinhSlope (x : ℂ) = (archSinhSlope x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [archSinhSlope, (Real.hasDerivAt_sinh 0).deriv]
  · rw [complexArchSinhSlope, archSinhSlope,
      dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx), dslope_of_ne _ hx]
    simp [slope]

@[simp] theorem complexArchCosSlope_ofReal (x : ℝ) :
    complexArchCosSlope (x : ℂ) = (archCosSlope x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [archCosSlope, (Real.hasDerivAt_cos 0).deriv]
  · rw [complexArchCosSlope, archCosSlope,
      dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx), dslope_of_ne _ hx]
    simp [slope]

@[simp] theorem complexArchExpSlope_ofReal (x : ℝ) :
    complexArchExpSlope (x : ℂ) = (archExpSlope x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [archExpSlope, (Real.hasDerivAt_exp 0).deriv]
  · rw [complexArchExpSlope, archExpSlope,
      dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx), dslope_of_ne _ hx]
    simp [slope]

@[simp] theorem complexRegularizedArchScale_ofReal (x : ℝ) :
    complexRegularizedArchScale (x : ℂ) = (regularizedArchScale x : ℂ) := by
  unfold complexRegularizedArchScale regularizedArchScale
  rw [complexArchSinhSlope_ofReal]
  rw [← Complex.ofReal_exp]
  push_cast

/-- Exact positive-real-axis agreement of the complex fixed-unit alpha core. -/
@[simp] theorem complexAlphaCore_ofReal
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    complexAlphaCore n (L : ℂ) = (alphaL n L : ℂ) := by
  rw [complexAlphaCore, alphaL_eq_unitInterval_integral n hL]
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have hLt : (L : ℂ) * (t : ℂ) = ((L * t : ℝ) : ℂ) := by push_cast
  rw [hLt, complexRegularizedArchScale_ofReal]
  rw [complexArchSinc_ofReal]
  push_cast

/-- Exact positive-real-axis agreement of the complex fixed-unit beta core. -/
@[simp] theorem complexBetaCore_ofReal
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    complexBetaCore n (L : ℂ) = (betaL n L : ℂ) := by
  rw [complexBetaCore, betaL_eq_unitInterval_integral n hL]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  have hLt : (L : ℂ) * (t : ℂ) = ((L * t : ℝ) : ℂ) := by push_cast
  rw [hLt, complexRegularizedArchScale_ofReal]
  rw [← Complex.ofReal_cos]
  push_cast

/-- Exact positive-real-axis agreement of the complex fixed-unit gamma core,
after removing only the production `wCorrection`. -/
@[simp] theorem complexGammaCore_ofReal
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    complexGammaCore n (L : ℂ) =
      ((sourceEq44GammaL n L - wCorrection L : ℝ) : ℂ) := by
  rw [complexGammaCore,
    sourceEq44GammaL_sub_wCorrection_eq_unitInterval_integral n hL]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  have hLt : (L : ℂ) * (t : ℂ) = ((L * t : ℝ) : ℂ) := by push_cast
  have hnegLt : -((L : ℂ) * (t : ℂ)) / 2 =
      ((-(L * t) / 2 : ℝ) : ℂ) := by push_cast
  rw [hLt, hnegLt, complexRegularizedArchScale_ofReal,
    complexArchCosSlope_ofReal, complexArchExpSlope_ofReal]
  push_cast

end Zeta23.CCM

#print axioms Zeta23.CCM.complexArchSinc_ofReal
#print axioms Zeta23.CCM.complexRegularizedArchScale_ofReal
#print axioms Zeta23.CCM.complexAlphaCore_ofReal
#print axioms Zeta23.CCM.complexBetaCore_ofReal
#print axioms Zeta23.CCM.complexGammaCore_ofReal
