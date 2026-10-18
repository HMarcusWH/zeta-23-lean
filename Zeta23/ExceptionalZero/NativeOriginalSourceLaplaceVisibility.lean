import Zeta23.ExceptionalZero.UniversalSincNativeSourceIdentification

/-!
# Laplace visibility of the actual native twice pole-killed source

The source is j = P²q. Its transform has one copy of the original infinite
product Q, rather than the two copies occurring in the detector correlation
k*k. The paper Fourier convention has the opposite sign to the Laplace
convention at gamma(rho); the actual source's proved evenness pays that sign.
-/

noncomputable section

open MeasureTheory Complex

namespace Zeta23.CCM

def nativeOriginalSourceLaplace (w : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * (nativeOriginalSource u : ℂ)

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

theorem nativeOriginalSourceLaplace_eq_paperFT (w : ℂ) :
    CCM.nativeOriginalSourceLaplace w =
      paperFT (originalSincSecondTest CCM.UniversalSinc.fixedScale) (I * w) := by
  unfold CCM.nativeOriginalSourceLaplace paperFT
  apply integral_congr_ae
  filter_upwards with u
  rw [nativeOriginalSource_cast_eq_physical]
  have hi : I * (I * w) * (u : ℂ) = -w * (u : ℂ) := by
    calc
      _ = (I * I) * w * (u : ℂ) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [hi, mul_comm]

/-- The literal twice pole-killed native source retains exactly one Q. -/
theorem nativeOriginalSourceLaplace_formula (w : ℂ) :
    CCM.nativeOriginalSourceLaplace w =
      ((I * w) ^ 2 + 1 / 4) ^ 2 * CCM.UniversalSinc.product CCM.UniversalSinc.fixedScale (I * w) := by
  rw [nativeOriginalSourceLaplace_eq_paperFT,
    paperFT_originalSincSecondTest CCM.UniversalSinc.fixedScale_pos]

theorem nativeOriginalSourceLaplace_at_zero (rho : ℂ) :
    CCM.nativeOriginalSourceLaplace (rho - 1 / 2) =
      paperFT (originalSincSecondTest CCM.UniversalSinc.fixedScale) (gammaOf rho) := by
  rw [nativeOriginalSourceLaplace_eq_paperFT]
  have hsign : I * (rho - 1 / 2) = -gammaOf rho := by
    unfold gammaOf
    rw [div_I]
    ring
  rw [hsign, paperFT_neg_eq_paperFT_of_even
    (originalSincSecondTest_even CCM.UniversalSinc.fixedScale_pos)]

/-- Nonvanishing is proved for the actual j transform, not borrowed from
the distinct detector autocorrelation transform. No simplicity is assumed. -/
theorem nativeOriginalSourceLaplace_ne_zero_at_off_line_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    CCM.nativeOriginalSourceLaplace ((rho : ℂ) - 1 / 2) ≠ 0 := by
  rw [nativeOriginalSourceLaplace_at_zero, paperFT_originalSincSecondTest
    CCM.UniversalSinc.fixedScale_pos]
  have hm := originalSincMultiplier_ne_zero_at_off_line_zero
    CCM.UniversalSinc.fixedScale_pos rho hoff
  have hp : (gammaOf (rho : ℂ)) ^ 2 + 1 / 4 ≠ 0 := by
    intro hz
    apply hm
    unfold originalSincMultiplier
    rw [hz, neg_zero, zero_mul]
  have hQ : CCM.UniversalSinc.product CCM.UniversalSinc.fixedScale (gammaOf (rho : ℂ)) ≠ 0 := by
    intro hz
    apply hm
    unfold originalSincMultiplier
    rw [hz, mul_zero]
  exact mul_ne_zero (pow_ne_zero 2 hp) hQ

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nativeOriginalSourceLaplace_formula
#print axioms Zeta23.ExceptionalZero.nativeOriginalSourceLaplace_at_zero
#print axioms Zeta23.ExceptionalZero.nativeOriginalSourceLaplace_ne_zero_at_off_line_zero
