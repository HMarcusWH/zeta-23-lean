import Zeta23.CCM.UniversalSincDetector
import Zeta23.ExceptionalZero.WeilFilter

/-!
# The original product multiplier at actual off-line zeros

This is the algebraic visibility component for the exact infinite sinc
product. It does not identify that product with `paperFT q`: constructing
the infinite-convolution density and proving its transform identity remain
necessary before the physical detector visibility theorem is available.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-- The transform multiplier prescribed by the paper source construction. -/
def originalSincMultiplier (s : ℝ) (z : ℂ) : ℂ :=
  -(z ^ 2 + 1 / 4) * CCM.UniversalSinc.product s z

theorem originalSincMultiplier_gammaOf (s : ℝ) (ρ : ℂ) :
    originalSincMultiplier s (gammaOf ρ) =
      ρ * (ρ - 1) * CCM.UniversalSinc.product s (gammaOf ρ) := by
  unfold originalSincMultiplier
  rw [poleKiller_factor_eq]

/-- No visibility premise is accepted: nonvanishing follows from the proved
infinite-product criterion and the actual open-strip zero carrier. -/
theorem originalSincMultiplier_ne_zero_at_off_line_zero {s : ℝ} (hs : 0 < s)
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    originalSincMultiplier s (gammaOf (ρ : ℂ)) ≠ 0 := by
  rw [originalSincMultiplier_gammaOf]
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have hre := ρ.2.2.1
    rw [h] at hre
    simp at hre
  have h1 : (ρ : ℂ) - 1 ≠ 0 := by
    intro h
    have hre := ρ.2.2.2
    rw [sub_eq_zero] at h
    rw [h] at hre
    simp at hre
  have him : (gammaOf (ρ : ℂ)).im ≠ 0 := by
    rw [Zeta23.WeilEF.gammaOf_im]
    exact sub_ne_zero.mpr (Ne.symm hoff)
  exact mul_ne_zero (mul_ne_zero h0 h1)
    (CCM.UniversalSinc.product_ne_zero_of_im_ne_zero hs him)

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.originalSincMultiplier_ne_zero_at_off_line_zero
