import Zeta23.CCM.UniversalSincPhysicalBounds
import Zeta23.ExceptionalZero.UniversalSincPhysicalDetector

/-! Public visibility of the literal physical source, after density identification. -/

noncomputable section

namespace Zeta23.ExceptionalZero

theorem universalSincPoleKilled_visible_at_offLine_zero {s : ℝ} (hs : 0 < s)
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    paperFT (CCM.universalSincKernel s) (gammaOf (ρ : ℂ)) ≠ 0 :=
  paperFT_originalSincTest_ne_zero_at_off_line_zero hs ρ hoff

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.universalSincPoleKilled_visible_at_offLine_zero
