import Mathlib.Data.Real.Basic

namespace Zeta23.CCM

/-! # Closure campaign B2: keep the three different tails distinct -/

structure CanonicalTailBudget where
  archIntegration : ℝ
  fourierMode : ℝ
  aperture : ℝ
  arch_nonneg : 0 ≤ archIntegration
  fourier_nonneg : 0 ≤ fourierMode
  aperture_nonneg : 0 ≤ aperture

def CanonicalTailBudget.total (b : CanonicalTailBudget) : ℝ :=
  b.archIntegration + b.fourierMode + b.aperture

theorem CanonicalTailBudget.total_nonneg (b : CanonicalTailBudget) :
    0 ≤ b.total := by
  unfold CanonicalTailBudget.total
  linarith [b.arch_nonneg, b.fourier_nonneg, b.aperture_nonneg]

end Zeta23.CCM

#print axioms Zeta23.CCM.CanonicalTailBudget.total_nonneg
