import Zeta23.ExceptionalZero.TwoTranslateFixedTest

noncomputable section

namespace Zeta23.ExceptionalZero

/-!
# Eventual completeness of the canonical radius family

This module strengthens the single-radius visibility theorem from
`TwoTranslateFixedTest`: a fixed spectral target is visible at every sufficiently
small positive radius.  It then transfers that uniformity through the existing
pole-killing operator and, optionally, to a countable radius sequence.

No positivity statement is made for any detector family.
-/

/-- A complex target is visible to every canonical seed below a radius cutoff. -/
def CanonicalSeedVisibleBelow (w : ℂ) (ε : ℝ) : Prop :=
  ∀ r : PositiveRadius, (r : ℝ) < ε →
    paperFT (canonicalSeedTest r) w ≠ 0

/-- A zeta zero is visible to every canonical pole-killed detector below a radius cutoff. -/
def CanonicalPoleKilledVisibleBelowAtZero
    (ρ₀ : zetaZeroConfig.carrier) (ε : ℝ) : Prop :=
  ∀ r : PositiveRadius, (r : ℝ) < ε →
    paperFT (canonicalPoleKilledTest r) (gammaOf (ρ₀ : ℂ)) ≠ 0

end Zeta23.ExceptionalZero
