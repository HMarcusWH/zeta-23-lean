import Zeta23.CCM.CanonicalSourceEnergy

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: archimedean small-aperture obligations

The full-space inequality remains a useful stronger target, but the RH-relevant
critical path only needs the legal boundary-flat carrier.  Neither proposition
is asserted here; they are explicit proof obligations.
-/

/-- Stronger full-space canonical archimedean upper bound. -/
def CanonicalArchSmallApertureUpperBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      matrixRealEnergy (canonicalArchMatrix L K) x ≤
        (L - 2) * ‖x‖ ^ 2

/-- Critical-path version restricted to the exact legal boundary-flat carrier.
This is weaker than the full-space target and is sufficient for the terminal
finite-Weil positivity route. -/
def CanonicalBoundaryFlatArchSmallApertureUpperBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      BoundaryFlatCoefficients K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) →
      matrixRealEnergy (canonicalArchMatrix L K) x ≤
        (L - 2) * ‖x‖ ^ 2

/-- Any future full-space proof immediately discharges the weaker legal-carrier
obligation. -/
theorem canonicalBoundaryFlatArchSmallApertureUpperBound_of_full
    (h : CanonicalArchSmallApertureUpperBound) :
    CanonicalBoundaryFlatArchSmallApertureUpperBound := by
  intro L hL hsmall K x _hflat
  exact h L hL hsmall K x

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalBoundaryFlatArchSmallApertureUpperBound_of_full
