import Zeta23.CCM.CanonicalSourceEnergy

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: pole lower-bound obligation

The historical pole matrix has an odd rank-one term with a negative sign.
Accordingly this module records a lower bound, not a false PSD assertion.
-/

/-- Uniform cubic lower bound required by the paper-level small-aperture proof. -/
def CanonicalPoleCubicLowerBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      -(2 / 9 : ℝ) * L ^ 3 * ‖x‖ ^ 2 ≤
        matrixRealEnergy (canonicalPoleMatrix L K) x

end Zeta23.CCM
