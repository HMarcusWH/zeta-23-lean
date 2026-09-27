import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.SourceContraction

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: archimedean small-aperture obligation

This module states the exact inequality needed by the uniform-base assembly.
It deliberately does not install the paper derivation as an axiom.
-/

/-- The canonical archimedean channel must lie below the scalar bound used by
the uniform-base proof. The quantifiers are full-space and uniform in K. -/
def CanonicalArchSmallApertureUpperBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      matrixRealEnergy (canonicalArchMatrix L K) x ≤
        (L - 2) * ‖x‖ ^ 2

end Zeta23.CCM
