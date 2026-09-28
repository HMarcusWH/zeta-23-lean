import Zeta23.CCM.CanonicalPrimeRemainder

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A3: unconditional all-aperture target

This module lives on the unconditional CCM side of the firewall. It names the
legal-carrier positivity proposition directly and does not import any terminal
adapter or audit module.
-/

def CanonicalAllAperturePositivity : Prop :=
  ∀ L : ℝ, 0 < L →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      BoundaryFlatCoefficients K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) →
      0 ≤ canonicalSourceChannelEnergy L K x

end Zeta23.CCM
