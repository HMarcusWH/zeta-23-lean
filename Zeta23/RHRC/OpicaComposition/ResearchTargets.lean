import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.OPICARound3.CofinalSimultaneousNegative

/-! OPEN research propositions, not axioms or proofs. The strict opposite-floor
domains are the domains of the actual resolvents. They do not cover a shared
ground eigenvalue; that obstruction is recorded separately below. Neither
normalization of a newborn vector nor a source-only kernel law is assumed. -/
noncomputable section
namespace Zeta23.OPICAComposition
open CCM OPICARound3

/-- LEAD/HYPOTHESIS: an independent real-part source bound on the actual even
resolvent ray at a negative shift strictly below the actual odd floor. OPEN. -/
def EvenRayComparison : Prop :=
  ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ),
    lam < 0 → ∀ (hlam : lam < poleNeutralOddRayleighBottom L K hL hK),
      (correctedCanonicalSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam)).re < 1

/-- LEAD/HYPOTHESIS: the genuine adjoint odd mirror, using the cubic pairing
functional from the public odd secular identity. No sign/conjugation swap. OPEN. -/
def OddAdjointRayComparison : Prop :=
  ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ),
    lam < 0 → ∀ (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK),
      (poleNeutralCubicPairingFunctional L K
        (poleNeutralOddShiftedRay hL K hK lam hlam)).re < 1

/-- The strict-ray proposals leave precisely this negative shared-ground
configuration outside their resolvent domains. This definition does not assert
that such a configuration exists or that it is impossible. -/
def NegativeSharedGroundConfiguration : Prop :=
  ∃ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
    poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK ∧
    poleNeutralEvenRayleighBottom L K hL hK < 0

/-- Separate OPEN source leaf; it is not supplied by either strict ray. -/
def SharedGroundExclusion : Prop := ¬ NegativeSharedGroundConfiguration

/-- OPEN: an independent eventual exclusion. It is not added as a premise to
the stronger original goal. D02 remains conditional on an actual off-line zero
and supplies cofinal counterpressure against this proposed universal bound. -/
def EventualNoSimultaneousNegativity : Prop :=
  ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ K : ℕ, 3 ≤ K → ¬ BothNeutralNegative L K

end Zeta23.OPICAComposition
