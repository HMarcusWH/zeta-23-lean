import Zeta23.OPICARound4.SearchSupport

noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3 Set

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Exact conditional target; its complete closing wrapper is withheld from
the reviewed menu, which must compose the eventual exclusion and D02 consumer. -/
def IntegrationClosureTarget : Prop :=
  EventualActualRayClosure → ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2

/-- Actual native signed response with an explicit OPEN arithmetic margin.
The target contains no proof, and does not assert that its margin holds. -/
def IntegrationSourceBudgetTarget : Prop :=
  ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK),
    0 < poleNeutralOddRayleighBottom L K hL hK - lam →
    (2 * nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ +
      (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
        LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re) / 2 <
      poleNeutralOddRayleighBottom L K hL hK - lam →
    (poleNeutralCorrectedCubicSource L K
      (poleNeutralEvenShiftedRay hL K hK lam hlam)).re < 1

/-- The proposer must construct the actual D03 plane, open its same-state
packet, apply the separately supplied physical cap and identify the conflict.
The complete frame-cap contradiction theorem is withheld from its menu. -/
def IntegrationJointIndexTarget : Prop :=
  ∀ (a b η : ℝ) (K : ℕ) (F : UniformNeutralNegativeFrame a b K η)
    (hη : 0 < η) (L : ℝ) (hL : 0 < L) (hI : L ∈ Icc a b),
    (∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))),
      NativePhysicalNeutralSubspace L K S → StrictlyNegativeNativeSubspace L K S →
        Module.finrank ℂ S ≤ 1) → False

end Zeta23.OPICARound4
