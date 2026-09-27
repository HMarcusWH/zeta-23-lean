import Zeta23.CCM.GroundComparisonPrinciple
import Zeta23.CCM.CanonicalSmallApertureCoercivity
import Zeta23.CCM.GlobalParityBottomSpectrum
import Zeta23.CCM.CanonicalApertureContinuity

namespace Zeta23.CCM

/-!
# Closure campaign A3: canonical ground propagation targets

These propositions are attached to the actual legal successor ground.  They do
not assert propagation.  The fixed-cell target isolates the remaining
first-crossing obstruction from the separately handled prime-power seams.
-/

/-- No negative first crossing inside any physical fixed-cutoff cell. -/
def CanonicalFixedCellGroundPropagation : Prop :=
  ∀ Q N : ℕ, 1 ≤ N →
    ∀ L₀ L : ℝ,
      L₀ ∈ fixedCanonicalCutoffCell Q →
      L ∈ fixedCanonicalCutoffCell Q →
      L₀ ≤ L →
      0 ≤ globalParitySuccessorBottom L₀ N →
      0 ≤ globalParitySuccessorBottom L N

/-- Global nonnegativity propagation for the actual successor legal ground from
one positive base aperture. -/
def CanonicalGlobalGroundPropagation (L₀ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∀ L : ℝ, L₀ ≤ L →
      0 ≤ globalParitySuccessorBottom L₀ N →
      0 ≤ globalParitySuccessorBottom L N

/-- Backward-compatible campaign name, now bound to the actual canonical
ground rather than an arbitrary real function. -/
abbrev CanonicalPropagationCandidate (L₀ : ℝ) : Prop :=
  CanonicalGlobalGroundPropagation L₀

end Zeta23.CCM
