import Zeta23.CCM.GroundComparisonPrinciple
import Zeta23.CCM.CanonicalSmallApertureCoercivity

namespace Zeta23.CCM

/-!
# Closure campaign A3: canonical propagation target shape

The campaign's decisive missing theorem is represented by an explicit
predicate over the legal-ground function supplied by any concrete application.
No assertion that the canonical ground satisfies it is made here.
-/

def CanonicalPropagationCandidate
    (ground : ℝ → ℝ) (L0 : ℝ) : Prop :=
  GroundNonnegativityPropagation ground L0

end Zeta23.CCM
