import Zeta23.ExceptionalZero.CanonicalArithmeticCriterion

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-!
# Closure campaign A3: exact all-aperture target

This is a stable name for the already-audited final positivity proposition.
No new proof of the proposition is asserted.
-/

abbrev CanonicalAllAperturePositivity : Prop :=
  CanonicalFiniteWeilPositivity

theorem canonicalAllAperturePositivity_iff_riemannHypothesis :
    CanonicalAllAperturePositivity ↔ RiemannHypothesis :=
  canonicalFiniteWeilPositivity_iff_riemannHypothesis

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalAllAperturePositivity_iff_riemannHypothesis
