import Zeta23.RHReference.DirectWindowSource
import Zeta23.RHReference.CofinalEnergyClosure

/-!
# Direct arithmetic windows to the native generated-pair terminal

The original arithmetic construction supplies the complete literal windows.
The native consumer integrates their positive energy, obtains cofinal moment
bounds at the original cutoff, and uses the actual generated trial pair.
-/

set_option autoImplicit false

namespace Zeta23.RHReference

/-- Unconditional terminal bound to the original pre-zero-exclusion supplier. -/
theorem riemannHypothesis_direct_arithmetic_windows : RiemannHypothesis :=
  riemannHypothesis_of_direct_windows principal_literal_windows

end Zeta23.RHReference

#print axioms Zeta23.RHReference.riemannHypothesis_direct_arithmetic_windows
