import Zeta23.ExceptionalZero.Cancellation

namespace Zeta23.ExceptionalZero

/-- A probe family packages only the response function at this stage. Extra admissibility conditions
    should be added when a concrete Weil/aperture family is selected. -/
structure ProbeFamily (ι : Type) where
  response : ι → ℝ → ℝ

end Zeta23.ExceptionalZero
