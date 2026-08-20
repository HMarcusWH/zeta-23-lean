import Zeta23.WeilEF.Main
import Zeta23.ExceptionalZero.ProbeFamily

namespace Zeta23.ExceptionalZero

/-- The literature-form Weil explicit formula is already proved unconditionally for the concrete
zeta zero configuration used by the exceptional-zero route.  This closes the generic explicit-formula
availability seam; the separate identity connecting a frozen R001 residual to a particular test
family remains an open route theorem. -/
theorem zeta_explicit_formula_literature : Zeta23.EF.EF_lit zetaZeroConfig := by
  simpa [zetaZeroConfig] using Zeta23.WeilEF.EF_lit_zeta zetaSeam

end Zeta23.ExceptionalZero
