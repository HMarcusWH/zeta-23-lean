import Zeta23.OPICATerminal.Common
import Zeta23.OPICARound6.PrimeDeficit.Source

noncomputable section
namespace OPICAExtractionR1

theorem native_literalG_eq_rampG (y : ℝ) :
    Zeta23.OPICARound6.PrimeDeficit.literalG y = rampG y := by
  change discreteG y = rampG y
  exact discreteG_eq_rampG y

end OPICAExtractionR1
