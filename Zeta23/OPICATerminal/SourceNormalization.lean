import Zeta23.OPICATerminal.Common
import Zeta23.OPICARound6.PrimeDeficit.Source
import Zeta23.OPICARound6.NextSearch.SourceEnergies
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

noncomputable section
namespace OPICAExtractionR1

theorem native_literalG_eq_rampG (y : ℝ) :
    Zeta23.OPICARound6.PrimeDeficit.literalG y = rampG y := by
  change discreteG y = rampG y
  exact discreteG_eq_rampG y

def NativeLiteralWindows : Prop := OneSidedWindows Zeta23.OPICARound6.PrimeDeficit.literalG

/-- Actual arithmetic windows remain a hypothesis. -/
theorem native_windows_of_ramp_windows (h : RampWindows) : NativeLiteralWindows :=
  windows_congr (fun y => (native_literalG_eq_rampG y).symm) h

end OPICAExtractionR1
#print axioms OPICAExtractionR1.native_literalG_eq_rampG
#print axioms OPICAExtractionR1.native_windows_of_ramp_windows
