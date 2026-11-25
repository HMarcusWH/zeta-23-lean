import OPICATerminalSupplier.Principal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

/-! Candidate original-source cut: no final RH/GRH theorem as input. -/
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top
namespace OPICAR2Original

theorem principal_vwin_from_source : VWinAt PChar.one 401 :=
  (UpperTheory.One.vwin_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter) PChar.one

theorem principal_host_from_source :
    HostExW (3 / 2 : ℝ) (GChi PChar.one).req :=
  supplyChi PChar.one principal_vwin_from_source

theorem principal_connected_of_topG (h : TopG) :
    OPICAExtractionR1.PrincipalConnected :=
  OPICAExtractionR1.principal_connected_of_topG_host h principal_host_from_source

theorem principal_windows_of_topG (h : TopG) :
    OPICAExtractionR1.RampWindows :=
  OPICAExtractionR1.principal_ramp_windows_of_connected (principal_connected_of_topG h)

end OPICAR2Original
