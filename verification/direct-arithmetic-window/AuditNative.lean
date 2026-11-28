import Zeta23.RHReference.CofinalEnergyClosure
import Zeta23.RHReference.Step123MomentHandoffAudit
import Zeta23WindowArithmetic.PrincipalNormalization
import DirectWindowAudit.Core

open Lean Elab Command DirectWindowAudit
open Zeta23.RHReference Zeta23.OPICATerminal

set_option maxHeartbeats 0 in
run_cmd
  audit ``Zeta23WindowArithmetic.principal_level_gm_eq_Gz .supplier
    [``Zeta23WindowArithmetic.principal_level_kept] []
  audit ``c1_of_direct_windows .native
    [``literal_energy_le_of_window, ``cofinal_energy_upper_of_windows,
     ``cofinal_normalized_energy_of_power_upper, ``c1_of_cofinal_normalized_energy,
     ``bothParityPowerComparison_proved, ``Deduction.landau_window, ``Deduction.poleData]
    [``bothParityPowerComparison_proved]
  audit ``riemannHypothesis_of_c1_through_generated_pair .native
    [``generated_pair_excludes_c1, ``generated_pair_eventually_refutes_slice_bounds,
     ``Zeta23.ExceptionalZero.exists_generatedStep123CompleteOutput]
    [``generated_pair_excludes_c1]
