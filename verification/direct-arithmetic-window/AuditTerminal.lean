import Zeta23.RHReference.DirectWindowAdapter
import DirectWindowAudit.Core

open Lean Elab Command DirectWindowAudit
open Zeta23.RHReference Zeta23.OPICATerminal

set_option maxHeartbeats 0 in
run_cmd
  audit ``riemannHypothesis_direct_arithmetic_windows .terminal
    [``Zeta23WindowArithmetic.principal_original_windows,
     ``Zeta23WindowArithmetic.arithmeticInputs,
     ``Zeta23WindowArithmetic.principal_level_gm_eq_Gz,
     ``originalGz_eq_literalG, ``principal_literal_windows,
     ``literal_energy_le_of_window, ``cofinal_energy_upper_of_windows,
     ``cofinal_normalized_energy_of_power_upper, ``c1_of_cofinal_normalized_energy,
     ``c1_of_direct_windows, ``bothParityPowerComparison_proved,
     ``riemannHypothesis_of_c1_through_generated_pair,
     ``generated_pair_excludes_c1, ``generated_pair_eventually_refutes_slice_bounds]
    [``riemannHypothesis_of_direct_windows, ``principal_literal_windows]
    (some ``RiemannHypothesis)
