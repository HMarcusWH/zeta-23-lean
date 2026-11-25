import OPICATerminalSupplier.TopGSource
import Zeta23.OPICATerminal.Audit
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd Zeta23.OPICATerminal.Audit.audit
  ``OPICATerminalSupplier.topG_from_original
  [``OPICATerminalSupplier.literature_from_original,
   ``UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter,
   ``UpperTheory.Zero.LLC.recTExists,
   ``UpperTheory.LiteratureTheorems.published_results_eigen,
   ``UpperTheory.LiteratureTheorems.published_results_first,
   ``SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt,
   ``UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound,
   ``GlobalTheory.Fc.forall_goal_of_shape_of_hyps] false
