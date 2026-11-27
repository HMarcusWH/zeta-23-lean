import Zeta23.RHReference.Step123MomentHandoff
import Lean.Elab.Command

/-! Independent direct proof-value checks for the strict C1 handoff. -/

open Lean Elab Command
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier Zeta23.RHReference

private def requireDirectProofEdges (root : Name) (required : List Name)
    (forbidden : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? root | throwError "Missing root {root}"
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof value {root}"
  let refs := value.getUsedConstantsAsSet
  for name in required do
    unless refs.contains name do throwError "{root} missing direct proof edge to {name}"
  for name in forbidden do
    if refs.contains name then throwError "{root} includes forbidden direct proof edge to {name}"
  logInfo m!"STRICT_C1_PROOF_EDGES_PASS {root} ({required.length} required, {forbidden.length} forbidden)"

run_cmd
  requireDirectProofEdges ``generated_pair_eventually_refutes_slice_bounds
    [``GeneratedStep123CompleteOutput.generated,
     ``GeneratedStep123Output.sourceData,
     ``OriginalDetectorPaddedFinitePhaseData.separation,
     ``OriginalDetectorPaddedFinitePhaseData.separation_gt_scale,
     ``OriginalDetectorPaddedFinitePhaseData.original_depth,
     ``recentered_negative_phase_eventually_relative_margin,
     ``mem_evenMomentSlice_iff, ``mem_oddMomentSlice_iff]
    [``exists_fixed_negative_original_phase,
     ``eventually_no_moment_slice_lower_bound_below_margin]
  requireDirectProofEdges ``generated_pair_excludes_c1
    [``generated_pair_eventually_refutes_slice_bounds]
    [``no_off_line_zero_of_cofinal_moment_slice_bounds]
  requireDirectProofEdges ``riemannHypothesis_of_c1_through_generated_pair
    [``exists_generatedStep123CompleteOutput, ``generated_pair_excludes_c1]
    [``riemannHypothesis_of_cofinal_moment_slice_bounds]
