import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

/-!
# Original arithmetic inputs before zero exclusion

This adapter assembles `TopG` and `VWin` from the original arithmetic source at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The imported source supplies the Galois row, local correspondence, theta and
covolume theorems.  The assembly stops before the original zero-free consumer.

Some upstream modules also contain terminal declarations.  They are not applied
here; the dedicated declaration-dependency audit checks this distinction.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

namespace Zeta23WindowArithmetic

/-- The source-proved arithmetic inputs, with no residual literature premise. -/
theorem arithmeticInputs : UpperTheory.Top.TopG ∧ UpperTheory.Top.VWin := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let F := UpperTheory.LiteratureTheorems.published_results_first O
  let hA :=
    (UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).1
  let hM :=
    (UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).2
  let hX :=
    SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
      (UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O)
      (UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O)
      (UpperTheory.LiteratureTheorems.poincare_lelong_inv_of_literature O)
      PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
      PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
      (UpperTheory.LiteratureTheorems.fargues_exact_of_literature O)
      (UpperTheory.LiteratureTheorems.zarhin_statement O)
      (UpperTheory.LiteratureTheorems.nef_rr_of_literature O)
      (UpperTheory.LiteratureTheorems.siegel_toroidal_integral_of_literature O)
      (UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O)
      (UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O)
      (UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O)
      (UpperTheory.LiteratureTheorems.ar_degree_of_literature O)
      (UpperTheory.LiteratureTheorems.published_results_arithmetic O)
      (UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O)
  let hL := UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O
  have hGreen : GlobalTheory.GLq.Green :=
    GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters
  have hHyps :=
    UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
      P F hA hM hX hL
      (fun cDep =>
        UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
          (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
  obtain ⟨H⟩ := hHyps
  refine ⟨?_, UpperTheory.One.vwin_of_row row⟩
  exact GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
    (UpperTheory.Top.shape_closed_link_n_of_green hGreen)
    trivial trivial H

end Zeta23WindowArithmetic
