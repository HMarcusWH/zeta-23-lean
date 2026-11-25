import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists

/-! Principal arithmetic extraction from the original Alpöge/Claude
source epoch, NOT a call to the external terminal theorem. The original
argument expressions in MainConclusion, EveryCharacterOfLiteratureOfVWin,
SiegelEisensteinSecondTermHypotheses and TopPlug are composed up to TopG.
All input components are closed in the common-pin environment.
-/
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX GlobalTheory.Fc
open UpperTheory.Top
namespace OPICATerminalSupplier

theorem literature_from_original : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
  ⟨UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter,
    UpperTheory.Zero.LLC.recTExists,
    UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter⟩

theorem topG_from_original : TopG := by
  let O := literature_from_original
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let F := UpperTheory.LiteratureTheorems.published_results_first O
  let hAM := UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O
  let hX := SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
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
  have h := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F hAM.1 hAM.2 hX hL (fun cDep =>
      UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
        (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
  exact h.elim fun h =>
    GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
      (UpperTheory.Top.shape_closed_link_n_of_green
        (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters))
      trivial trivial h

end OPICATerminalSupplier
