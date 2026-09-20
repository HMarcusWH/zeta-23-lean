import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]

class Post224SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post224_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 224)
        self.assertEqual(theorem["validated_head"], "83de9193dffba12097d950d2291348db76d047f7")
        self.assertEqual(theorem["merge_commit"], "0f8f5ad468b337622942f76725c9d76db74e27e4")
        self.assertEqual(theorem["tree"], "aaedc131612393a1198837b3e5288e48538a94ae")
        self.assertEqual(delta["pr"], 224)
        self.assertEqual(delta["theorem_family"], "ODD_CUBIC_PROJECTION_CLOSED_FORM")
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "cubicProjectionResidual_eq_oddCubicProjectionSlope_smul",
        )

    def test_post224_does_not_overclaim_correction_collapse(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post224_cubic_projection_closed_form"], "PROVED_PR_224")
        self.assertEqual(route["post224_predecessor_correction_proportionality"], "OPEN_NEXT")
        self.assertEqual(route["post224_alpha_gamma_affine_relation"], "DERIVED_CONDITIONAL_NOT_FORMALIZED")
        self.assertEqual(route["post224_one_coefficient_zero_shift_scalar"], "DERIVED_CONDITIONAL_NOT_FORMALIZED")
        self.assertEqual(route["next_research_target"], "CROSS_PARITY_PREDECESSOR_CORRECTION_PROPORTIONALITY")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post223_research_and_control_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)

if __name__ == "__main__":
    unittest.main()
