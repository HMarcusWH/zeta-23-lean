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

    def test_post224_math_docs_have_no_embedded_control_bytes(self):
        paths = (
            RHRC / "RESEARCH_LEADS_POST_224_CUBIC_PROJECTION_DELTA.md",
            RHRC / "RESEARCH_LEADS.md",
            RHRC / "OBSTRUCTION_LEDGER.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_224_DELTA.md",
        )
        for path in paths:
            with self.subTest(path=path):
                text = path.read_text(encoding="utf-8")
                bad = [
                    (i, ord(ch))
                    for i, ch in enumerate(text)
                    if (ord(ch) < 32 and ch not in "\n\r") or ord(ch) == 127
                ]
                self.assertEqual(bad, [])

    def test_post224_authority_headings_are_current(self):
        audit = (RHRC.parent.parent / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0]
        fork = (RHRC.parent.parent / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0]
        self.assertEqual(
            audit,
            "# RHRC formal audit — merged theorem authority PR #224; research evidence PR #223",
        )
        self.assertEqual(
            fork,
            "# Fork notes — RHRC current state through merged PR #224",
        )

    def test_post224_operational_route_points_to_predecessor_correction(self):
        for rel in (
            Path("routes/R003_ccm_bridge/README.md"),
            Path("FB05_INCOMPATIBILITY_PROGRAM.md"),
        ):
            with self.subTest(path=rel):
                text = (RHRC / rel).read_text(encoding="utf-8")
                self.assertIn("CROSS_PARITY_PREDECESSOR_CORRECTION_PROPORTIONALITY", text)
                self.assertIn(
                    "HISTORICAL / DOWNSTREAM AFTER PREDECESSOR COLLAPSE",
                    text,
                )
                self.assertNotIn("**ACTIVE / HIGHEST INFORMATION.**", text)

if __name__ == "__main__":
    unittest.main()
