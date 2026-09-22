import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post224HistoricalSyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post224_is_preserved_as_historical_theorem_provenance(self):
        note = self.state["control_note"]
        for token in (
            "Post-#224 theorem authority advances to merged-green PR #224",
            "83de9193dffba12097d950d2291348db76d047f7",
            "0f8f5ad468b337622942f76725c9d76db74e27e4",
            "aaedc131612393a1198837b3e5288e48538a94ae",
            "cubicProjectionResidual_eq_oddCubicProjectionSlope_smul",
        ):
            self.assertIn(token, note)
        self.assertGreaterEqual(self.state["merged_theorem_anchor"]["pr"], 227)

    def test_post224_open_targets_are_closed_only_by_later_theorems(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post224_cubic_projection_closed_form"], "PROVED_PR_224")
        self.assertEqual(route["post224_predecessor_correction_proportionality"], "PROVED_PR_226")
        self.assertEqual(route["post224_alpha_gamma_affine_relation"], "PROVED_PR_227")
        self.assertEqual(route["post224_one_coefficient_zero_shift_scalar"], "PROVED_PR_227")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "PROVED_PR_242")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post224_delta_documents_remain_frozen_history(self):
        for path in (
            RHRC / "RESEARCH_LEADS_POST_224_CUBIC_PROJECTION_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_224_DELTA.md",
        ):
            self.assertTrue(path.exists())
            text = path.read_text(encoding="utf-8")
            bad = [
                (i, ord(ch))
                for i, ch in enumerate(text)
                if (ord(ch) < 32 and ch not in "\n\r") or ord(ch) == 127
            ]
            self.assertEqual(bad, [])

    def test_old_route_snapshots_remain_explicitly_historical(self):
        checks = (
            (ROOT / "README.md", "## Historical RH/CCM frontier after PR #215"),
            (RHRC / "README.md", "## Historical post-#215 retained negative-root secular frontier"),
            (RHRC / "CURRENT_RESEARCH_PLAN.md", "## Historical post-#203 — FB-05 / same-state two-parity squeeze"),
            (RHRC / "DOCUMENTATION_AUTHORITY.md", "## Historical post-#215 authority — retained negative-root secular frontier"),
            (RHRC / "VALIDATION_PROTOCOL.md", "## Historical post-#215 validation refinement"),
        )
        for path, marker in checks:
            with self.subTest(path=path):
                self.assertIn(marker, path.read_text(encoding="utf-8"))

if __name__ == "__main__":
    unittest.main()
