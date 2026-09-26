import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
SCOUT_DIR = RHRC / "routes" / "R003_ccm_bridge"

class Post249SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post249_is_research_evidence_not_theorem_authority(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 272)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        scout = self.state["post249_research_scout"]
        self.assertEqual(scout["pr"], 249)
        self.assertEqual(scout["validated_head"], "1758ed7fd1fd0bbae6b6929b3793fa8e97288b55")
        self.assertEqual(scout["merge_commit"], "caec6773664458bde0eac55cf1ad60446c385efd")
        self.assertEqual(scout["merge_tree"], "6c5e363e4477cc075ac3779dabc4ce8d27e69674")
        self.assertEqual(scout["evidence_class"], "EXPERIMENTAL_SIGNAL_ONLY")
        self.assertEqual(scout["workflow_harvest"], "11_OF_11_ATTACHED_WORKFLOWS_SUCCESS")
        self.assertFalse(scout["theorem_promotion"])
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_interpretation_repairs_are_locked(self):
        note = (SCOUT_DIR / "POST247_REMAINDER_BUDGET_RATIO_SCOUT_2026_09_23.md").read_text(encoding="utf-8")
        for required in (
            "no asymptotic decay law is claimed",
            "nominal resolution scale",
            "not a hard Fourier cutoff theorem",
            "leading-order `O(δ²)` behavior",
            "certified sign-change brackets",
            "not globally minimal deltas",
            "not a globally self-consistent alternate zeta function",
            "does not rule out PNT-strength",
            "RH remains OPEN",
        ):
            self.assertIn(required, note)
        for forbidden in (
            "super-exponentially small slack",
            "collapses super-exponentially",
            "switches on exactly at the first zeta zero",
            "negative eigenvalue scales as `δ²`",
            "smallest `δ` certified bad",
            "Only the prime-free regime has a real margin",
        ):
            self.assertNotIn(forbidden, note)

    def test_planted_control_scope_is_explicit(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post249_zero_side_perturbation_control"], "BUILT_EXPERIMENTAL_PR_249")
        self.assertEqual(route["post249_globally_consistent_planted_zeta_control"], "OPEN")
        self.assertEqual(route["post249_ratio_asymptotic_rate"], "NOT_ESTABLISHED")
        self.assertEqual(route["post249_first_zero_scale_signal"], "COARSE_GRID_SEPARATION_NOT_EXACT_SWITCH")
        self.assertEqual(
            route["post249_offline_increment_delta_scaling"],
            "LEADING_ORDER_NEAR_ZERO_SIGNAL_NOT_EXACT_GLOBAL_SCALING",
        )
        self.assertEqual(route["post249_sign_change_thresholds"], "CERTIFIED_BRACKETS_NOT_GLOBAL_MINIMA")
        backend = (SCOUT_DIR / "post247_remainder_budget_ratio_scout.py").read_text(encoding="utf-8")
        self.assertIn("not a global minimum certificate", backend)
        self.assertIn("not a globally self-consistent alternate zeta function", backend)

if __name__ == "__main__":
    unittest.main()
