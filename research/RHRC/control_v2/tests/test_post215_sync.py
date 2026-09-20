import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post215SyncTests(unittest.TestCase):
    def test_three_anchor_model(self):
        state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))
        theorem = state["merged_theorem_anchor"]
        control = state["merged_control_anchor"]
        self.assertEqual(theorem["pr"], 222)
        self.assertEqual(theorem["validated_head"], "c46939488ead9535a63b547c38d64938a882a9f1")
        self.assertEqual(theorem["merge_commit"], "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5")
        self.assertEqual(theorem["tree"], "fd151afbcae3155cc4d32a75da08b6f7e0119099")
        self.assertEqual(control["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_exact_post215_geometry_is_locked(self):
        text = (RHRC / "RESEARCH_LEADS_POST_215_RETAINED_SECULAR_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "PR #215",
            "5469fbac77c82ccfc9dad0da4c7ce2b0ba67c47a",
            "191b1b648448c92010286dae54df8502df1f55ce",
            "4e6111c974ae8abbf59a5063d4b1ea760fa39ffd",
            "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED",
            "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED",
            "M4 covector = (24,144)",
            "wedge = [-7.92856142933793718521707742118e-7",
            "R_min = [-7.60547660138399452560501190345e-11",
            "R_max = [1.02497161190896926446719955942e-6",
            "retained eigenmode / first-bad restriction was `NOT_TESTED`",
        ):
            self.assertIn(token, text)

    def test_active_route_moves_to_retained_negative_root(self):
        route = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))["active_research_route"]
        self.assertEqual(route["full_space_dual_geometry"], "DUAL_INDEPENDENCE_CERTIFIED_RESEARCH_PR_215")
        self.assertEqual(route["full_space_complete_functional_sign"], "SIGN_INDEFINITE_CERTIFIED_RESEARCH_PR_215")
        self.assertEqual(route["full_space_dual_proportionality"], "FALSIFIED_RESEARCH_PR_215")
        self.assertEqual(route["retained_state_implication"], "BIREGULAR_ZERO_SHIFT_NORMAL_FORM_MERGED_PR_222")
        self.assertEqual(route["contact_locus_route"], "LEAD_REQUIRES_SAME_STATE_CONTACT_BRIDGE")
        self.assertEqual(route["retained_negative_root_secular_route"], "COMPOSED_THROUGH_PR_220")
        self.assertEqual(route["zero_shift_response_route"], "PURE_SIGN_NORMAL_FORM_MERGED_PR_222")
        self.assertEqual(route["resonant_spectral_tube_route"], "GENERIC_THEORY_RETAINED_BUT_ELIMINATED_ON_BIREGULAR_RETAINED_STATE")
        self.assertEqual(route["next_research_target"], "RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION")
        self.assertEqual(route["active_subobligation"], "OBS-059I")

    def test_post215_delta_has_post_green_sections_and_firewalls(self):
        text = (RHRC / "RESEARCH_LEADS_POST_215_RETAINED_SECULAR_DELTA.md").read_text(encoding="utf-8")
        for heading in ("# What became formally true","# What changed","# Upstream implications","# Downstream implications","# Resurrected routes","# New RH-relevant clues","# Falsification checks","# Highest-leverage next moves","# Standing questions"):
            self.assertIn(heading, text)
        for token in ("FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED","FULL_SPACE_SIGN_INDEFINITE_CERTIFIED","crossParityFirstBadRootCertificate","cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root","RETAINED_CROSS_PARITY_SECULAR_COMPLETION","same-state","HYPOTHESIS / template","RH remains OPEN"):
            self.assertIn(token, text)

    def test_dead_routes_are_narrow_not_pair_d_death(self):
        text = (RHRC / "DEAD_ROUTES_POST_215_DELTA.md").read_text(encoding="utf-8")
        for token in ("DR-029","DR-030","universal full-carrier","retained negative-root secular completion","contact route is quarantined, not dead","RH remains OPEN"):
            self.assertIn(token, text)

    def test_claim_and_route_surfaces_remain_unpromoted(self):
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        action_registry = json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsNone(route["route_spec_digest"])
        self.assertIsNone(route["boundary_digest"])
        self.assertEqual(action_registry["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")


if __name__ == "__main__":
    unittest.main()
