import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post215SyncTests(unittest.TestCase):
    def test_three_anchor_model(self):
        state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))
        theorem = state["merged_theorem_anchor"]
        research = state["latest_research_evidence"]
        control = state["merged_control_anchor"]
        self.assertEqual(theorem["pr"], 220)
        self.assertEqual(theorem["validated_head"], "f61844ed2c0ae3a83fca20f0d287e0b66d2bf64b")
        self.assertEqual(theorem["merge_commit"], "d1ce40c83f4771be6529119fbdda9598bf07baad")
        self.assertEqual(theorem["tree"], "c127bf1a5fa6394eadd435d613ced0d1b2b178bd")
        self.assertEqual(research["pr"], 215)
        self.assertEqual(research["validated_head"], "5469fbac77c82ccfc9dad0da4c7ce2b0ba67c47a")
        self.assertEqual(research["merge_commit"], "191b1b648448c92010286dae54df8502df1f55ce")
        self.assertEqual(research["tree"], "4e6111c974ae8abbf59a5063d4b1ea760fa39ffd")
        self.assertEqual(research["disposition"], "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED")
        self.assertEqual(research["sign_route_classification"], "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED")
        self.assertEqual(research["control_transfer_status"], "DUAL_INDEPENDENCE_SURVIVES_Q13_Q15_CONTROLS")
        self.assertFalse(research["theorem_promotion"])
        self.assertEqual(control["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_exact_post215_geometry_is_locked(self):
        research = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))["latest_research_evidence"]
        self.assertEqual(research["predecessor_N"], 2)
        self.assertEqual(research["successor_K"], 3)
        self.assertEqual(research["selected_parity"], "even")
        self.assertEqual(research["primary_Q"], 14)
        self.assertEqual(research["moment_four_covector"], ["24", "144"])
        self.assertEqual(research["primary_wedge"], "-7.92856142933793718521707742118e-7")
        self.assertEqual(research["primary_R_min"], "-7.60547660138399452560501190345e-11")
        self.assertEqual(research["primary_R_max"], "1.02497161190896926446719955942e-6")
        self.assertEqual(research["retained_state_implication"], "NOT_TESTED")

    def test_active_route_moves_to_retained_negative_root(self):
        route = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))["active_research_route"]
        self.assertEqual(route["full_space_dual_geometry"], "DUAL_INDEPENDENCE_CERTIFIED_RESEARCH_PR_215")
        self.assertEqual(route["full_space_complete_functional_sign"], "SIGN_INDEFINITE_CERTIFIED_RESEARCH_PR_215")
        self.assertEqual(route["full_space_dual_proportionality"], "FALSIFIED_RESEARCH_PR_215")
        self.assertEqual(route["retained_state_implication"], "THEOREM_COMPOSED_THROUGH_PR_220_AND_CLASSIFIED_PR_221_DELTA")
        self.assertEqual(route["contact_locus_route"], "LEAD_REQUIRES_SAME_STATE_CONTACT_BRIDGE")
        self.assertEqual(route["retained_negative_root_secular_route"], "COMPOSED_THROUGH_PR_220")
        self.assertEqual(route["zero_shift_response_route"], "CLASSIFIED_BY_VALIDATED_PR_221_DELTA")
        self.assertEqual(route["resonant_spectral_tube_route"], "RESURRECTED_ACTIVE_SECONDARY")
        self.assertEqual(route["next_research_target"], "RETAINED_BRANCH_ARITHMETIC_DISCRIMINATION")
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
