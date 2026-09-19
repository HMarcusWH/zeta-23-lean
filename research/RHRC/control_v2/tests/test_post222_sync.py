import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]

class Post222SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_authority_split_is_exact(self):
        merged = self.state["merged_theorem_anchor"]; delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(merged["pr"], 222); self.assertEqual(merged["validated_head"], "c46939488ead9535a63b547c38d64938a882a9f1")
        self.assertEqual(merged["merge_commit"], "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5"); self.assertEqual(merged["tree"], "fd151afbcae3155cc4d32a75da08b6f7e0119099")
        self.assertEqual(delta["pr"], 222); self.assertEqual(delta["validated_head"], "e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543")
        self.assertEqual(delta["tree"], "48d8752950c28e0d3bbd385646e71075abef9e76"); self.assertEqual(delta["status"], "MERGED_VIA_PR_222")
        self.assertEqual(delta["theorem_family"], "BIREGULAR_FIRST_BAD_ZERO_SHIFT_NORMAL_FORM")
        self.assertEqual(delta["final_pr_head"], "c46939488ead9535a63b547c38d64938a882a9f1")
        self.assertEqual(delta["merge_commit"], "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5")
        self.assertEqual(delta["merge_tree"], "fd151afbcae3155cc4d32a75da08b6f7e0119099")
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_biregular_route_is_scalarized_not_closed(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["biregular_first_bad_selection"], "MERGED_PR_222")
        self.assertEqual(route["retained_actual_shell_resonance"], "ELIMINATED_ON_BIREGULAR_RETAINED_STATE_PR_222")
        self.assertEqual(route["retained_source_correction_resonance"], "ELIMINATED_ON_BIREGULAR_RETAINED_STATE_PR_222")
        self.assertEqual(route["retained_transported_index_resonance"], "ELIMINATED_ON_BIREGULAR_RETAINED_STATE_PR_222")
        self.assertEqual(route["canonical_simultaneous_odd_bad_branch"], "OPEN_SCALAR_SIGN_CLASSIFIED_BY_PR_222")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(route["next_research_target"], "RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION")

    def test_post222_delta_has_required_post_green_sections(self):
        text = (RHRC / "RESEARCH_LEADS_POST_222_BIREGULAR_FIRST_BAD_DELTA.md").read_text(encoding="utf-8")
        for heading in ("# What became formally true","# What changed","# Upstream implications","# Downstream implications","# Resurrected routes","# New RH-relevant clues","# Falsification checks","# Highest-leverage next moves","# Standing questions"):
            self.assertIn(heading, text)
        for token in ("exists_both_intrinsicPredecessorRegular_in_open_fixedCell","exists_biRegular_cellMinimal_firstBadCertificate","K(b)","K(a)","K(d)","successorParityBad_iff_zeroShiftShellResponse_re_neg","exists_evenOddZeroShiftScalarNormalForm_of_even","RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION","RH remains OPEN"):
            self.assertIn(token, text)

    def test_post222_obstruction_delta_keeps_obs059i_open(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_222_DELTA.md").read_text(encoding="utf-8")
        for token in ("OBS-059I","OPEN / BIREGULAR-SCALARIZED / CANONICAL-ARITHMETIC-SIGN LAW REQUIRED","K(b)=0","K(a)=0","K(d)=0","Re(α₀ σ_+ + Γ₀ μ₀)","RH remains OPEN"):
            self.assertIn(token, text)

    def test_control_semantics_and_claim_surface_remain_frozen(self):
        action = json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        r003 = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(action["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertEqual([b["id"] for b in action["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]["first_breaks"]], ["E4A4-SCHUR-FB-05"])
        self.assertEqual(r003["phase"], "DISCOVERY"); self.assertFalse(r003["confirmatory_execution_authorized"])
        self.assertIsNone(r003["route_spec_digest"]); self.assertIsNone(r003["boundary_digest"])

if __name__ == "__main__":
    unittest.main()
