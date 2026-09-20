import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post229SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_exact_post229_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 229)
        self.assertEqual(theorem["validated_head"], "9d4f81c171264be424fbac40f1211263c3cc6abd")
        self.assertEqual(theorem["merge_commit"], "992398c810de5fb84919846fc4192d709d51e783")
        self.assertEqual(theorem["tree"], "d9ae07d1ca92cb23b4a3ae3ccae0b32e9b7d38c8")
        self.assertEqual(delta["pr"], 229)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_229")
        self.assertEqual(delta["theorem_family"], "CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION")
        self.assertEqual(delta["exact_promoted_declaration"], "oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div")
        self.assertIn("one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div", delta["supporting_declarations"])
        self.assertIn("one_sub_crossParitySecularGamma_eq_resolvent_pairing_div", delta["supporting_declarations"])

    def test_post229_route_state_and_claim_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post229_correction_functional_riesz"], "PROVED_PR_229")
        self.assertEqual(route["post229_alpha_mixed_resolvent_formula"], "PROVED_PR_229")
        self.assertEqual(route["post229_gamma_mixed_resolvent_formula"], "PROVED_PR_229")
        self.assertEqual(route["post229_alpha_reality_sign"], "OPEN_MIXED_RESOLVENT_PAIRING")
        self.assertEqual(route["post229_source_coupling_bridge"], "OPEN_NEXT")
        self.assertEqual(route["post229_retained_source_balance"], "OPEN_NEXT")
        self.assertEqual(route["next_research_target"], "CROSS_PARITY_CORRECTION_SOURCE_COUPLING")
        self.assertEqual(route["required_new_information"], "CANONICAL_SOURCE_COUPLING_AND_RETAINED_SOURCE_BALANCE")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_research_and_control_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)

    def test_post229_delta_documents_are_clean_and_complete(self):
        required_sections = ("What became formally true","Workflow harvest","What changed","Upstream implications","Downstream implications","Resurrected routes","New RH-relevant clues","Falsification checks","Highest-leverage next moves")
        for path in (RHRC / "RESEARCH_LEADS_POST_229_RIESZ_DELTA.md", RHRC / "OBSTRUCTION_LEDGER_POST_229_DELTA.md"):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)
            bad = [(i, ord(ch)) for i, ch in enumerate(text) if (ord(ch) < 32 and ch not in "\n\r") or ord(ch) == 127]
            self.assertEqual(bad, [])

    def test_post229_current_headings(self):
        self.assertEqual((ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0], "# RHRC formal audit — merged theorem authority PR #229; research evidence PR #223")
        self.assertEqual((ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0], "# Fork notes — RHRC current state through merged PR #229")

if __name__ == "__main__":
    unittest.main()
