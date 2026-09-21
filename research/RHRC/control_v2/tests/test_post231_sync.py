import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post231SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_exact_post231_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 231)
        self.assertEqual(theorem["validated_head"], "f9623be705955bd98ef563aa75d3244712009cac")
        self.assertEqual(theorem["merge_commit"], "0d0305da1390206a4531ac2cbca52e45b19f2cad")
        self.assertEqual(theorem["tree"], "5d50bd188db58e76b47e768bcad0e815356fb9dd")
        self.assertEqual(delta["pr"], 231)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_231")
        self.assertEqual(delta["theorem_family"], "CROSS_PARITY_CORRECTION_SOURCE_COUPLING_AND_RETAINED_SOURCE_BALANCE")
        self.assertEqual(delta["exact_promoted_declaration"], "star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling")
        for decl in (
            "star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_channels",
            "star_one_sub_crossParitySecularAlpha_mul_shellInner_eq_cubicShellCoupling",
            "star_one_sub_crossParitySecularGamma_mul_shellInner_eq_cubicShellCoupling",
            "star_crossParitySecularGamma_mul_shellInner_eq_shellInner_sub_cubicShellCoupling",
            "RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalanceFactored_of_even",
            "RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_source_ne_zero",
            "RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad",
        ):
            self.assertIn(decl, delta["supporting_declarations"])

    def test_post231_route_state_and_claim_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_231")
        self.assertEqual(route["post231_correction_source_coupling"], "PROVED_PR_231")
        self.assertEqual(route["post231_source_channel_rewrite"], "PROVED_PR_231")
        self.assertEqual(route["post231_gamma_shell_balance"], "PROVED_PR_231")
        self.assertEqual(route["post231_retained_source_balance_factored"], "PROVED_PR_231")
        self.assertEqual(route["post231_retained_source_balance_source_nonzero"], "PROVED_PR_231")
        self.assertEqual(route["post231_retained_source_balance_odd_good"], "PROVED_PR_231")
        self.assertEqual(route["post231_source_coupling_sign"], "OPEN_NO_SIGN_PROVED")
        self.assertEqual(route["post231_alpha_reality_sign"], "OPEN_MIXED_RESOLVENT_PAIRING")
        self.assertEqual(route["post231_retained_source_gram_disk"], "OPEN_NEXT")
        self.assertEqual(route["next_research_target"], "RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK")
        self.assertEqual(route["required_new_information"], "GOOD_SECTOR_GRAM_CONTROL_COMPOSED_WITH_RETAINED_SOURCE_BALANCE")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertTrue(route["canonical_simultaneous_odd_bad_branch"].startswith("OPEN"))
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_control_and_research_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)

    def test_post231_delta_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications", "Resurrected routes",
            "New RH-relevant clues", "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_231_SOURCE_BALANCE_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_231_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_and_control_readme_match_post231(self):
        self.assertEqual((ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
                         "# RHRC formal audit — merged theorem authority PR #231; research evidence PR #223")
        self.assertEqual((ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
                         "# Fork notes — RHRC current state through merged PR #231")
        text = (RHRC / "control_v2" / "README.md").read_text(encoding="utf-8")
        override = text.split("## Post-#231 current-state override", 1)[1].split(
            "## Post-#229 current-state override", 1
        )[0]
        self.assertIn("RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK", override)
        self.assertIn("GOOD_SECTOR_GRAM_CONTROL_COMPOSED_WITH_RETAINED_SOURCE_BALANCE", override)

    def test_control_semantics_remain_frozen(self):
        action = json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        r003 = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(action["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertEqual([b["id"] for b in action["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]["first_breaks"]], ["E4A4-SCHUR-FB-05"])
        self.assertEqual(r003["phase"], "DISCOVERY")
        self.assertFalse(r003["confirmatory_execution_authorized"])
        self.assertIsNone(r003["route_spec_digest"])
        self.assertIsNone(r003["boundary_digest"])

if __name__ == "__main__":
    unittest.main()
