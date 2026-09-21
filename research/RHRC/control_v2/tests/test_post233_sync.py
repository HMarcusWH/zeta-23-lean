import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post233SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post233_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 233)
        self.assertEqual(
            theorem["validated_head"],
            "565428e066004e559490fbe1d21d46ef14494de3",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "9dfee4f50d5b57c92327da564ddf2f6159223fe1",
        )
        self.assertEqual(
            theorem["tree"],
            "5713b8d8088864cb126aae48a3a5a5ac8304807a",
        )
        self.assertEqual(delta["pr"], 233)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_233")
        self.assertEqual(
            delta["theorem_family"],
            "RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK",
        )
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad",
        )
        for decl in (
            "norm_sq_parityCanonicalSourcePairing_le_mul_energy_of_not_parityBad",
            "canonicalOneStepDomination_of_not_parityBad",
            "intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq",
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedCrossParitySourceGramDiskEnergy_of_even_of_not_oddBad",
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedCrossParitySourceGramDisk_of_even_of_not_oddBad",
        ):
            self.assertIn(decl, delta["supporting_declarations"])

    def test_post233_route_state_and_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_233")
        self.assertEqual(route["post233_good_sector_gram"], "PROVED_PR_233")
        self.assertEqual(route["post233_shifted_resolvent_energy"], "PROVED_PR_233")
        self.assertEqual(route["post233_retained_source_gram_disk"], "PROVED_PR_233")
        self.assertEqual(route["post233_sharp_negative_shift_disk"], "PROVED_PR_233")
        self.assertEqual(route["post233_disk_emptiness"], "OPEN_NOT_PROVED")
        self.assertEqual(
            route["good_sector_one_step_domination_independence"],
            "CONSUMED_NOT_INDEPENDENT_PR_233",
        )
        self.assertEqual(
            route["next_research_target"],
            "RETAINED_SOURCE_DISK_SECULAR_INTERSECTION",
        )
        self.assertEqual(
            route["required_new_information"],
            "M4_FREE_RETAINED_DISK_HALFPLANE_COMPATIBILITY",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertTrue(route["canonical_simultaneous_odd_bad_branch"].startswith("OPEN"))
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post233_delta_documents_are_complete(self):
        required_sections = (
            "What became formally true",
            "Workflow harvest",
            "What changed",
            "Upstream implications",
            "Downstream implications",
            "Resurrected routes",
            "New RH-relevant clues",
            "Falsification checks",
            "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_233_GRAM_DISK_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_233_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_match_post233(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #233; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #233",
        )

    def test_control_and_research_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)


if __name__ == "__main__":
    unittest.main()
