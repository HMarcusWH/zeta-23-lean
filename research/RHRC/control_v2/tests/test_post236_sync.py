import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post236SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post236_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 236)
        self.assertEqual(
            theorem["validated_head"],
            "45491342f5661429679579c7889c1ad8b96728b6",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "a66e1c617033f4adaa52e935668399efb93048ac",
        )
        self.assertEqual(
            theorem["tree"],
            "5ef597b1d75075ec2299261a4193432a36932ffe",
        )
        self.assertEqual(delta["pr"], 236)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_236")
        self.assertEqual(
            delta["theorem_family"],
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
        )
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "RegularCellMinimalNegativeEnergyCertificate."
            "oddBad_of_even_of_realSourceDeficit_pos_of_radius_gap",
        )

    def test_post236_route_and_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_236")
        self.assertEqual(route["post236_canonical_real_phase_collapse"], "PROVED_PR_236")
        self.assertEqual(route["post236_source_kernel_reality"], "PROVED_PR_236")
        self.assertEqual(route["post236_one_real_scalar_reduction"], "PROVED_PR_236")
        self.assertEqual(
            route["next_research_target"],
            "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
        )
        self.assertEqual(
            route["required_new_information"],
            "REALITY_OF_RETAINED_M4_AND_SCALAR_COMPOSITION",
        )
        self.assertEqual(route["post236_sharp_radius_shell_barrier"], "OPEN_NOT_PROVED")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post236_delta_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_236_REAL_PHASE_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_236_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_match_post236(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #236; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #236",
        )


if __name__ == "__main__":
    unittest.main()
