import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post235SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post235_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 235)
        self.assertEqual(
            theorem["validated_head"],
            "d7ae288e874b2cf3462a8e00c35c7b713607a192",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "0c347a99a02157798109ffb5a4718e201e6fa083",
        )
        self.assertEqual(
            theorem["tree"],
            "ba6d8e6f5a714742353678e36cbc90d869b31798",
        )
        self.assertEqual(delta["pr"], 235)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_235")
        self.assertEqual(
            delta["theorem_family"],
            "RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
        )
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "RegularCellMinimalNegativeEnergyCertificate."
            "oddBad_of_even_of_sourceKernelDeficit_pos_of_sharpExcess_pos",
        )

    def test_post235_route_and_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_235")
        self.assertEqual(
            route["post235_source_kernel_forbidden_quadrant"], "PROVED_PR_235"
        )
        self.assertEqual(route["post235_deficit_excess_interface"], "PROVED_PR_235")
        self.assertEqual(
            route["next_research_target"],
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
        )
        self.assertEqual(
            route["required_new_information"],
            "CONJUGATION_COMPATIBLE_CANONICAL_NORMALIZATION",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post235_delta_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_235_SOURCE_KERNEL_QUADRANT_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_235_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_match_post235(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #235; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #235",
        )


if __name__ == "__main__":
    unittest.main()
