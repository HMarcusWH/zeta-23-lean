import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post242SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post242_theorem_provenance_survives_later_authority(self):
        note = self.state["control_note"]
        for token in (
            "PR #242",
            "d4ccbd67223278e95e3aef728f0f42891aff6fd7",
            "d2ba055243cdf0765a58ce2068a98744b7ae9432",
            "0f4f82b5fc43024c52c75ec8940108830ceaf7c1",
            "NoRegularFirstBadCertificates -> Mathlib.RiemannHypothesis",
        ):
            self.assertIn(token, note)
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 245)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 245)

    def test_post239_post240_post242_route_state_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(
            route["post239_generic_safe_shift_transfer_reality"],
            "PROVED_PR_239",
        )
        self.assertEqual(route["post239_retained_gamma_reality"], "PROVED_PR_239")
        self.assertEqual(route["post239_retained_alpha_reality"], "PROVED_PR_239")
        self.assertEqual(
            route["post240_gamma_obstruction_normal_form"], "PROVED_PR_240"
        )
        self.assertEqual(
            route["post240_positive_center_deficit_transfer_escape"],
            "PROVED_PR_240",
        )
        self.assertEqual(route["post240_center_deficit_positive"], "OPEN_NOT_PROVED")
        self.assertEqual(route["post242_terminal_mathlib_rh_seam"], "PROVED_PR_242")
        self.assertEqual(
            route["post242_no_regular_first_bad_certificates"],
            "OPEN_STRONG_SUFFICIENT_ENDPOINT",
        )
        self.assertEqual(route["next_research_target"], "CANONICAL_PRIME_REMAINDER_DOMINANCE")
        self.assertEqual(
            route["required_new_information"],
            "RH_STRENGTH_WEIGHTED_CHEBYSHEV_REMAINDER_INFORMATION",
        )
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post242_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for p in (
            RHRC / "RESEARCH_LEADS_POST_242_TERMINAL_PROVENANCE_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_242_DELTA.md",
            RHRC / "DEAD_ROUTES_POST_242_DELTA.md",
        ):
            text = p.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

        reconciliation = (
            RHRC / "HISTORICAL_ROUTE_AUDIT_POST_242_RECONCILIATION.md"
        ).read_text(encoding="utf-8")
        for token in (
            "Odd-selected is not a blank branch",
            "Safe-shift reality is closed",
            "#240 is conditional on positive center deficit",
            "The Mathlib seam is closed",
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
            "RH remains OPEN",
        ):
            self.assertIn(token, reconciliation)

    def test_current_headings_match_post245(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #245; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #245",
        )


if __name__ == "__main__":
    unittest.main()
