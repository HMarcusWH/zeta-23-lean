import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post237SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post237_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 237)
        self.assertEqual(theorem["validated_head"], "8b7ba6b25c6f8977ff27890196e5b43ca3459b78")
        self.assertEqual(theorem["merge_commit"], "267d417216f1731c6860b7553ba87397843fe258")
        self.assertEqual(theorem["tree"], "28b22a2a4c96f32874fc09cd1e73f2fb09807e9d")
        self.assertEqual(delta["pr"], 237)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_237")
        self.assertEqual(delta["theorem_family"], "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR")
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "RegularCellMinimalNegativeEnergyCertificate."
            "retainedRealCompletedSourceCorridor_of_even_of_not_oddBad",
        )

    def test_post237_route_and_claim_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post237_real_completed_source_corridor"], "PROVED_PR_237")
        self.assertEqual(route["post237_m4_reality"], "PROVED_PR_237")
        self.assertEqual(route["post237_completed_source_reality"], "PROVED_PR_237")
        self.assertEqual(route["post237_budget_disk_scalarization"], "PROVED_PR_237")
        self.assertEqual(route["post237_source_m4_coercivity"], "PROVED_PR_237")
        self.assertEqual(
            route["post237_retained_gamma_reality"],
            "DERIVED_NOT_SEPARATELY_FORMALIZED",
        )
        self.assertEqual(route["post237_gamma_sign"], "OPEN")
        self.assertEqual(
            route["post237_generic_safe_shift_transfer_reality"],
            "OPEN_NEXT_THEOREM_TARGET",
        )
        self.assertEqual(
            route["next_research_target"],
            "CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post237_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_237_COMPLETED_SOURCE_CORRIDOR_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_237_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

        reconciliation = (
            RHRC / "HISTORICAL_ROUTE_AUDIT_POST_237_RECONCILIATION.md"
        ).read_text(encoding="utf-8")
        for token in (
            "non-authoritative hypothesis map",
            "PR #237 real completed-source corridor",
            "Strongest explicit independent fallback",
            "generic safe-shift Gamma/alpha reality",
            "RH remains OPEN",
        ):
            self.assertIn(token, reconciliation)

        dead = (RHRC / "DEAD_ROUTES_POST_237_DELTA.md").read_text(encoding="utf-8")
        self.assertIn("mixed-pairing reality from canonical conjugation symmetry", dead)
        self.assertIn("Rsharp <= q^2", dead)

    def test_current_headings_match_post237(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #237; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #237",
        )


if __name__ == "__main__":
    unittest.main()
