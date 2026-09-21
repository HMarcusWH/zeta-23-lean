import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post234SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post234_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 234)
        self.assertEqual(
            theorem["validated_head"],
            "6d9b60752f7a4f164113bb0602fcdee87e2a54a1",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "b18d81f11a04982e438b7e196853ae665dab0cc2",
        )
        self.assertEqual(
            theorem["tree"],
            "94a0db085c35d2aba753a8359e452e4189c5c897",
        )
        self.assertEqual(delta["pr"], 234)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_234")
        self.assertEqual(
            delta["theorem_family"],
            "RETAINED_SOURCE_DISK_SECULAR_INTERSECTION",
        )
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedSourceRealPartOrSharpRadius_of_even_of_not_oddBad",
        )
        for decl in (
            "complexDisk_halfPlane_gap_sq_le",
            "complexDisk_halfPlane_support_dichotomy",
            "re_star_mul_cubicShellSelf_eq_norm_sq_mul_re",
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedDiskSecularIntersectionSharp_of_even_of_not_oddBad",
            "RegularCellMinimalNegativeEnergyCertificate."
            "evenShiftedDiskSecularIntersection_of_even_of_not_oddBad",
        ):
            self.assertIn(decl, delta["supporting_declarations"])

    def test_post234_route_state_and_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_234")
        self.assertEqual(route["post234_disk_secular_intersection"], "PROVED_PR_234")
        self.assertEqual(route["post234_m4_elimination"], "PROVED_PR_234")
        self.assertEqual(route["post234_source_real_radius_dichotomy"], "PROVED_PR_234")
        self.assertEqual(
            route["post234_source_kernel_forbidden_quadrant"],
            "OPEN_NEXT_THEOREM_INTERFACE",
        )
        self.assertEqual(
            route["post234_numerical_prerequisite"],
            "CANONICAL_CUBIC_SHELL_NORMALIZATION",
        )
        self.assertEqual(
            route["post234_latest_shifted_state_scout"],
            "672_ATTEMPTED_0_SHIFTED_STATES",
        )
        self.assertEqual(
            route["next_research_target"],
            "RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
        )
        self.assertEqual(
            route["required_new_information"],
            "CANONICAL_SOURCE_DEFICIT_AND_EXCESS_SIGN_CONTROL",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertTrue(route["canonical_simultaneous_odd_bad_branch"].startswith("OPEN"))
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post234_delta_documents_are_complete(self):
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
            RHRC / "RESEARCH_LEADS_POST_234_DISK_SECULAR_INTERSECTION_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_234_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_match_post234(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #234; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #234",
        )

    def test_control_and_research_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)


if __name__ == "__main__":
    unittest.main()
