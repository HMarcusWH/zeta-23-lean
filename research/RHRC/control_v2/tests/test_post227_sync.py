import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post227SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post227_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 227)
        self.assertEqual(theorem["validated_head"], "b8d29733167a95e16f5721eddfced6b650a3b641")
        self.assertEqual(theorem["merge_commit"], "7aace87a5644f837e2c8b64bdcf5e66b2dc0b020")
        self.assertEqual(theorem["tree"], "1dd1cdefcf4f4f7929b310697fdd1615a861ca1a")
        self.assertEqual(delta["pr"], 227)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_227")
        self.assertEqual(delta["theorem_family"], "CROSS_PARITY_ONE_COEFFICIENT_TRANSFER_COLLAPSE")
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftOneCoefficientNormalForm_of_even",
        )
        self.assertEqual(delta["prerequisite_theorem_pr"], 226)
        self.assertEqual(
            delta["prerequisite_theorem_declaration"],
            "oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul",
        )

    def test_post227_route_state_and_claim_firewall(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post224_predecessor_correction_proportionality"], "PROVED_PR_226")
        self.assertEqual(route["post224_alpha_gamma_affine_relation"], "PROVED_PR_227")
        self.assertEqual(route["post224_one_coefficient_zero_shift_scalar"], "PROVED_PR_227")
        self.assertEqual(route["post227_safe_negative_shift_one_coefficient_transfer"], "PROVED_PR_227")
        self.assertEqual(route["post227_zero_shift_one_coefficient_transfer"], "PROVED_PR_227")
        self.assertEqual(route["post227_kernel_direction_collapse"], "PROVED_PR_227")
        self.assertEqual(route["post227_biregular_selected_even_normal_form"], "PROVED_PR_227")
        self.assertEqual(route["post227_alpha_reality_sign"], "OPEN_MIXED_RESOLVENT_PAIRING")
        self.assertEqual(
            route["next_research_target"],
            "CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION",
        )
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["parity_complete_retained_state_exclusion"], "OPEN")
        self.assertEqual(route["terminal_mathlib_rh_seam"], "OPEN")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_research_and_control_anchors_do_not_move(self):
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)

    def test_post227_delta_documents_are_clean_and_complete(self):
        required_sections = (
            "What became formally true",
            "What changed",
            "Upstream implications",
            "Downstream implications",
            "Resurrected routes",
            "New RH-relevant clues",
            "Falsification checks",
            "Highest-leverage next moves",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_227_ONE_COEFFICIENT_TRANSFER_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_227_DELTA.md",
        ):
            with self.subTest(path=path):
                text = path.read_text(encoding="utf-8")
                for section in required_sections:
                    self.assertIn(section, text)
                bad = [
                    (i, ord(ch))
                    for i, ch in enumerate(text)
                    if (ord(ch) < 32 and ch not in "\n\r") or ord(ch) == 127
                ]
                self.assertEqual(bad, [])

    def test_post227_current_headings(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #227; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #227",
        )

if __name__ == "__main__":
    unittest.main()
