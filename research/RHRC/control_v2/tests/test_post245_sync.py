import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent
sys.path.insert(0, str(RHRC / "tools"))

import arithmetic_firewall_lint  # noqa: E402


class Post245SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_exact_post245_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 245)
        self.assertEqual(
            theorem["validated_head"], "766579346ec86b25d63fb61f8e0b46752a028f6c"
        )
        self.assertEqual(
            theorem["merge_commit"], "ad0347ef07e2c7717f88bd9d8bf7555be75ad88e"
        )
        self.assertEqual(theorem["tree"], "0466006ec23b3f24f6ea113b303014ae42a680dd")
        self.assertEqual(delta["pr"], 245)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_245")
        self.assertEqual(delta["theorem_family"], "TERMINAL_GATE_RH_EQUIVALENCE")
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "Zeta23.ExceptionalZero."
            "noArbitrarilyLargeWholeCellRetainedFamily_iff_riemannHypothesis",
        )
        self.assertIn(
            "Zeta23.ExceptionalZero.noRegularFirstBadCertificates_iff_riemannHypothesis",
            delta["supporting_declarations"],
        )

    def test_route_has_no_sub_rh_gate_and_rh_stays_open(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["terminal_mathlib_rh_seam"], "PROVED_PR_242")
        self.assertEqual(
            route["post245_no_regular_first_bad_certificates"], "RH_EQUIVALENT_PR_245"
        )
        self.assertEqual(
            route["post245_generated_family_final_gate"], "RH_EQUIVALENT_PR_245"
        )
        self.assertEqual(route["post245_eventual_aperture_bound"], "OPEN_RH_EQUIVALENT")
        self.assertEqual(route["post245_sub_rh_gate_remaining_on_route"], "NONE")
        self.assertEqual(
            route["next_research_target"], "CANONICAL_PRIME_REMAINDER_DOMINANCE"
        )
        self.assertEqual(
            route["required_new_information"],
            "RH_STRENGTH_WEIGHTED_CHEBYSHEV_REMAINDER_INFORMATION",
        )
        for key in (
            "post245_canonical_prime_remainder_normal_form",
            "post245_prime_remainder_dominance_rh_equivalence",
            "post245_generated_riesz_six_target_rh_equivalence",
        ):
            self.assertEqual(route[key], "CANDIDATE_POST245_ARITHMETIC_CRITERION_PR")
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_control_note_supersedes_strictly_weaker_claim(self):
        note = self.state["control_note"]
        for token in (
            "PR #245",
            "766579346ec86b25d63fb61f8e0b46752a028f6c",
            "ad0347ef07e2c7717f88bd9d8bf7555be75ad88e",
            "0466006ec23b3f24f6ea113b303014ae42a680dd",
            "NoArbitrarilyLargeWholeCellRetainedFamily <-> Mathlib.RiemannHypothesis",
            "is superseded",
            "no sub-RH gate remains on this route",
            "CANONICAL_PRIME_REMAINDER_DOMINANCE",
            "RH remains OPEN",
        ):
            self.assertIn(token, note)

    def test_post245_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_245_ARITHMETIC_CRITERION_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_245_DELTA.md",
            RHRC / "DEAD_ROUTES_POST_245_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)
            self.assertIn("RH remains OPEN", text)

    def test_arithmetic_modules_expose_exact_declarations(self):
        remainder = (ROOT / "Zeta23" / "CCM" / "CanonicalPrimeRemainder.lean").read_text(
            encoding="utf-8"
        )
        for name in (
            "canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum",
            "canonicalPolePrimeDiscrepancy_eq_neg_tail_sub_remainder",
            "canonicalPolePrimeDiscrepancyEnergy_eq_neg_tail_sub_remainder",
            "canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget",
            "canonicalSourceChannelEnergy_nonneg_iff_budget_le",
        ):
            self.assertIn(f"theorem {name}", remainder)
            self.assertIn(f"#print axioms Zeta23.CCM.{name}", remainder)
        self.assertNotIn("RiemannHypothesis", remainder)

        criterion = (
            ROOT / "Zeta23" / "ExceptionalZero" / "CanonicalArithmeticCriterion.lean"
        ).read_text(encoding="utf-8")
        for name in (
            "canonicalFiniteWeilPositivity_iff_riemannHypothesis",
            "canonicalRieszSixPositivity_iff_riemannHypothesis",
            "generatedRetainedRieszSixEventuallyNonnegative_iff_riemannHypothesis",
            "canonicalPrimeRemainderDominance_iff_riemannHypothesis",
            "generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis",
            "exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero",
        ):
            self.assertIn(f"theorem {name}", criterion)
            self.assertIn(f"#print axioms Zeta23.ExceptionalZero.{name}", criterion)
        for forbidden in ("sorry", "\naxiom ", "native_decide"):
            self.assertNotIn(forbidden, remainder)
            self.assertNotIn(forbidden, criterion)

        ccm_root = (ROOT / "Zeta23" / "CCM.lean").read_text(encoding="utf-8")
        ez_root = (ROOT / "Zeta23" / "ExceptionalZero.lean").read_text(encoding="utf-8")
        self.assertIn("import Zeta23.CCM.CanonicalPrimeRemainder", ccm_root)
        self.assertIn(
            "import Zeta23.ExceptionalZero.CanonicalArithmeticCriterion", ez_root
        )

    def test_arithmetic_firewall_passes_and_is_wired_into_ci(self):
        self.assertEqual(arithmetic_firewall_lint.lint(), [])
        workflow = (ROOT / ".github" / "workflows" / "rhrc.yml").read_text(
            encoding="utf-8"
        )
        self.assertIn("research/RHRC/tools/arithmetic_firewall_lint.py", workflow)
        self.assertIn("research/RHRC/tools/axiom_audit.py", workflow)
        self.assertIn("assert p['theorem_anchor']['pr'] == 245", workflow)


if __name__ == "__main__":
    unittest.main()
