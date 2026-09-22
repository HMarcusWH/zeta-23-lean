import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

LIVING_SURFACES = (
    ROOT / "README.md", ROOT / "AUDIT.md", ROOT / "FORK_NOTES.md",
    RHRC / "CURRENT_RESEARCH_PLAN.md", RHRC / "DOCUMENTATION_AUTHORITY.md",
    RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md", RHRC / "OBSTRUCTION_LEDGER.md",
    RHRC / "DEAD_ROUTES.md", RHRC / "README.md", RHRC / "RESEARCH_LEADS.md",
    RHRC / "VALIDATION_PROTOCOL.md", RHRC / "control_v2" / "README.md",
    RHRC / "routes" / "R003_ccm_bridge" / "README.md",
    RHRC / "countermodels" / "README.md",
)
BEGIN = "<!-- RHRC_CURRENT_STATE_BEGIN -->"
END = "<!-- RHRC_CURRENT_STATE_END -->"


def current_block(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise AssertionError(f"{path}: expected exactly one current-state marker pair")
    prefix, rest = text.split(BEGIN, 1)
    block, _suffix = rest.split(END, 1)
    if len(prefix.splitlines()) > 45:
        raise AssertionError(f"{path}: current-state block is not front-loaded")
    return block


class CurrentStateSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_machine_state_is_merged_post245(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 245)
        self.assertEqual(
            self.state["merged_theorem_anchor"]["validated_head"],
            "766579346ec86b25d63fb61f8e0b46752a028f6c",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["merge_commit"],
            "ad0347ef07e2c7717f88bd9d8bf7555be75ad88e",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["tree"],
            "0466006ec23b3f24f6ea113b303014ae42a680dd",
        )
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 245)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(
            route["next_research_target"], "CANONICAL_PRIME_REMAINDER_DOMINANCE"
        )
        self.assertEqual(
            route["required_new_information"],
            "RH_STRENGTH_WEIGHTED_CHEBYSHEV_REMAINDER_INFORMATION",
        )
        self.assertEqual(route["terminal_mathlib_rh_seam"], "PROVED_PR_242")
        self.assertEqual(
            route["post245_no_regular_first_bad_certificates"], "RH_EQUIVALENT_PR_245"
        )
        self.assertEqual(
            route["post245_generated_family_final_gate"], "RH_EQUIVALENT_PR_245"
        )
        self.assertEqual(route["post245_sub_rh_gate_remaining_on_route"], "NONE")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #245",
            "766579346ec86b25d63fb61f8e0b46752a028f6c",
            "ad0347ef07e2c7717f88bd9d8bf7555be75ad88e",
            "0466006ec23b3f24f6ea113b303014ae42a680dd",
            "MERGED_VIA_PR_245",
            "TERMINAL_GATE_RH_EQUIVALENCE",
            "noArbitrarilyLargeWholeCellRetainedFamily_iff_riemannHypothesis",
            "noRegularFirstBadCertificates_iff_riemannHypothesis",
            "NoArbitrarilyLargeWholeCellRetainedFamily <-> RiemannHypothesis",
            "NoRegularFirstBadCertificates <-> RiemannHypothesis",
            "11/11 ATTACHED WORKFLOWS GREEN",
            "terminal Mathlib RH seam = PROVED / PR #242",
            "whole-cell provenance preservation = PROVED / PR #243",
            "arbitrary-large retained aperture family = PROVED / PR #243",
            "off-line zero -> arbitrarily-large whole-cell bi-regular retained negative-energy certificates",
            "eventual generated-family aperture bound = OPEN / RH-EQUIVALENT",
            "sub-RH gate remaining on this route = NONE",
            "contact theory = FALLBACK ONLY",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "next research target = CANONICAL_PRIME_REMAINDER_DOMINANCE",
            "required new information = RH_STRENGTH_WEIGHTED_CHEBYSHEV_REMAINDER_INFORMATION",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #242",
            "merged theorem authority = PR #243",
            "next research target = GENERATED_FAMILY_FINAL_GATE",
            "terminal Mathlib RH seam = OPEN",
            "NoRegularFirstBadCertificates = PROVED",
            "NoArbitrarilyLargeWholeCellRetainedFamily = PROVED",
            "strictly weaker than NoRegularFirstBadCertificates",
            "RH = PROVED",
        )
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                block = current_block(path)
                for token in required:
                    self.assertIn(token, block)
                for token in forbidden:
                    self.assertNotIn(token, block)

    def test_control_semantics_remain_frozen(self):
        action_registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            action_registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
        self.assertEqual(
            [
                b["id"]
                for b in action_registry["actions"][
                    "E4_A4_REGULAR_SCHUR_ENERGY_SIGN"
                ]["first_breaks"]
            ],
            ["E4A4-SCHUR-FB-05"],
        )


if __name__ == "__main__":
    unittest.main()
