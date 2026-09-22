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

    def test_machine_state_is_merged_post243(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 243)
        self.assertEqual(
            self.state["merged_theorem_anchor"]["validated_head"],
            "7b9cc503c50478000ce4ac53c61d4a96ed2d4050",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["merge_commit"],
            "be58e98a843ceeceb93a7729d95a3fb6bb0b60df",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["tree"],
            "abf8ff5b429adea4adaaec28e182dc30495b1ba8",
        )
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 243)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(route["next_research_target"], "GENERATED_FAMILY_FINAL_GATE")
        self.assertEqual(
            route["required_new_information"],
            "EVENTUAL_CANONICAL_UPPER_BOUND_ON_WHOLE_CELL_RETAINED_APERTURE",
        )
        self.assertEqual(route["post243_whole_cell_provenance"], "PROVED_PR_243")
        self.assertEqual(
            route["post243_arbitrarily_large_retained_family"], "PROVED_PR_243"
        )
        self.assertEqual(
            route["post243_generated_family_final_gate"],
            "OPEN_EVENTUAL_APERTURE_BOUND",
        )
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #243",
            "7b9cc503c50478000ce4ac53c61d4a96ed2d4050",
            "be58e98a843ceeceb93a7729d95a3fb6bb0b60df",
            "abf8ff5b429adea4adaaec28e182dc30495b1ba8",
            "MERGED_VIA_PR_243",
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
            "exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero",
            "off-line zero -> arbitrarily-large whole-cell bi-regular retained negative-energy certificates",
            "11/11 ATTACHED WORKFLOWS GREEN",
            "terminal Mathlib RH seam = PROVED / PR #242",
            "whole-cell provenance preservation = PROVED / PR #243",
            "arbitrary-large retained aperture family = PROVED / PR #243",
            "NoArbitrarilyLargeWholeCellRetainedFamily",
            "eventual generated-family aperture bound = OPEN",
            "contact theory = FALLBACK ONLY",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "GENERATED_FAMILY_FINAL_GATE",
            "EVENTUAL_CANONICAL_UPPER_BOUND_ON_WHOLE_CELL_RETAINED_APERTURE",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #237",
            "merged theorem authority = PR #242",
            "next research target = CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
            "next research target = OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
            "terminal Mathlib RH seam = OPEN",
            "NoRegularFirstBadCertificates = PROVED",
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
