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

    def test_machine_state_is_merged_post237(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 237)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 237)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(
            route["next_research_target"],
            "CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
        )
        self.assertEqual(
            route["required_new_information"],
            "CONJUGATION_COMPATIBLE_SHIFTED_RESOLVENT_AND_REAL_TRANSFER_COEFFICIENTS",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #237",
            "8b7ba6b25c6f8977ff27890196e5b43ca3459b78",
            "267d417216f1731c6860b7553ba87397843fe258",
            "28b22a2a4c96f32874fc09cd1e73f2fb09807e9d",
            "MERGED_VIA_PR_237",
            "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
            "retainedRealCompletedSourceCorridor_of_even_of_not_oddBad",
            "retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq",
            "13/13 ATTACHED WORKFLOWS GREEN",
            "PR #223",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED",
            "retained Gamma is real",
            "f = q*Gamma",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
            "CONJUGATION_COMPATIBLE_SHIFTED_RESOLVENT_AND_REAL_TRANSFER_COEFFICIENTS",
            "CANONICAL_CUBIC_SHELL_NORMALIZATION",
            "672 attempted / 0 shifted states",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #236",
            "next research target = RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
            "required new information = REALITY_OF_RETAINED_M4_AND_SCALAR_COMPOSITION",
            "next research target = RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
            "required new information = CONJUGATION_COMPATIBLE_CANONICAL_NORMALIZATION",
            "full-composite parity mechanism = current",
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
