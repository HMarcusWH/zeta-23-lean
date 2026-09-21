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

    def test_machine_state_is_merged_post235(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 235)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 235)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
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

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #235",
            "d7ae288e874b2cf3462a8e00c35c7b713607a192",
            "0c347a99a02157798109ffb5a4718e201e6fa083",
            "ba6d8e6f5a714742353678e36cbc90d869b31798",
            "MERGED_VIA_PR_235",
            "RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
            "oddBad_of_even_of_sourceKernelDeficit_pos_of_sharpExcess_pos",
            "retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad",
            "D > 0 and E > 0 forces odd badness",
            "PR #223",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
            "CONJUGATION_COMPATIBLE_CANONICAL_NORMALIZATION",
            "CANONICAL_CUBIC_SHELL_NORMALIZATION",
            "672 attempted / 0 shifted states",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #234",
            "next research target = RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
            "required new information = CANONICAL_SOURCE_DEFICIT_AND_EXCESS_SIGN_CONTROL",
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
