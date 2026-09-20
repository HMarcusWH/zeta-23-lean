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
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_machine_state_is_merged_post222(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 222)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 222)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["active_research_route"]["next_research_target"], "RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION")
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #222", "c46939488ead9535a63b547c38d64938a882a9f1", "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5", "fd151afbcae3155cc4d32a75da08b6f7e0119099",
            "e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543", "48d8752950c28e0d3bbd385646e71075abef9e76",
            "MERGED_VIA_PR_222",
            "BIREGULAR_FIRST_BAD_ZERO_SHIFT_NORMAL_FORM",
            "PR #223", "5e01e55544be937b0f0e389f1f279e13a89f2b3a",
            "8c57ce445a2223dab4a3e8aedbd3db67171e96b0",
            "3588cd964a3346b20e359b41c02eb8caaed3221a",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE",
            "PR #117", "E4A4-SCHUR-FB-05", "OBS-059I", "RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION",
            "R003 phase = DISCOVERY", "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = ("PR #184", "PR #201", "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION", "full-composite parity mechanism = current")
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                block = current_block(path)
                for token in required: self.assertIn(token, block)
                for token in forbidden: self.assertNotIn(token, block)

    def test_control_semantics_remain_frozen(self):
        action_registry = json.loads((RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8"))
        self.assertEqual(action_registry["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertEqual([b["id"] for b in action_registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]["first_breaks"]], ["E4A4-SCHUR-FB-05"])

    def test_historical_fixtures_are_not_rewritten_by_current_surface_rule(self):
        fixture = json.loads((RHRC / "routes" / "R003_ccm_bridge" / "fixtures" / "post214_fb05_kernel_dual_geometry_v1.json").read_text(encoding="utf-8"))
        self.assertEqual(fixture["theorem_authority_pr"], 213)
        self.assertEqual(fixture["latest_research_authority_pr"], 205)

if __name__ == "__main__":
    unittest.main()
