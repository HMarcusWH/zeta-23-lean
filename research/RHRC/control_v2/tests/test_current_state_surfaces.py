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

    def test_machine_state_is_post222_delta(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 221)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 222)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 215)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["active_research_route"]["next_research_target"], "RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION")
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #221", "a26f3a9ef2d40fc0522a20c5d184fc0a8968325b", "ab5f29ba01899362ab03fdb509a04c4d5afc2744", "4fda17717de7b7644c267e98b5c61b7dc3e36547",
            "PR #222", "e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543", "48d8752950c28e0d3bbd385646e71075abef9e76",
            "GREEN_PR_THEOREM_DELTA_PENDING_MERGE",
            "BIREGULAR_FIRST_BAD_ZERO_SHIFT_NORMAL_FORM",
            "PR #215", "5469fbac77c82ccfc9dad0da4c7ce2b0ba67c47a",
            "191b1b648448c92010286dae54df8502df1f55ce",
            "4e6111c974ae8abbf59a5063d4b1ea760fa39ffd",
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
