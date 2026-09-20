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

    def test_machine_state_is_merged_post224(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 224)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 224)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["active_research_route"]["next_research_target"], "CROSS_PARITY_PREDECESSOR_CORRECTION_PROPORTIONALITY")
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #224", "83de9193dffba12097d950d2291348db76d047f7",
            "0f8f5ad468b337622942f76725c9d76db74e27e4",
            "aaedc131612393a1198837b3e5288e48538a94ae",
            "MERGED_VIA_PR_224", "ODD_CUBIC_PROJECTION_CLOSED_FORM",
            "cubicProjectionResidual_eq_oddCubicProjectionSlope_smul",
            "stronger predecessor correction proportionality = OPEN / NOT PROVED BY #224",
            "PR #223", "5e01e55544be937b0f0e389f1f279e13a89f2b3a",
            "8c57ce445a2223dab4a3e8aedbd3db67171e96b0",
            "3588cd964a3346b20e359b41c02eb8caaed3221a",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE",
            "PR #117", "E4A4-SCHUR-FB-05", "OBS-059I",
            "CROSS_PARITY_PREDECESSOR_CORRECTION_PROPORTIONALITY",
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
