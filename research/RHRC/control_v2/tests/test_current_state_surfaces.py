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

    def test_machine_state_is_merged_post233(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 233)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 233)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(
            route["next_research_target"],
            "RETAINED_SOURCE_DISK_SECULAR_INTERSECTION",
        )
        self.assertEqual(
            route["required_new_information"],
            "M4_FREE_RETAINED_DISK_HALFPLANE_COMPATIBILITY",
        )
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #233",
            "565428e066004e559490fbe1d21d46ef14494de3",
            "9dfee4f50d5b57c92327da564ddf2f6159223fe1",
            "5713b8d8088864cb126aae48a3a5a5ac8304807a",
            "MERGED_VIA_PR_233",
            "RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK",
            "evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad",
            "evenShiftedCrossParitySourceGramDiskEnergy_of_even_of_not_oddBad",
            "evenShiftedCrossParitySourceGramDisk_of_even_of_not_oddBad",
            "norm_sq_parityCanonicalSourcePairing_le_mul_energy_of_not_parityBad",
            "intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq",
            "PROVED STRUCTURAL CONSEQUENCE / NOT INDEPENDENT ARITHMETIC INFORMATION",
            "retained disk emptiness = OPEN / NOT PROVED BY #233",
            "11/11 ATTACHED WORKFLOWS GREEN",
            "PR #223",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "RETAINED_SOURCE_DISK_SECULAR_INTERSECTION",
            "M4_FREE_RETAINED_DISK_HALFPLANE_COMPATIBILITY",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #231",
            "next research target = RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK",
            "required new information = GOOD_SECTOR_GRAM_CONTROL_COMPOSED_WITH_RETAINED_SOURCE_BALANCE",
            "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION",
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
