import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent
sys.path.insert(0, str(RHRC / "control_v2"))

from render_current_state import (
    BEGIN,
    END,
    LIVING_SURFACES,
    render_current_state_block,
)


def current_block(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise AssertionError(f"{path}: expected exactly one current-state marker pair")
    prefix, rest = text.split(BEGIN, 1)
    block, _suffix = rest.split(END, 1)
    if len(prefix.splitlines()) > 45:
        raise AssertionError(f"{path}: current-state block is not front-loaded")
    return block.strip("\n")


class CurrentStateSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_machine_state_contracts(self):
        theorem = self.state["merged_theorem_anchor"]
        self.assertGreaterEqual(theorem["pr"], 278)
        self.assertEqual(theorem["status"], "MERGED_GREEN_THEOREM_STATE")
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")
        self.assertFalse(self.state["candidate_branch"]["terminal_claim_change"])
        route = self.state["active_research_route"]
        self.assertEqual(
            route["current_obstruction"],
            "OBS-060_GROUND_SPECTRUM_FIRST_CROSSING_BARRIER",
        )
        self.assertEqual(route["current_next_research_target"], "PRODUCTION_ARITHMETIC_SATURATION_FRONTIER")
        self.assertEqual(route["post278_fixedN_ground_continuity"], "PROVED_MERGED_PR_278")
        self.assertEqual(route["post278_sameN_zero_contact"], "PROVED_MERGED_PR_278")
        self.assertEqual(route["post276_small_aperture_ground_spectrum"], "PROVED_PR_276")

    def test_every_living_surface_exactly_matches_machine_renderer(self):
        expected = render_current_state_block(self.state)
        for path in LIVING_SURFACES:
            with self.subTest(path=path):
                self.assertEqual(current_block(path), expected)

    def test_renderer_preserves_claim_firewall(self):
        block = render_current_state_block(self.state)
        self.assertIn("RH = OPEN", block)
        self.assertIn(
            "RH-sufficient terminal formulations are not counted as independent sub-RH progress",
            block,
        )
        self.assertIn(
            f"current candidate PR = #{self.state['candidate_branch']['pr']} / "
            f"{self.state['candidate_branch']['status']}",
            block,
        )
        self.assertNotIn("RH = PROVED", block)

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
