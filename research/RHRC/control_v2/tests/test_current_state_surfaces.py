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

    def test_machine_state_is_merged_post242(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 242)
        self.assertEqual(
            self.state["merged_theorem_anchor"]["validated_head"],
            "d4ccbd67223278e95e3aef728f0f42891aff6fd7",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["merge_commit"],
            "d2ba055243cdf0765a58ce2068a98744b7ae9432",
        )
        self.assertEqual(
            self.state["merged_theorem_anchor"]["tree"],
            "0f4f82b5fc43024c52c75ec8940108830ceaf7c1",
        )
        self.assertEqual(self.state["latest_validated_theorem_delta"]["pr"], 242)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        route = self.state["active_research_route"]
        self.assertEqual(
            route["next_research_target"],
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
        )
        self.assertEqual(
            route["required_new_information"],
            "PRESERVE_ARBITRARILY_LARGE_APERTURE_AND_WHOLE_CELL_BADNESS_THROUGH_BIREGULAR_SELECTION",
        )
        self.assertEqual(route["terminal_mathlib_rh_seam"], "PROVED_PR_242")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_every_living_surface_frontloads_machine_state(self):
        required = (
            "PR #242",
            "d4ccbd67223278e95e3aef728f0f42891aff6fd7",
            "d2ba055243cdf0765a58ce2068a98744b7ae9432",
            "0f4f82b5fc43024c52c75ec8940108830ceaf7c1",
            "MERGED_VIA_PR_242",
            "CONDITIONAL_TERMINAL_RH_SEAM",
            "riemannHypothesis_of_noRegularFirstBadCertificates",
            "NoRegularFirstBadCertificates -> RiemannHypothesis",
            "11/11 ATTACHED WORKFLOWS GREEN",
            "terminal Mathlib RH seam = PROVED / PR #242",
            "STRONG SUFFICIENT ENDPOINT / NOT PRIMARY RESEARCH TARGET",
            "generic safe negative-shift transfer reality = PROVED / PR #239",
            "positive-center-deficit transfer escape = PROVED / PR #240",
            "D > 0",
            "OPEN / NOT PROVED",
            "odd-selected exact cross-parity negative-root endpoint = PROVED",
            "simultaneous odd-bad exclusion = OPEN",
            "PR #223",
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED",
            "PR #117",
            "E4A4-SCHUR-FB-05",
            "OBS-059I",
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
            "PRESERVE_ARBITRARILY_LARGE_APERTURE_AND_WHOLE_CELL_BADNESS_THROUGH_BIREGULAR_SELECTION",
            "R003 phase = DISCOVERY",
            "confirmatory execution = NOT AUTHORIZED",
            "terminal claim = RH_OPEN",
        )
        forbidden = (
            "merged theorem authority = PR #237",
            "next research target = CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
            "terminal Mathlib RH seam = OPEN",
            "generic safe-shift transfer reality = OPEN / NEXT THEOREMIZATION",
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
