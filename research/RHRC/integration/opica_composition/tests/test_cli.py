"""Portable orchestration guards; native proof lanes remain independently required.

Only the failing source-report tests replace a lightweight source inspector.
Their heavy checkers are tripwires and never return a simulated proof success.
The positive support-receipt test executes the real authored49-test runner.
"""
from collections import Counter
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_composition import cli
from research.RHRC.integration.opica_composition.accept import ROUND4_LANES
from research.RHRC.integration.opica_composition.canonical import ContractError, canonical_bytes, load_bytes
from research.RHRC.integration.opica_composition.descendant import BASE, BASE_TREE
from research.RHRC.integration.opica_composition.provider import configuration
from research.RHRC.integration.opica_composition.testing import discover_methods

REPO = Path(__file__).resolve().parents[5]
R4 = REPO / "research/RHRC/integration/opica_round4"
SUPPORT = REPO / "research/RHRC/integration/opica_round4_support"
REQUIRED_LANES = (
    "CONTRACT", "PARENT_REGRESSION", "CURRENT_COMPATIBILITY", "COMPOSITION_FORMAL",
    "SEMANTIC_NEGATIVES", "REPLAY_CAMPAIGN", "FRAMEWORK_ADAPTERS", "PROVIDER_SELECTED",
    "GENERATED_STATE", "MATHEMATICAL_SUPPORT", "SOURCE_NUMERICS",
)


class CliOrchestrationTests(unittest.TestCase):
    def test_original_acceptance_census_has_every_numbered_method_once(self):
        original = load_bytes((R4 / "BASELINE_ACCEPTANCE_MATRIX.json").read_bytes())["tests"]
        methods = [row for row in discover_methods() if row["case"] is not None]
        self.assertEqual(len(original), 117)
        self.assertEqual(len(methods), 117)
        self.assertEqual(Counter(row["case"] for row in methods), Counter(row["id"] for row in original))
        self.assertEqual(len({row["method"] for row in methods}), 117)

    def test_all_thirteen_work_packages_remain_explicit(self):
        packages = load_bytes((R4 / "WORK_PACKAGES.json").read_bytes())["packages"]
        self.assertEqual([row["id"] for row in packages], ["R4-" + str(i).zfill(2) for i in range(13)])
        self.assertTrue(all(row.get("name") and row.get("implementation") and row.get("acceptance_authority")
                            for row in packages))

    def test_every_lane_uses_its_own_source_identity(self):
        profile = load_bytes(cli.PROFILE.read_bytes())
        self.assertEqual(set(ROUND4_LANES), set(REQUIRED_LANES))
        self.assertEqual(len(ROUND4_LANES), 11)
        self.assertEqual(profile["required_input_lanes"], list(ROUND4_LANES))
        requested = {"requested_commit": "a" * 40, "requested_tree": "b" * 40}
        provider = configuration()
        for lane in REQUIRED_LANES:
            with self.subTest(lane=lane):
                row = cli.lane_expected(lane, requested)
                self.assertEqual(row["id"], lane)
                if lane == "PARENT_REGRESSION":
                    self.assertEqual(row, {"id": lane, "scope": "FROZEN_BASELINE",
                                           "checked": {"commit": BASE, "tree": BASE_TREE}})
                elif lane == "PROVIDER_SELECTED":
                    self.assertEqual(row, {"id": lane, "scope": "SELECTED_PROVIDER", "checked": {
                        "repository": provider["repository"], "commit": provider["commit"],
                        "toolchain": provider["toolchain"]}})
                else:
                    self.assertEqual(row, {"id": lane, "scope": "CURRENT_HOST", "checked": {
                        "commit": requested["requested_commit"], "tree": requested["requested_tree"]}})
        with self.assertRaises(ContractError):
            cli.lane_expected("ACCEPTANCE", requested)

    def test_source_report_mismatch_stops_before_any_heavy_checker(self):
        current = {"schema": "SOURCE_IDENTITY_FIXTURE_ONLY_NOT_PROOF", "commit": "c" * 40}
        changed = {**current, "commit": "d" * 40}
        for source, after in ((current, changed), (changed, changed)):
            with self.subTest(source=source, after=after), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                files = {}
                for name, row in (("results.json", {}), ("source.json", source), ("source-after.json", after)):
                    path = root / name
                    path.write_bytes(canonical_bytes(row))
                    files[name] = path
                with patch.object(cli, "validate_descendant", return_value=current) as inspector, \
                     patch.object(cli, "worker_from_environment", side_effect=AssertionError("native worker must not run")) as worker, \
                     patch("research.RHRC.integration.opica_composition.qualification.check_current_compatibility",
                           side_effect=AssertionError("heavy native checker must not run")) as heavy:
                    with self.assertRaisesRegex(ContractError, "Lane source differs"):
                        cli.verify_lane_raw({"id": "CURRENT_COMPATIBILITY"}, {}, files, REPO, root / "independent")
                    inspector.assert_called_once_with(REPO, require_clean=True)
                    worker.assert_not_called()
                    heavy.assert_not_called()
                    self.assertFalse((root / "independent").exists())

    def test_real_support_runner_yields_all_forty_nine_tests_in_both_modes(self):
        expected = load_bytes((SUPPORT / "EXPECTED_TEST_IDS.json").read_bytes())
        self.assertEqual(len(expected), 49)
        with tempfile.TemporaryDirectory() as tmp:
            rows = cli.support_regressions(REPO, Path(tmp))
            self.assertEqual(len(rows), 2)
            for row, optimized in zip(rows, (False, True)):
                receipt = row["receipt"]
                self.assertEqual(row["command"]["exit_code"], 0)
                self.assertEqual(receipt["test_ids"], sorted(expected))
                self.assertEqual(receipt["executed"], 49)
                self.assertIs(receipt["optimized"], optimized)

    def test_support_receipt_rejects_empty_skipped_or_wrong_mode_wrappers(self):
        # Synthetic failures test parsing only; no synthetic success is accepted.
        base = {"status": "PASS", "executed": 49, "expected": 49, "skips": 0, "errors": 0,
                "failures": 0, "expected_failures": 0, "unexpected_successes": 0, "optimized": False}
        for update in ({"executed": 0}, {"skips": 1}, {"optimized": True}):
            with self.subTest(update=update), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                def rejected_wrapper(repo, argv, output, label):
                    path = output / (label + ".log")
                    path.write_text(json.dumps({**base, **update}) + "\n", encoding="utf-8")
                    return {"log": path.name, "exit_code": 0}
                with patch.object(cli, "run_command", side_effect=rejected_wrapper):
                    with self.assertRaises(ContractError):
                        cli.support_regressions(REPO, root)


if __name__ == "__main__":
    unittest.main()
