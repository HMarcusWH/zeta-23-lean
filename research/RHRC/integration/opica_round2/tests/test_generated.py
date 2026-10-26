"""Adversarial source-freeze and pre-regeneration CI boundary fixtures."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[3]
TEMP_ROOT = REPO.parent / "opica-round2-generated-test-temp"
sys.path.insert(0, str(HERE))
import run_checks

spec = importlib.util.spec_from_file_location("_opica2_suite_under_test", REPO / "research/RHRC/tools/run_suite.py")
suite = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suite)


class GeneratedBeforeWriteTests(unittest.TestCase):
    def setUp(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(dir=TEMP_ROOT)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.config = self.root / "config"
        self.config.mkdir()
        (self.repo / "product.json").write_text("committed stale bytes", encoding="utf-8")
        (self.config / "BUILD_MANIFEST.json").write_text(json.dumps({"generated": [{"path": "product.json"}]}))

    def execute(self, command):
        with patch.object(run_checks, "HERE", self.config), patch.object(run_checks.contract, "git", return_value="a" * 40):
            with patch.object(run_checks.compiler, "run_command", side_effect=command) as called:
                result = run_checks.execute_generated(self.repo, self.root / "evidence", 30)
        return result, called

    def test_stale_committed_bytes_fail_before_any_rewrite(self):
        calls = []
        def stale(repo, argv, output, name, tree, **kwargs):
            calls.append(argv)
            self.assertEqual(argv[-1], "--check")
            self.assertNotIn("--write", argv)
            return {"returncode": 1}
        with self.assertRaises(ValueError):
            self.execute(stale)
        self.assertEqual(len(calls), 1)
        self.assertEqual((self.repo / "product.json").read_text(), "committed stale bytes")

    def test_check_command_that_rewrites_is_rejected(self):
        def mutation(repo, argv, output, name, tree, **kwargs):
            (repo / "product.json").write_text("laundered bytes")
            return {"returncode": 0}
        with self.assertRaises(ValueError):
            self.execute(mutation)

    def test_missing_product_is_rejected_before_command(self):
        (self.repo / "product.json").unlink()
        with patch.object(run_checks, "HERE", self.config), patch.object(run_checks.compiler, "run_command") as command:
            with self.assertRaises(ValueError):
                run_checks.execute_generated(self.repo, self.root / "evidence", 30)
            command.assert_not_called()

    def test_duplicate_product_is_rejected(self):
        (self.config / "BUILD_MANIFEST.json").write_text(json.dumps({"generated": [{"path": "product.json"}] * 2}))
        with patch.object(run_checks, "HERE", self.config), patch.object(run_checks.compiler, "run_command") as command:
            with self.assertRaises(ValueError):
                run_checks.execute_generated(self.repo, self.root / "evidence", 30)
            command.assert_not_called()


class SourceFreezeTests(unittest.TestCase):
    def setUp(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(dir=TEMP_ROOT)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        def git(*args):
            subprocess.run(["git", "-C", str(self.repo), *args], check=True, capture_output=True)
        git("init")
        git("config", "user.name", "OPICA test fixture")
        git("config", "user.email", "fixture@example.invalid")
        git("config", "core.autocrlf", "false")
        (self.repo / "Source.lean").write_text("theorem source_fixture : True := True.intro\n")
        (self.repo / ".gitignore").write_text("ignored.lean\n.lake/\n")
        git("add", ".")
        git("commit", "-m", "Fixture source")

    def test_capture_is_external_immutable_and_reverified(self):
        target = self.root / "source-freeze.json"
        suite.freeze_source(target, repo=self.repo)
        suite.verify_source_freeze(target, repo=self.repo)
        with self.assertRaises(FileExistsError):
            suite.freeze_source(target, repo=self.repo)
        self.assertFalse(json.loads(target.read_bytes())["full_release_accepted"])
        with self.assertRaises(ValueError):
            suite.freeze_source(self.repo / "cannot-write.json", repo=self.repo)
        self.assertFalse((self.repo / "cannot-write.json").exists())

    def test_source_change_after_capture_fails(self):
        target = self.root / "source-freeze.json"
        suite.freeze_source(target, repo=self.repo)
        (self.repo / "Source.lean").write_text("changed source\n")
        with self.assertRaises(ValueError):
            suite.verify_source_freeze(target, repo=self.repo)

    def test_ignored_source_provider_is_not_a_clean_checkout(self):
        (self.repo / "ignored.lean").write_text("axiom ignoredProvider : False\n")
        with self.assertRaises(ValueError):
            suite.source_snapshot(self.repo)


class WorkflowBoundaryTests(unittest.TestCase):
    def test_historical_suite_needs_explicit_projection(self):
        with self.assertRaises(ValueError):
            suite.run_round2_suite(argparse.Namespace(ancestor_projection=None, skip_derived_state=False))

    def test_historical_predicates_and_tests_use_authenticated_projection(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            projection = Path(tmp).resolve()
            with patch.object(suite, "run") as commands:
                suite.run_round2_suite(argparse.Namespace(ancestor_projection=projection, skip_derived_state=True))
            calls = [call.args[0] for call in commands.call_args_list]
            dispatches = [argv for argv in calls if "--ancestor-projection" in argv]
            self.assertEqual(len(dispatches), 2)
            self.assertTrue(all(argv[-1] == str(projection) for argv in dispatches))
            self.assertTrue(any(str(projection / "research/RHRC/tools/run_suite.py") in argv for argv in calls))
            self.assertTrue(any(str(projection / "research/RHRC/integration/opica_followup/tests") in argv for argv in calls))

    def test_cold_and_generated_workflow_boundaries_are_explicit(self):
        workflow = (REPO / ".github/workflows/rhrc_opica_round2.yml").read_text(encoding="utf-8")
        self.assertLess(workflow.index("test ! -e .lake/build"), workflow.index("--build-mode cold"))
        self.assertLess(workflow.index('run_checks.py" generated'), workflow.index("materialize_derived_state.py --write"))
        self.assertLess(workflow.index("git worktree add --detach"), workflow.index("materialize_derived_state.py --write"))
        self.assertNotIn("--skip-derived-state", workflow)
        self.assertIn("--snapshot-mode in-workflow", workflow)
        self.assertNotIn("--snapshot-mode post-run", workflow)
        self.assertIn("--require-hashes --only-binary=:all:", workflow)
        self.assertIn("--verify-source-freeze", workflow)

    def test_exact81_products_and_required_job_inventory(self):
        manifest = json.loads((HERE / "BUILD_MANIFEST.json").read_bytes())
        products = [row["path"] for row in manifest["generated"]]
        self.assertEqual(len(products), 81)
        self.assertEqual(len(set(products)), 81)
        expected = {"contract", "controls", "ancestry", "aggregate", "generated", "harvest", "acceptance"}
        expected.update("formal(" + lane + ")" for lane in ("causal", "filtered", "gram", "structural"))
        observed = {row["name"] for row in suite.WORKFLOW_CLASSIFICATIONS["required_jobs"]}
        self.assertEqual(observed, expected)


if __name__ == "__main__":
    unittest.main()
