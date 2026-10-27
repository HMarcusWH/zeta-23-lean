"""Adversarial source-freeze and pre-regeneration CI boundary fixtures."""
from __future__ import annotations

import argparse
import importlib.util
import hashlib
import io
import json
import runpy
import shlex
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

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
        with patch.object(run_checks, "HERE", self.config), patch.object(run_checks.contract, "git", return_value="a" * 40), \
                patch.object(run_checks, "_generated_windows_transport_required", return_value=False):
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


class WindowsGeneratedTransportTests(unittest.TestCase):
    """Synthetic transport/router fixtures; no frozen CLI, real Git or Lean runs."""
    def setUp(self):
        self.writers = []

    def tearDown(self):
        for handle in self.writers:
            handle.close()

    @staticmethod
    def source_pin(repo, relative):
        return {"path": relative, "frozen_tree": run_checks.contract.FROZEN_TREE,
                "mode": "100644", "git_blob": "0" * 40, "bytes": 0, "sha256": "0" * 64}

    @staticmethod
    def synthetic_caller(path, name="run_lean"):
        namespace = {}
        exec(compile("def " + name + "(factory, **kwargs):\n    return factory(**kwargs)\n", str(path), "exec"), namespace)
        return namespace[name]

    @staticmethod
    def no_event(*args, **kwargs):
        pass

    def text_factory(self, *args, **kwargs):
        self.last_kwargs = kwargs
        raw = io.BytesIO()
        # Deliberately emulate default Windows translation on every test OS.
        handle = io.TextIOWrapper(raw, encoding=kwargs.get("encoding", "utf-8"),
                                  newline=kwargs.get("newline", "\r\n"))
        self.writers.append(handle)
        return handle

    @staticmethod
    def payload(handle):
        handle.write("source-id\tZeta23.Native\tname\tTHEOREM\n")
        handle.flush()
        return handle.buffer.getvalue()

    def test_scoped_writer_repairs_crlf_kind_transport_without_changing_other_payload_bytes(self):
        caller = self.synthetic_caller(REPO / run_checks._GENERATED_CANDIDATE)
        options = dict(mode="w", suffix=".tsv", encoding="utf-8", delete=False)
        before = self.payload(caller(self.text_factory, **options))
        factory, count = run_checks._generated_make_tsv_factory(REPO, factory=self.text_factory,
            pin=self.source_pin, emit=self.no_event)
        after = self.payload(caller(factory, **options))
        self.assertEqual(before.split(b"\n")[0].split(b"\t")[-1], b"THEOREM\r")
        self.assertEqual(after.split(b"\n")[0].split(b"\t")[-1], b"THEOREM")
        self.assertEqual(before.replace(b"\r\n", b"\n"), after)
        self.assertEqual(self.last_kwargs["newline"], "\n")
        self.assertEqual(count, [1])

    def test_other_callers_suffixes_modes_encodings_and_explicit_newlines_are_unchanged(self):
        records = []
        def original(*args, **kwargs):
            records.append((args, kwargs))
            return object()
        factory, count = run_checks._generated_make_tsv_factory(REPO, factory=original,
            pin=self.source_pin, emit=self.no_event)
        default = dict(mode="w", suffix=".tsv", encoding="utf-8", delete=False)
        cases = [(HERE / "foreign.py", "run_lean", default),
                 (REPO / run_checks._GENERATED_CANDIDATE, "foreign_function", default),
                 (REPO / run_checks._GENERATED_CANDIDATE, "run_lean", {**default, "suffix": ".lean"}),
                 (REPO / run_checks._GENERATED_CANDIDATE, "run_lean", {**default, "encoding": "ascii"}),
                 (REPO / run_checks._GENERATED_CANDIDATE, "run_lean", {**default, "mode": "w+b"}),
                 (REPO / run_checks._GENERATED_CANDIDATE, "run_lean", {**default, "newline": "\r\n"})]
        for source, function, options in cases:
            self.synthetic_caller(source, function)(factory, **options)
            self.assertEqual(records[-1][1], options)
        self.assertEqual(count, [0])

    def test_router_changes_only_exact_candidate_child_and_preserves_all_io_arguments(self):
        records = []
        def original(command, *args, **kwargs):
            records.append((command, args, kwargs))
            return "original-result"
        report = REPO.parent / "not-created-transport.jsonl"
        routed, count = run_checks._generated_make_materialize_router(REPO, report, "a" * 64, "b" * 32,
            runner=original, pin=self.source_pin, emit=self.no_event)
        command = [sys.executable, str(REPO / run_checks._GENERATED_CANDIDATE), "--check"]
        self.assertEqual(routed(command, cwd=REPO, check=True, stdout=subprocess.PIPE), "original-result")
        actual, args, kwargs = records[0]
        self.assertEqual(actual, run_checks._generated_worker_argv(REPO, report, "a" * 64, "b" * 32, "candidate", "check"))
        self.assertEqual(kwargs, dict(cwd=REPO, check=True, stdout=subprocess.PIPE))
        self.assertEqual(args, ())
        unrelated = ["lake", "env", "lean", "driver.lean"]
        routed(unrelated, cwd=REPO, capture_output=True)
        self.assertIs(records[-1][0], unrelated)
        self.assertEqual(count, [1])

    def test_wrong_candidate_flags_interpreter_cwd_shell_and_second_route_are_refused(self):
        original = Mock()
        routed, count = run_checks._generated_make_materialize_router(REPO, REPO.parent / "unused.jsonl", "a" * 64, "b" * 32,
            runner=original, pin=self.source_pin, emit=self.no_event)
        command = [sys.executable, str(REPO / run_checks._GENERATED_CANDIDATE), "--check"]
        for argv, kwargs in [(command + ["--extra"], dict(cwd=REPO)),
                             ([*command[:2], "--unknown"], dict(cwd=REPO)),
                             (["wrong-python", *command[1:]], dict(cwd=REPO)),
                             (command, dict(cwd=REPO.parent)), (command, dict(cwd=REPO, shell=True))]:
            with self.subTest(argv=argv, kwargs=kwargs), self.assertRaises(ValueError):
                routed(argv, **kwargs)
        original.assert_not_called()
        routed(command, cwd=REPO)
        with self.assertRaises(ValueError):
            routed(command, cwd=REPO)
        self.assertEqual(original.call_count, 1)

    def test_frozen_cli_blob_authentication_is_readonly_and_rejects_wrong_source_identity(self):
        relative = run_checks._GENERATED_CANDIDATE
        raw = (REPO / relative).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()
        original = Mock(return_value=SimpleNamespace(returncode=0,
            stdout=("100644 blob " + blob + "\t" + relative + "\0").encode("utf-8")))
        pin = run_checks._generated_frozen_cli_pin(REPO, relative, runner=original)
        self.assertEqual(pin["git_blob"], blob)
        self.assertEqual(original.call_args.args[0], ["git", "-C", str(REPO), "ls-tree", "-r", "--full-tree", "-z",
            run_checks.contract.FROZEN_TREE, "--", relative])
        original.return_value.stdout = ("100644 blob " + "0" * 40 + "\t" + relative + "\0").encode()
        with self.assertRaises(ValueError):
            run_checks._generated_frozen_cli_pin(REPO, relative, runner=original)

    def test_original_cli_failure_restores_interpreter_state_and_all_patches(self):
        argv, path, original_run, original_factory = sys.argv, sys.path, subprocess.run, tempfile.NamedTemporaryFile
        def fail(target, run_name):
            self.assertEqual(sys.argv, [str(REPO / run_checks._GENERATED_MATERIALIZE), "--check"])
            self.assertEqual(sys.path[0], str((REPO / run_checks._GENERATED_MATERIALIZE).parent))
            raise RuntimeError("synthetic frozen failure")
        with self.assertRaises(RuntimeError):
            run_checks._generated_execute_frozen(REPO, "materialize", "check", REPO.parent / "unused.jsonl",
                "a" * 64, "b" * 32, emit=self.no_event, pin=self.source_pin, run_path=fail)
        self.assertIs(sys.argv, argv)
        self.assertIs(sys.path, path)
        self.assertIs(subprocess.run, original_run)
        self.assertIs(tempfile.NamedTemporaryFile, original_factory)

    def test_linux_command_is_exact_direct_cli_and_windows_command_is_explicit_internal_worker(self):
        output = REPO.parent / "unused-generated-output"
        with patch.object(run_checks, "_generated_windows_transport_required", return_value=False):
            argv, transport = run_checks._generated_check_command(REPO, output)
        self.assertEqual(argv, [sys.executable, "-B", "research/RHRC/tools/materialize_derived_state.py", "--check"])
        self.assertEqual(transport["mode"], "DIRECT_FROZEN_CLI_PLATFORM_DEFAULT_UNCHANGED")
        with patch.object(run_checks, "_generated_windows_transport_required", return_value=True), \
                patch.object(run_checks.contract, "digest", return_value="a" * 64):
            argv, transport = run_checks._generated_check_command(REPO, output)
        self.assertEqual(argv[:4], [sys.executable, "-B", str(REPO / run_checks._GENERATED_WORKER), run_checks._GENERATED_INTERNAL_FLAG])
        self.assertEqual(argv[-4:], ["--target", "materialize", "--mode", "check"])
        self.assertEqual(transport["normalization_scope"], run_checks._GENERATED_LF_SCOPE)
        self.assertFalse(transport["full_release_authority"])

    def test_internal_worker_is_not_a_ninth_public_check(self):
        observed = []
        class ParsedOnly(Exception):
            pass
        def parse_only(parser, *args, **kwargs):
            observed.extend(action.choices for action in parser._actions if action.dest == "check")
            raise ParsedOnly()
        with patch.object(argparse.ArgumentParser, "parse_args", autospec=True, side_effect=parse_only), \
                self.assertRaises(ParsedOnly):
            run_checks.main()
        self.assertEqual(observed, [("contract", "formal", "controls", "ancestry", "aggregate", "generated", "harvest", "acceptance")])

    def test_transport_report_requires_exact_scope_source_pins_order_and_zero_exit_completion(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            output = Path(tmp).resolve()
            transport = {"mode": "EXPLICIT_WINDOWS_FROZEN_CLI_LF_TRANSPORT", "worker_sha256": "a" * 64,
                         "run_id": "b" * 32, "report": "windows-lf-transport.jsonl"}
            report = output / transport["report"]
            events = []
            def event(name, **fields):
                return {"schema": "OPICA2_GENERATED_LF_TRANSPORT_EVENT_V1", "event": name, "repo": str(REPO),
                        "run_id": transport["run_id"], "worker_sha256": transport["worker_sha256"],
                        "normalization_scope": run_checks._GENERATED_LF_SCOPE, **fields}
            materialize, candidate = self.source_pin(REPO, run_checks._GENERATED_MATERIALIZE), self.source_pin(REPO, run_checks._GENERATED_CANDIDATE)
            candidate_argv = [sys.executable, str(REPO / run_checks._GENERATED_CANDIDATE), "--check"]
            events.append(event("WORKER_START", target="materialize", mode="check", source_pin=materialize,
                original_argv=[sys.executable, str(REPO / run_checks._GENERATED_MATERIALIZE), "--check"]))
            events.append(event("ROUTE_CANDIDATE_SUBPROCESS", target="materialize", mode="check", source_pin=candidate,
                original_argv=candidate_argv, actual_argv=run_checks._generated_worker_argv(REPO, report, "a" * 64, "b" * 32, "candidate", "check")))
            events.append(event("WORKER_START", target="candidate", mode="check", source_pin=candidate, original_argv=candidate_argv))
            events.append(event("SELECT_EXPLICIT_LF_TSV_WRITER", target="candidate", source_pin=candidate, caller_function="run_lean",
                suffix=".tsv", encoding="utf-8", original_newline_argument="OMITTED", actual_newline_argument="LF"))
            for target, pin in [("candidate", candidate), ("materialize", materialize)]:
                events.append(event("WORKER_FINISH", target=target, mode="check", source_pin=pin, selected_count=1,
                    status="PASS_TRANSPORT_ONLY_ORIGINAL_EXIT_ZERO"))
            def write(rows):
                report.write_bytes(b"".join((json.dumps(row) + "\n").encode("utf-8") for row in rows))
            write(events)
            with patch.object(run_checks, "_generated_frozen_cli_pin", side_effect=self.source_pin), \
                    patch.object(run_checks.contract, "digest", return_value="a" * 64):
                result = run_checks._generated_verify_transport(REPO, output, transport)
                self.assertEqual(result["event_count"], 6)
                for mutated in [events[:-1], [events[0], *events[2:]], list(reversed(events))]:
                    write(mutated)
                    with self.assertRaises(ValueError):
                        run_checks._generated_verify_transport(REPO, output, transport)
                for index, field, value in [(1, "mode", "write"), (3, "suffix", ".lean"), (1, "actual_argv", candidate_argv),
                                            (4, "selected_count", True), (4, "status", "ASSUMED_SUCCESS"),
                                            (2, "run_id", "c" * 32), (0, "source_pin", candidate)]:
                    mutated = json.loads(json.dumps(events))
                    mutated[index][field] = value
                    write(mutated)
                    with self.subTest(index=index, field=field), self.assertRaises(ValueError):
                        run_checks._generated_verify_transport(REPO, output, transport)




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
        (self.repo / ".gitignore").write_text("ignored.lean\nscripts/\n.lake/\n")
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

    def test_dependency_cache_is_allowed_but_same_provider_at_project_root_is_rejected(self):
        """Reproduce CI87's misplaced Mathlib script without deleting it."""
        target = self.root / "source-freeze.json"
        suite.freeze_source(target, repo=self.repo)
        package = self.repo / ".lake/packages/mathlib/scripts/bench/size/run.py"
        package.parent.mkdir(parents=True)
        package.write_text("# fixture for the separately authenticated dependency cache\n")
        suite.verify_source_freeze(target, repo=self.repo)
        misplaced = self.repo / "scripts/bench/size/run.py"
        misplaced.parent.mkdir(parents=True)
        misplaced.write_bytes(package.read_bytes())
        with self.assertRaisesRegex(ValueError, "Untracked or ignored executable source provider"):
            suite.verify_source_freeze(target, repo=self.repo)
        self.assertTrue(misplaced.is_file(), "The source guard must reject, not clean or whitelist, contamination")


class WorkflowBoundaryTests(unittest.TestCase):
    @staticmethod
    def lean_cache_inputs(workflow):
        """Read only canonical with-fields of pinned Lean action steps."""
        lines = workflow.splitlines()
        settings = []
        for index, line in enumerate(lines):
            if not line.lstrip().startswith("- uses: leanprover/lean-action@"):
                continue
            indentation = len(line) - len(line.lstrip())
            fields = {}
            in_with = False
            for child in lines[index + 1:]:
                if not child.strip():
                    continue
                child_indent = len(child) - len(child.lstrip())
                if child_indent <= indentation:
                    break
                if child_indent == indentation + 2:
                    in_with = child.strip() == "with:"
                elif in_with and child_indent == indentation + 4:
                    key, separator, value = child.strip().partition(":")
                    if separator and key in {"use-github-cache", "use-mathlib-cache"}:
                        fields[key] = value.strip()
            settings.append(fields)
        return settings

    def test_round2_disables_every_broad_cache_and_keeps_official_mathlib_cache(self):
        text = (REPO / ".github/workflows/rhrc_opica_round2.yml").read_text(encoding="utf-8")
        settings = self.lean_cache_inputs(text)
        self.assertEqual(len(settings), 6)
        for fields in settings:
            self.assertEqual(fields.get("use-github-cache"), "false")
            self.assertEqual(fields.get("use-mathlib-cache"), "true")

    def test_original_workflow_cache_default_is_preserved_only_without_round2_extension(self):
        condition = "${{ hashFiles('research/RHRC/integration/opica_round2/DESCENDANT_EXTENSION.json') == '' }}"
        count = 0
        for name in ("rhrc_opica.yml", "rhrc_opica_followup.yml"):
            text = (REPO / ".github/workflows" / name).read_text(encoding="utf-8")
            settings = self.lean_cache_inputs(text)
            self.assertTrue(settings)
            for fields in settings:
                self.assertEqual(fields.get("use-github-cache"), condition)
                self.assertEqual(fields.get("use-mathlib-cache"), "true")
            count += len(settings)
        self.assertEqual(count, 5)

    def test_source_workflow_composition_commands_parse_with_actual_cli_and_all_evidence(self):
        """Parse real workflow argv, stopping before any fake compiler evidence."""
        text = (REPO / ".github/workflows/rhrc_opica_round2.yml").read_text(encoding="utf-8")
        lines = text.splitlines()
        original_parse = argparse.ArgumentParser.parse_args
        class ParsedOnly(Exception):
            pass
        for stage in ("ancestry", "aggregate", "acceptance"):
            index = next(i for i, line in enumerate(lines) if 'run_checks.py" ' + stage in line)
            parts = []
            while True:
                line = lines[index].strip()
                continuation = line.endswith("\\")
                parts.append(line[:-1] if continuation else line)
                if not continuation:
                    break
                index += 1
            tokens = shlex.split(" ".join(parts))
            start = next(i for i, token in enumerate(tokens) if token.endswith("/run_checks.py")) + 1
            observed = []
            def parse_only(parser, *args, **kwargs):
                namespace = original_parse(parser, *args, **kwargs)
                observed.append(namespace)
                raise ParsedOnly()
            with patch.object(sys, "argv", ["run_checks.py", *tokens[start:]]), \
                    patch.object(argparse.ArgumentParser, "parse_args", autospec=True, side_effect=parse_only):
                with self.assertRaises(ParsedOnly):
                    run_checks.main()
            self.assertEqual(len(observed), 1)
            args = observed[0]
            self.assertEqual(args.check, stage)
            if stage == "ancestry":
                self.assertIsNotNone(args.ancestor_projection)
                self.assertTrue(all(getattr(args, name) is None for name in ("baseline76", "baseline100", "current76", "current100")))
            else:
                self.assertTrue(all(getattr(args, field) is not None for field in
                    ("clause_evidence", "control_evidence", "optimized_control_evidence", "ancestry_evidence")))
                self.assertTrue(args.clause_evidence.as_posix().endswith("/PAPER_CROSSWALK.json"))
                self.assertTrue(args.control_evidence.as_posix().endswith("/normal/controls/result.json"))
                self.assertTrue(args.optimized_control_evidence.as_posix().endswith("/optimized/controls/result.json"))
                self.assertTrue(args.ancestry_evidence.as_posix().endswith("/ancestry/result.json"))
            if stage == "aggregate":
                self.assertEqual(args.build_mode, "cold")
            if stage == "acceptance":
                self.assertTrue(args.formal_receipt.as_posix().endswith("/aggregate/compiler-receipt.json"))
                self.assertNotIn("composed-receipt", args.formal_receipt.as_posix())
    def test_historical_suite_needs_explicit_projection(self):
        with self.assertRaises(ValueError):
            suite.run_round2_suite(argparse.Namespace(ancestor_projection=None, skip_derived_state=False))

    def test_historical_predicates_and_tests_use_authenticated_projection(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            projection = Path(tmp).resolve()
            frozen_test = projection / "research/RHRC/graph/tests/test_post292_review_file_classes.py"
            frozen_test.parent.mkdir(parents=True)
            frozen_test.write_text("# Command fixture; never executed here\n", encoding="utf-8")
            with patch.object(suite, "run") as commands:
                suite.run_round2_suite(argparse.Namespace(ancestor_projection=projection, skip_derived_state=False))
            calls = [call.args[0] for call in commands.call_args_list]
            dispatches = [argv for argv in calls if "--ancestor-projection" in argv]
            self.assertEqual(len(dispatches), 2)
            self.assertTrue(all(argv[argv.index("--ancestor-projection") + 1] == str(projection) for argv in dispatches))
            self.assertTrue(all("--output" in argv and not Path(argv[-1]).is_relative_to(REPO) for argv in dispatches))
            self.assertTrue(any(str(projection / "research/RHRC/tools/run_suite.py") in argv for argv in calls))
            self.assertTrue(any(str(projection / "research/RHRC/integration/opica_followup/tests") in argv for argv in calls))
            graph = [call for call in commands.call_args_list if "-s" in call.args[0]
                     and Path(call.args[0][call.args[0].index("-s") + 1]).parts[-2:] == ("graph", "tests")]
            expected = {path.name for path in (suite.ROOT / "graph/tests").glob("test_*.py")}
            self.assertEqual({call.args[0][call.args[0].index("-p") + 1] for call in graph}, expected)
            for call in graph:
                argv = call.args[0]
                pattern = argv[argv.index("-p") + 1]
                if pattern == "test_post292_review_file_classes.py":
                    self.assertEqual(Path(argv[argv.index("-s") + 1]), frozen_test.parent)
                    self.assertEqual(call.kwargs["cwd"], projection)
                else:
                    self.assertEqual(Path(argv[argv.index("-s") + 1]), suite.ROOT / "graph/tests")

    def test_missing_frozen_historical_graph_test_cannot_be_silently_omitted(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp, patch.object(suite, "run"):
            with self.assertRaisesRegex(ValueError, "exact historical graph classification test"):
                suite.run_base_suite(argparse.Namespace(skip_derived_state=True),
                    include_ancestor=False, historical_projection=Path(tmp))

    def test_actual_ancestor_dispatch_arguments_pass_both_real_cli_parsers(self):
        """Exercise each real parser with the suite's exact emitted command."""
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            projection = Path(tmp).resolve()
            frozen_test = projection / "research/RHRC/graph/tests/test_post292_review_file_classes.py"
            frozen_test.parent.mkdir(parents=True)
            frozen_test.write_text("# Parser fixture; never executed here\n", encoding="utf-8")
            with patch.object(suite, "run") as commands:
                suite.run_round2_suite(argparse.Namespace(ancestor_projection=projection, skip_derived_state=False))
            dispatches = [call.args[0] for call in commands.call_args_list if "--ancestor-projection" in call.args[0]]
            original_parse = argparse.ArgumentParser.parse_args
            class ParsedOnly(Exception):
                pass
            outputs = []
            for argv in dispatches:
                index = next(i for i, item in enumerate(argv) if item.endswith("validate_contract.py"))
                parsed = []
                def parse_only(parser, *args, **kwargs):
                    namespace = original_parse(parser, *args, **kwargs)
                    parsed.append(namespace)
                    raise ParsedOnly()
                with patch.object(sys, "argv", argv[index:]), \
                        patch.object(argparse.ArgumentParser, "parse_args", autospec=True, side_effect=parse_only):
                    with self.assertRaises(ParsedOnly):
                        runpy.run_path(argv[index], run_name="__main__")
                self.assertEqual(len(parsed), 1)
                self.assertEqual(parsed[0].phase, "preflight")
                self.assertEqual(parsed[0].ancestor_projection, projection)
                self.assertIsNotNone(parsed[0].output)
                self.assertFalse(parsed[0].output.is_relative_to(REPO))
                self.assertFalse(parsed[0].output.is_relative_to(projection))
                outputs.append(parsed[0].output)
            self.assertEqual(len(set(outputs)), 2)

    def test_protected_python_only_caller_remains_diagnostic_and_authenticates_projection(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            output = Path(tmp).resolve()
            projection = output / "source"
            frozen_test = projection / "research/RHRC/graph/tests/test_post292_review_file_classes.py"
            frozen_test.parent.mkdir(parents=True)
            frozen_test.write_text("# Diagnostic command fixture; never executed here\n", encoding="utf-8")
            (output / "source-before.json").write_text(json.dumps({
                "checked_commit": "a" * 40, "checked_tree": "b" * 40}), encoding="utf-8")
            args = argparse.Namespace(ancestor_projection=None, skip_derived_state=True)
            with patch.object(suite, "prepare_round2_diagnostic", return_value=(projection, output)) as prepare, \
                    patch.object(suite, "run") as commands, \
                    patch.object(suite, "verify_source_freeze") as verify, patch("builtins.print"):
                suite.run_round2_suite(args)
            prepare.assert_called_once_with(args)
            verify.assert_called_once_with(output / "source-before.json")
            calls = [call.args[0] for call in commands.call_args_list]
            self.assertEqual(sum("--ancestor-projection" in argv for argv in calls), 2)
            frozen = next(argv for argv in calls if str(projection / "research/RHRC/tools/run_suite.py") in argv)
            self.assertIn("--skip-derived-state", frozen)
            native_tests = {"test_claim_firewall.py", "test_native_evaluation.py", "test_gram_diagnostics.py", "test_primal_certifier.py"}
            selected = [argv[argv.index("-p") + 1] for argv in calls if str(HERE / "tests") in argv and "-p" in argv]
            self.assertEqual(selected, list(suite.DIAGNOSTIC_TEST_FILES) * 2)
            self.assertFalse(set(selected) & native_tests)
            report = json.loads((output / "diagnostic-report.json").read_bytes())
            self.assertEqual(report["status"], "PASS_DIAGNOSTIC_METADATA_AND_FROZEN_BASE_REGRESSIONS_ONLY")
            self.assertFalse(report["full_core_accepted"])
            self.assertFalse(report["full_release_accepted"])
            self.assertEqual(report["human_review"], "NOT_ESTABLISHED")
            self.assertEqual(report["native_lean_typed_controls"], "NOT_RUN_HERE_REQUIRED_IN_ROUND2_CONTROLS_JOB")

    def test_failed_diagnostic_command_cannot_emit_success_report(self):
        TEMP_ROOT.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=TEMP_ROOT) as tmp:
            output = Path(tmp).resolve()
            with patch.object(suite, "prepare_round2_diagnostic", return_value=(output / "source", output)), \
                    patch.object(suite, "run", side_effect=subprocess.CalledProcessError(1, ["fixture"])):
                with self.assertRaises(subprocess.CalledProcessError):
                    suite.run_round2_suite(argparse.Namespace(ancestor_projection=None, skip_derived_state=True))
            self.assertFalse((output / "diagnostic-report.json").exists())

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
        generated = workflow.split("  generated:\n", 1)[1].split("  harvest:\n", 1)[0]
        self.assertLess(generated.index("Build exact native prerequisites for every paired typed control"),
                        generated.index("Run all frozen and current suites with explicit ancestry scope"))
        self.assertIn("NATIVE_PREREQUISITES_WARM_PROJECT_OBJECTS_ALLOWED_NO_COLD_CLAIM", generated)
        self.assertIn("OPICA2_TYPED_CONTROL_OUTPUT: /tmp/opica2-evidence/typed-native-pairs", generated)

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
