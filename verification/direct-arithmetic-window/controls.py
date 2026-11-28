#!/usr/bin/env python3
"""Source controls, real Lean audit fixtures, and independent-checker controls."""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


stage = load("stage")
evidence = load("evidence")


def tamper_export(source, target, theorem):
    names, count = {0: ""}, 0
    with source.open() as src, target.open("w") as dst:
        for line in src:
            obj = json.loads(line)
            if "str" in obj:
                x = obj["str"]
                names[obj["in"]] = ".".join(x for x in (names[x["pre"]], x["str"]) if x)
            elif "num" in obj:
                x = obj["num"]
                names[obj["in"]] = names[x["pre"]] + "." + str(x["i"])
            if "thm" in obj and names.get(obj["thm"]["name"]) == theorem:
                # Valid NDJSON, unchanged statement, deliberately ill-typed proof:
                # the proposition itself has type Prop, not a proof of itself.
                obj["thm"]["value"] = obj["thm"]["type"]
                count += 1
            dst.write(json.dumps(obj, separators=(",", ":")) + "\n")
    stage.require(count == 1, "tamper control did not find exactly one target theorem")


def validate_tampered_rejection(text, exit_code):
    stage.require(exit_code != 0, "tampered proof unexpectedly accepted")
    # Official Nanoda reports this assertion for the observed type mismatch.
    # A generic panic or a missing declaration is not the intended rejection.
    pattern = r"mismatch|expected|typecheck|type check|assertion failed: self\.def_eq\(u, v\)"
    stage.require(re.search(pattern, text, re.I), "tampered proof failed for an unrelated reason")
    for kernel in ("Lean default", "Lean paranoid", "nanoda"):
        stage.require(kernel + " kernel rejected the solution" in text, "tampered proof not rejected by " + kernel)


class SourceControls(unittest.TestCase):
    def test_imports_ignore_nested_comments(self):
        src = b'import A\n/- import Never\n/- import Nested -/\nimport this file.\n-/\nimport B C -- tail\n'
        self.assertEqual(stage.imports(src), ["A", "B", "C"])
        self.assertEqual(stage.imports(b'import A\ndef s := "text\nimport NotAnImport\n"\n'), ["A"])

    def test_bad_paths(self):
        for path in ("../x", "/x", "a//b", "a\\b", "a/./b"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                stage.safe(path)

    def test_project_cache_symlinks_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); project = root / "stage"; project.mkdir()
            external = root / "external"; external.mkdir()
            (external / "stale.olean").write_bytes(b"inherited object")
            cache = project / ".lake"
            cache.symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symlink project cache"):
                stage.project_cache_is_fresh(project)
            cache.unlink(); cache.mkdir()
            (cache / "build").symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symlink project cache"):
                stage.project_cache_is_fresh(project)
            (cache / "build").unlink()
            packages = cache / "packages"; packages.mkdir()
            (packages / "cached.olean").write_bytes(b"dependency object")
            self.assertTrue(stage.project_cache_is_fresh(project))
            (cache / "lakefile.olean").write_bytes(b"stale project configuration")
            self.assertFalse(stage.project_cache_is_fresh(project))

    def test_dependency_preparation_rejects_source_mutation(self):
        runner = load("run")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); package = root / ".lake/packages/mathlib"
            package.mkdir(parents=True)
            (package / ".gitignore").write_text(".lake/\n*.hash\n")
            (package / "Source.lean").write_text("-- pinned source\n")
            def git(*args):
                return subprocess.check_output(["git", "-C", str(package), *args], stderr=subprocess.STDOUT)
            git("init", "--quiet"); git("add", ".")
            git("-c", "user.name=Control", "-c", "user.email=control@example.invalid", "commit", "--quiet", "-m", "fixture")
            pin = git("rev-parse", "HEAD").decode().strip()
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "git", "name": "mathlib", "rev": pin}]}))
            class FixtureRun:
                args = argparse.Namespace(jobs=2)
                out = root / "preparation"
                mutate = False
                def command(self, argv, _name, cwd, _env):
                    if argv[1:] != ["build", "Mathlib"] or cwd != root:
                        raise ValueError("preparation attempted a different target")
                    cache = package / ".lake"; cache.mkdir(exist_ok=True)
                    (cache / "cached.olean.hash").write_text("metadata")
                    if self.mutate:
                        (package / "Untracked.lean").write_text("-- unexpected source\n")
            fixture = FixtureRun()
            with patch.dict(runner.LOCK, mathlib=pin):
                runner.prepare_dependencies(fixture, root, root / "compiler")
                self.assertTrue((fixture.out / "dependency-packages-after.json").is_file())
                fixture.mutate = True
                with self.assertRaisesRegex(ValueError, "package source changed"):
                    runner.prepare_dependencies(fixture, root, root / "compiler")

    def test_exact_comparator_export_roots(self):
        config = json.loads((HERE / "comparator/config.json").read_text())
        config["theorem_names"] = ["direct_window_preflight"]
        primitives = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
                      "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
                      "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
                      "optParam", "autoParam", "semiOutParam", "outParam"]
        expected = ["lake", "env", "exporter", "PreflightSolution", "--", "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
                    "direct_window_preflight", "propext", "Quot.sound", "Classical.choice", *primitives]
        self.assertEqual(stage.comparator_export_command("lake", "exporter", "PreflightSolution", config), expected)
        lock = stage.read_json(HERE / "SOURCE_LOCK.json")
        lock["comparator_export_roots"]["primitive_targets"].append("outParam")
        with patch.object(stage, "read_json", return_value=lock), self.assertRaisesRegex(ValueError, "duplicate"):
            stage.comparator_export_command("lake", "exporter", "PreflightSolution", config)
        config["permitted_axioms"].append("Lean.trustCompiler")
        with self.assertRaisesRegex(ValueError, "axiom policy"):
            stage.comparator_export_command("lake", "exporter", "PreflightSolution", config)

    def test_observed_nanoda_type_rejection(self):
        observed = """Running Lean paranoid kernel on solution
Lean paranoid kernel rejected the solution
Running nanoda kernel on solution
thread 'thread_2' (5) panicked at src/tc.rs:955:71:
assertion failed: self.def_eq(u, v)
thread 'main' (2) panicked at src/tc.rs:173:26:
A thread in `check_all_declars` panicked while being joined: Any { .. }
nanoda kernel rejected the solution
Running Lean default kernel on solution
error: Lean paranoid exited with 1
Lean default kernel rejected the solution
"""
        validate_tampered_rejection(observed, 1)
        unrelated = observed.replace("assertion failed: self.def_eq(u, v)",
                                     "declaration not found in infer_const, Lean.trustCompiler")
        with self.assertRaisesRegex(ValueError, "unrelated reason"):
            validate_tampered_rejection(unrelated, 101)
        with self.assertRaisesRegex(ValueError, "not rejected by nanoda"):
            validate_tampered_rejection(observed.replace("nanoda kernel rejected the solution", ""), 1)
        with self.assertRaisesRegex(ValueError, "unexpectedly accepted"):
            validate_tampered_rejection(observed, 0)

    def test_changed_effective_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); (p / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
            (p / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": "pin"}]}))
            (p / "Proof.lean").write_text("theorem good : True := True.intro\n")
            receipt = p.parent / (p.name + ".json")
            data = {"schema": "DIRECT_WINDOW_STAGE_V1", "head": "head", "source_toolchain": "leanprover/lean4:v4.33.1",
                    "mathlib": "pin", "files": [{"path": n, "sha256": h} for n,h in stage.staged_files(p).items()]}
            receipt.write_text(json.dumps(data))
            try:
                stage.verify_stage(p, receipt)
                (p / "Proof.lean").write_text("axiom bad : False\n")
                with self.assertRaises(ValueError): stage.verify_stage(p, receipt)
            finally:
                receipt.unlink()

    def test_mixed_candidate_and_missing_phase_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def fake(path, phase):
                return {"phase": phase, "head": "bad" if phase == "alternate-checker" else "good",
                        "tree": "t", "run_id": "1", "run_attempt": "1"}
            with patch.object(evidence, "verify", side_effect=fake), self.assertRaisesRegex(ValueError, "mixed"):
                evidence.aggregate(root, root / "result.json")
            with self.assertRaises(FileNotFoundError): evidence.aggregate(root, root / "result.json")

    def test_tamper_changes_only_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            before = [{"str": {"pre": 0, "str": "target"}, "in": 1},
                      {"thm": {"name": 1, "type": 2, "value": 3, "levelParams": [], "all": []}}]
            (p / "good").write_text("".join(json.dumps(x) + "\n" for x in before))
            tamper_export(p / "good", p / "bad", "target")
            after = [json.loads(x) for x in (p / "bad").read_text().splitlines()]
            self.assertEqual(after[0], before[0])
            self.assertEqual(after[1]["thm"]["type"], before[1]["thm"]["type"])
            self.assertNotEqual(after[1]["thm"]["value"], before[1]["thm"]["value"])


def command(argv, cwd, log, env=None, success=True):
    with log.open("w") as handle:
        r = subprocess.run([str(x) for x in argv], cwd=cwd, env=env, stdout=handle, stderr=subprocess.STDOUT)
    text = log.read_text(errors="replace")
    print(text, end="")
    stage.require((r.returncode == 0) == success, "unexpected process result: " + str(argv))
    return text, r.returncode


def audit_controls(prefix, work, out):
    work.mkdir(parents=True, exist_ok=False); out.mkdir(parents=True, exist_ok=True)
    (work / "DirectWindowAudit").mkdir()
    for source, target in (("AuditCore", "Core"), ("SmokeFixtures", "SmokeFixtures"), ("AuditSmoke", "Smoke")):
        shutil.copyfile(HERE / (source + ".lean"), work / "DirectWindowAudit" / (target + ".lean"))
    (work / "lakefile.toml").write_text('name = "DirectWindowControls"\n[[lean_lib]]\nname = "DirectWindowAudit"\nglobs = ["DirectWindowAudit.+"]\n')
    (work / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    env = dict(os.environ, PATH=str(prefix / "bin") + os.pathsep + os.environ["PATH"],
               DIRECT_WINDOW_AUDIT_DIR=str((out / "audit").resolve()), LAKE_ARTIFACT_CACHE="false")
    text, _ = command([prefix / "bin/lake", "build", "DirectWindowAudit.Smoke"], work, out / "audit-controls.log", env)
    stage.require("DIRECT_WINDOW_AUDIT_CONTROLS_PASS" in text, "audit controls did not finish")


def checker_controls(prefix, judge_prefix, exporter, work, out):
    work.mkdir(parents=True, exist_ok=False); out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(prefix / "bin") + os.pathsep + os.environ["PATH"], LAKE_ARTIFACT_CACHE="false")
    source_version = subprocess.check_output([str(prefix / "bin/lean"), "--version"], text=True).strip()
    judge_version = subprocess.check_output([str(judge_prefix / "bin/lean"), "--version"], text=True).strip()
    stage.require("version 4.33.1" in source_version and "version 4.36.0" in judge_version, "preflight toolchain mismatch")
    exporter_commit = subprocess.check_output(["git", "-C", str(exporter.parents[3]), "rev-parse", "HEAD"], text=True).strip()
    expected_exporter = json.loads((HERE / "SOURCE_LOCK.json").read_text())["exporter"]["commit"]
    stage.require(exporter_commit == expected_exporter, "preflight exporter source mismatch")
    settings = json.loads((HERE / "comparator/config.json").read_text())
    settings.update(challenge_module="PreflightChallenge", solution_module="PreflightSolution", theorem_names=["direct_window_preflight"])
    config = out / "preflight-config.json"; config.write_text(json.dumps(settings, indent=2) + "\n")
    challenge = work / "challenge"; challenge.mkdir()
    def setup(where, name, text):
        (where / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (where / "lakefile.toml").write_text('name = "Preflight"\n[[lean_lib]]\nname = "' + name + '"\n')
        (where / (name + ".lean")).write_text(text)
    def export(where, module, target, label):
        command([prefix / "bin/lake", "build", module], where, out / (label + "-build.log"), env)
        with target.open("wb") as handle, (out / (label + "-export.log")).open("wb") as errors:
            # Use exactly the judge's required primitive roots alongside the
            # fixture. Whole-Init exports include unrelated compiler-trust code.
            r = subprocess.run(stage.comparator_export_command(prefix / "bin/lake", exporter, module, settings),
                               cwd=where, env=env, stdout=handle, stderr=errors)
        stage.require(r.returncode == 0 and target.stat().st_size > 0, "preflight export failed")
    setup(challenge, "PreflightChallenge", "import Init\ntheorem direct_window_preflight : True := by sorry\n")
    challenge_export = work / "challenge.export"
    export(challenge, "PreflightChallenge", challenge_export, "challenge")
    clean = work / "clean"; clean.mkdir()
    setup(clean, "PreflightSolution", "import Init\ntheorem direct_window_preflight : True := True.intro\n")
    clean_export = work / "clean.export"
    export(clean, "PreflightSolution", clean_export, "clean")
    judge = work / "judge"; judge.mkdir()
    judge_env = dict(os.environ, PATH=str(judge_prefix / "bin") + os.pathsep + os.environ["PATH"])
    def judge_export(path, name, valid):
        text, rc = command([judge_prefix / "bin/lake", "comparator", "--config", config,
                           "--challenge-from-export", challenge_export, "--solution-from-export", path],
                          judge, out / (name + "-comparator.log"), judge_env, success=valid)
        stage.require(("Your solution is okay!" in text) == valid, "incorrect comparator disposition")
        return text, rc
    clean_text, _ = judge_export(clean_export, "clean", True)
    for kernel in ("Lean default", "Lean paranoid", "nanoda"):
        stage.require(kernel + " kernel accepts the solution" in clean_text, "missing clean kernel acceptance: " + kernel)
    cases = {
        "wrong-statement": "import Init\ntheorem direct_window_preflight : True ∧ True := ⟨True.intro, True.intro⟩\n",
        "extra-axiom": "import Init\naxiom direct_window_extra_axiom : True\ntheorem direct_window_preflight : True := direct_window_extra_axiom\n",
    }
    rejected = []
    for label, source in cases.items():
        path = work / label; path.mkdir(); setup(path, "PreflightSolution", source)
        target = work / (label + ".export"); export(path, "PreflightSolution", target, label)
        text, _ = judge_export(target, label, False)
        pattern = r"axiom" if label == "extra-axiom" else r"type|statement|mismatch|match"
        stage.require(re.search(pattern, text, re.I), "negative case failed for an unrelated reason")
        if label == "extra-axiom":
            stage.require("direct_window_extra_axiom" in text, "wrong axiom rejection")
        rejected.append(label)
    bad = work / "tampered.export"; tamper_export(clean_export, bad, "direct_window_preflight")
    text, rc = judge_export(bad, "tampered-export", False)
    validate_tampered_rejection(text, rc)
    rejected.append("tampered-export")
    (out / "preflight.json").write_text(json.dumps({"accepted_clean": True, "rejected": rejected,
        "source_version": source_version, "judge_version": judge_version, "exporter_commit": exporter_commit,
        "exporter_sha256": evidence.digest(exporter), "permitted_axioms": settings["permitted_axioms"],
        "external_kernels": settings["external_kernels"]}, indent=2) + "\n")
    print("DIRECT_WINDOW_CHECKER_CONTROLS_PASS")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--checker", action="store_true")
    parser.add_argument("--source-prefix", type=Path)
    parser.add_argument("--judge-prefix", type=Path)
    parser.add_argument("--exporter", type=Path)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.audit:
        audit_controls(args.source_prefix.resolve(), args.work.resolve(), args.out.resolve())
    elif args.checker:
        checker_controls(args.source_prefix.resolve(), args.judge_prefix.resolve(), args.exporter.resolve(),
                         args.work.resolve(), args.out.resolve())
    else:
        unittest.main(argv=[sys.argv[0]], verbosity=2)
