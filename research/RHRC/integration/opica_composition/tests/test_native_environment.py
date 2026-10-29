"""Portable regressions for pinned toolchain aliases and environment identity.

These are filesystem/identity tests, not native compiler qualification. Real
temporary files supply the bytes. Only leaf lstat/readlink results model Linux
symlinks, so Windows hosts need no symlink creation privilege. The compiler
version subprocess is fixed test data and never supplies proof authority.
Pinned benchmark projection tests use real Git objects and checkout commands;
Linux tests create actual symlinks rather than skipping their conversion.
"""
from contextlib import contextmanager, redirect_stderr
from dataclasses import asdict, replace
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from research.RHRC.integration.opica_composition import cli, executor, qualification, snapshot
from research.RHRC.integration.opica_composition.accept import verify_lane_bundle
from research.RHRC.integration.opica_composition.canonical import ContractError
from research.RHRC.integration.opica_composition.contracts import SearchBudget, WorkerConfig


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def native_path(path):
    return Path(os.path.abspath(path))


@contextmanager
def leaf_links(links, *, reparse=()):
    """Change leaf metadata only; all directories and file reads stay real."""
    links = {native_path(path): target for path, target in links.items()}
    reparse = {native_path(path) for path in reparse}
    real_lstat, real_readlink = os.lstat, os.readlink

    def lstat(path, *args, **kwargs):
        key = native_path(path)
        if key in links:
            return SimpleNamespace(st_mode=stat.S_IFLNK | 0o777,
                                   st_file_attributes=1024 if key in reparse else 0)
        info = real_lstat(path, *args, **kwargs)
        if key in reparse:
            return SimpleNamespace(st_mode=info.st_mode, st_file_attributes=1024)
        return info

    def readlink(path, *args, **kwargs):
        key = native_path(path)
        return links[key] if key in links else real_readlink(path, *args, **kwargs)

    # Path.lstat uses os.stat(follow_symlinks=False) on some Python versions.
    # Model the same leaf metadata there without changing is_file or traversal.
    with patch.object(os, "lstat", side_effect=lstat), patch.object(Path, "lstat", new=lstat), \
            patch.object(os, "readlink", side_effect=readlink):
        yield


class NativeEnvironmentTests(unittest.TestCase):
    VERSION = b"Lean pinned toolchain fixture\n"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="opica-toolchain-alias-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.toolchain = self.root / "toolchain"
        self.imports = self.root / "imports"
        self.evidence = self.root / "evidence"
        for directory in (self.toolchain / "bin", self.toolchain / "lib", self.imports, self.evidence):
            directory.mkdir(parents=True)
        self.lean = self.write(self.toolchain / "bin" / "lean", b"compiler fixture bytes")
        self.module = self.write(self.imports / "Module.olean", b"import object bytes")
        self.worker = WorkerConfig(str(self.lean), str(self.toolchain), [str(self.imports)], production=False)

    def write(self, path, raw=b"alias placeholder bytes"):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return path

    def environment(self, *, manifest_output=None):
        with patch.object(executor.subprocess, "run", return_value=SimpleNamespace(stdout=self.VERSION)) as version:
            result = executor.worker_environment(self.worker, manifest_output=manifest_output)
        version.assert_called_once()
        self.assertEqual(version.call_args.args[0], [str(self.lean), "--version"])
        return result

    def test_regular_toolchain_file_uses_actual_bytes(self):
        target = self.write(self.toolchain / "lib" / "libLLVM.so", b"regular library bytes")
        self.assertEqual(executor._toolchain_file_record(target, self.toolchain),
                         (sha256(b"regular library bytes"), []))

    def test_contained_alias_chain_hashes_target_and_records_each_raw_link(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        middle = self.write(self.toolchain / "lib" / "versions" / "LLVM.so")
        target = self.write(self.toolchain / "payload" / "LLVM.bin", b"actual pinned library bytes")
        links = {alias: "versions/LLVM.so", middle: "../../payload/LLVM.bin"}
        with leaf_links(links):
            actual = executor._toolchain_file_record(alias, self.toolchain)
        self.assertEqual(actual, (sha256(target.read_bytes()), [
            {"path": "lib/libLLVM.so", "target": "versions/LLVM.so"},
            {"path": "lib/versions/LLVM.so", "target": "../../payload/LLVM.bin"}]))

    def test_absolute_contained_alias_is_bound_to_its_raw_target(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        target = self.write(self.toolchain / "lib" / "LLVM.bin", b"actual library bytes")
        with leaf_links({alias: str(target)}):
            value, links = executor._toolchain_file_record(alias, self.toolchain)
        self.assertEqual(value, sha256(target.read_bytes()))
        self.assertEqual(links, [{"path": "lib/libLLVM.so", "target": str(target)}])

    def test_file_outside_approved_prefix_is_rejected(self):
        outside = self.write(self.root / "outside.so", b"outside bytes")
        with self.assertRaises(ContractError):
            executor._toolchain_file_record(outside, self.toolchain)

    def test_relative_and_absolute_escapes_are_rejected(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        outside = self.write(self.root / "outside.bin", b"outside bytes")
        for target in ("../../outside.bin", str(outside)):
            with self.subTest(target=target), leaf_links({alias: target}), self.assertRaises(ContractError):
                executor._toolchain_file_record(alias, self.toolchain)

    def test_cycle_and_excessive_chain_are_rejected_at_the_boundary(self):
        first = self.write(self.toolchain / "lib" / "first.so")
        second = self.write(self.toolchain / "lib" / "second.so")
        with leaf_links({first: "second.so", second: "first.so"}), self.assertRaises(ContractError):
            executor._toolchain_file_record(first, self.toolchain)
        aliases = [self.write(self.toolchain / "lib" / ("link" + str(index) + ".so")) for index in range(41)]
        self.write(self.toolchain / "lib" / "payload.bin", b"bounded chain bytes")
        links = {path: "link" + str(index + 1) + ".so" for index, path in enumerate(aliases[:-1])}
        links[aliases[39]] = "payload.bin"
        with leaf_links(links):
            self.assertEqual(len(executor._toolchain_file_record(aliases[0], self.toolchain)[1]), 40)
        links[aliases[39]] = "link40.so"
        links[aliases[40]] = "payload.bin"
        with leaf_links(links), self.assertRaises(ContractError):
            executor._toolchain_file_record(aliases[0], self.toolchain)

    def test_dangling_and_directory_targets_are_rejected(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        directory = self.toolchain / "lib" / "directory"
        directory.mkdir()
        with leaf_links({alias: "missing.bin"}), self.assertRaises((ContractError, FileNotFoundError)):
            executor._toolchain_file_record(alias, self.toolchain)
        with leaf_links({alias: "directory"}), self.assertRaises(ContractError):
            executor._toolchain_file_record(alias, self.toolchain)

    def test_linked_parent_and_reparse_leaf_are_rejected(self):
        alias = self.write(self.toolchain / "lib" / "linked" / "libLLVM.so")
        with leaf_links({alias.parent: "other"}), self.assertRaises(ContractError):
            executor._toolchain_file_record(alias, self.toolchain)
        target = self.write(self.toolchain / "lib" / "LLVM.bin", b"library bytes")
        with leaf_links({}, reparse=[target]), self.assertRaises(ContractError):
            executor._toolchain_file_record(target, self.toolchain)
        with leaf_links({alias: "../LLVM.bin"}, reparse=[alias]), self.assertRaises(ContractError):
            executor._toolchain_file_record(alias, self.toolchain)

    def test_link_changed_during_hashing_is_rejected(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        self.write(self.toolchain / "lib" / "payload.bin", b"library bytes")
        with leaf_links({alias: "payload.bin"}), patch.object(os, "readlink", side_effect=["payload.bin", "changed.bin"]):
            with self.assertRaises(ContractError):
                executor._toolchain_file_record(alias, self.toolchain)

    def test_environment_binds_target_bytes_raw_chain_and_exact_manifest(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        target = self.write(self.toolchain / "lib" / "payload.bin", b"actual pinned library bytes")
        manifest = self.evidence / "objects.json"
        links = {"lib/libLLVM.so": [{"path": "lib/libLLVM.so", "target": "payload.bin"}]}
        objects = {"TOOLCHAIN/lib/libLLVM.so": sha256(target.read_bytes()),
                   "IMPORT_0/Module.olean": sha256(self.module.read_bytes())}
        raw = json.dumps({"objects": objects, "toolchain_file_links": links}, ensure_ascii=False,
                         sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
        with leaf_links({alias: "payload.bin"}):
            environment = self.environment(manifest_output=manifest)
        self.assertEqual(environment, {
            "compiler_sha256": sha256(self.lean.read_bytes()),
            "version_sha256": sha256(self.VERSION),
            "object_count": 2,
            "objects_digest": sha256(b"OPICA_IMPORT_OBJECTS_V2\0" + raw),
            "toolchain_file_links": links})
        self.assertEqual(json.loads(manifest.read_bytes()), {
            str(alias.absolute()): sha256(target.read_bytes()),
            str(self.module.absolute()): sha256(self.module.read_bytes())})

        # Lean's shell thread pool follows its CLI flag. Merely retaining the
        # environment variable can still spawn a host-sized pool under RLIMIT_AS.
        budgets = (SearchBudget(), SearchBudget(heartbeats=314159, wall_seconds=17,
                   output_bytes=512345, memory_bytes=987654321, disk_bytes=456789000))
        for budget in budgets:
            for production in (False, True):
                with self.subTest(production=production, budget=budget):
                    worker = WorkerConfig(str(self.lean), str(self.toolchain), [str(self.imports)],
                                          bubblewrap="/fixture/bwrap", prlimit="/fixture/prlimit",
                                          production=production)
                    inherited = {"PATH": "unsafe-inherited-path", "LEAN_PATH": "unsafe-imports",
                                 "LEAN_NUM_THREADS": "999", "OPICA_TEST_SECRET": "not-a-real-secret",
                                 "SYSTEMROOT": "system-root", "WINDIR": "windows-directory",
                                 "TEMP": "temporary-directory", "TMP": "temporary-directory"}
                    with patch.dict(os.environ, inherited, clear=True):
                        command, env = executor._recipe(worker, self.evidence, "Smoke.lean",
                                                        "Smoke.olean", budget)
                    lean_index = command.index(str(self.lean))
                    self.assertEqual(command[lean_index + 1], "-j2")
                    self.assertEqual(command[lean_index + 2], "-s262144")
                    self.assertEqual(command.count("-j2"), 1)
                    self.assertEqual(command.count("-s262144"), 1)
                    self.assertNotIn("-j2", command[:lean_index])
                    self.assertNotIn("-s262144", command[:lean_index])
                    self.assertEqual(command.count(str(self.lean)), 1)
                    if not production:
                        self.assertEqual(command, [str(self.lean), "-j2", "-s262144", "--root=" + str(self.evidence),
                            "-DmaxHeartbeats=" + str(budget.heartbeats), "-DmaxRecDepth=2048",
                            "-o", str(self.evidence / "Smoke.olean"), str(self.evidence / "Smoke.lean")])
                        self.assertEqual(env, {"SYSTEMROOT": "system-root", "WINDIR": "windows-directory",
                            "TEMP": "temporary-directory", "TMP": "temporary-directory",
                            "PATH": str(self.lean.parent), "LEAN_NUM_THREADS": "2",
                            "LEAN_PATH": os.pathsep.join([str(self.evidence), str(self.imports)])})
                    else:
                        prefix = [worker.prlimit, "--as=" + str(budget.memory_bytes),
                            "--cpu=" + str(budget.wall_seconds),
                            "--fsize=" + str(budget.output_bytes), "--", worker.bubblewrap,
                            "--unshare-all", "--die-with-parent", "--new-session", "--clearenv",
                            "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
                        suffix = ["--bind", str(self.evidence), "/out", "--chdir", "/out",
                            "--setenv", "PATH", str(self.lean.parent),
                            "--setenv", "LEAN_NUM_THREADS", "2",
                            "--setenv", "LEAN_PATH", ":".join(["/out", str(self.imports)]),
                            worker.prlimit, "--nproc=64", "--", str(self.lean), "-j2", "-s262144", "--root=/out",
                            "-DmaxHeartbeats=" + str(budget.heartbeats), "-DmaxRecDepth=2048",
                            "-o", "/out/Smoke.olean", "/out/Smoke.lean"]
                        self.assertEqual(command[:len(prefix)], prefix)
                        self.assertEqual(command[-len(suffix):], suffix)
                        self.assertNotIn("--nproc=64", command[:command.index(worker.bubblewrap)])
                        self.assertEqual(command[lean_index - 3:lean_index],
                                         [worker.prlimit, "--nproc=64", "--"])
                        self.assertEqual(command.count("--bind"), 1)
                        for mounted in (self.toolchain, self.imports):
                            index = command.index(str(mounted), len(prefix))
                            self.assertEqual(command[index - 1:index + 2],
                                             ["--ro-bind", str(mounted), str(mounted)])
                        self.assertEqual(env, {})
                    with patch.dict(os.environ, inherited, clear=True):
                        math_command, _ = executor._recipe(worker, self.evidence, "Zeta23/Smoke.lean",
                            "Zeta23/Smoke.olean", budget, mathematical_support=True)
                    math_lean_index = math_command.index(str(self.lean))
                    self.assertEqual(math_command[math_lean_index + 1:math_lean_index + 3],
                                     ["-j2", "-s262144"])
                    self.assertEqual(math_command.count("-s262144"), 1)
                    self.assertNotIn("-s262144", math_command[:math_lean_index])
                    if production:
                        self.assertNotIn("--nproc=64", math_command[:math_command.index(worker.bubblewrap)])
                        self.assertEqual(math_command[math_lean_index - 3:math_lean_index],
                                         [worker.prlimit, "--nproc=64", "--"])

    def test_target_byte_change_changes_environment_identity(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        target = self.write(self.toolchain / "lib" / "payload.bin", b"library before")
        with leaf_links({alias: "payload.bin"}):
            before = self.environment()
            target.write_bytes(b"library after")
            after = self.environment()
        self.assertNotEqual(before["objects_digest"], after["objects_digest"])
        self.assertEqual(before["toolchain_file_links"], after["toolchain_file_links"])

    def test_equal_byte_retarget_changes_environment_identity(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so")
        for name in ("first.bin", "second.bin"):
            self.write(self.toolchain / "lib" / name, b"same library bytes")
        with leaf_links({alias: "first.bin"}):
            before = self.environment()
        with leaf_links({alias: "second.bin"}):
            after = self.environment()
        self.assertEqual(before["object_count"], after["object_count"])
        self.assertNotEqual(before["objects_digest"], after["objects_digest"])

    def test_versioned_library_alias_is_inventoried_without_a_selected_suffix(self):
        alias = self.write(self.toolchain / "lib" / "libLLVM.so.19.1")
        target = self.write(self.toolchain / "lib" / "payload.bin", b"versioned library bytes")
        manifest = self.evidence / "versioned-objects.json"
        with leaf_links({alias: "payload.bin"}):
            environment = self.environment(manifest_output=manifest)
        self.assertEqual(environment["object_count"], 2)
        self.assertEqual(environment["toolchain_file_links"], {
            "lib/libLLVM.so.19.1": [{"path": "lib/libLLVM.so.19.1", "target": "payload.bin"}]})
        self.assertEqual(json.loads(manifest.read_bytes())[str(alias.absolute())], sha256(target.read_bytes()))

    def test_dangling_alias_cannot_be_silently_omitted_from_environment(self):
        # A directory placeholder preserves the is_file()==False behavior of a
        # dangling link; only lstat/readlink are replaced, not enumeration.
        alias = self.toolchain / "lib" / "libLLVM.so"
        alias.mkdir()
        (self.toolchain / "lib" / "directory").mkdir()
        for target in ("missing.bin", "directory"):
            with self.subTest(target=target), leaf_links({alias: target}), \
                    self.assertRaises((ContractError, FileNotFoundError)):
                self.environment()

    def test_import_object_alias_remains_rejected(self):
        self.write(self.imports / "payload.bin", b"import bytes")
        for name in ("Alias.olean", "Alias.payload"):
            alias = self.write(self.imports / name)
            with self.subTest(name=name), leaf_links({alias: "payload.bin"}), self.assertRaises(ContractError):
                self.environment()

    def test_source_and_evidence_aliases_remain_rejected(self):
        repo = self.root / "source-repo"
        source = self.write(repo / "Zeta23" / "Injected.lean", b"theorem fixture : True := True.intro")
        evidence = self.write(self.evidence / "OpicaAttempt.olean", b"evidence bytes")
        with leaf_links({source: "Other.lean", evidence: "Other.olean"}):
            with self.assertRaises(ContractError):
                snapshot.discover_source_paths(repo)
            with self.assertRaises(ContractError):
                snapshot.file_hash(source)
            with self.assertRaises(ContractError):
                executor.validate_output_inventory(self.evidence)


class PinnedBenchmarkProjectionTests(unittest.TestCase):
    RELATIVE = "scripts/bench/size/run.py"
    BLOB = "e5224d533ef27b001224859a9b36696846a7e7fe"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="opica-package-projection-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.fixture_number = 0
        self.git = shutil.which("git")
        self.assertIsNotNone(self.git, "Real Git is required for package projection regressions")
        self.git_env = {**os.environ, "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                        "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}

    def git_command(self, root, *args, data=None):
        result = subprocess.run([self.git, "-C", str(root), *args], input=data,
                                capture_output=True, env=self.git_env, check=False)
        self.assertEqual(result.returncode, 0, (args, result.stderr.decode("utf-8", "replace")))
        return result.stdout

    def fixture(self, *, raw=b"run", mode="120000", regular=False, extra_alias=None):
        self.fixture_number += 1
        host = self.root / ("host-" + str(self.fixture_number))
        package = host / ".lake" / "packages" / "mathlib"
        alias = package / self.RELATIVE
        alias.parent.mkdir(parents=True)
        self.git_command(package, "init", "--quiet")
        self.git_command(package, "config", "user.name", "OPICA fixture")
        self.git_command(package, "config", "user.email", "fixture@example.invalid")
        self.git_command(package, "config", "core.autocrlf", "false")
        self.git_command(package, "config", "core.symlinks", "false" if os.name == "nt" or regular else "true")
        # Deliberately different bytes prove that projection does not copy the target.
        (alias.parent / "run").write_bytes(b"#!/usr/bin/env python3\nprint('benchmark target')\n")
        self.git_command(package, "add", "--", "scripts/bench/size/run")

        def add_alias(path, contents, git_mode="120000"):
            path.parent.mkdir(parents=True, exist_ok=True)
            if os.name != "nt" and not regular and git_mode == "120000":
                path.symlink_to(os.fsdecode(contents))
                self.assertTrue(path.is_symlink(), "Linux must exercise actual symlink conversion")
            else:
                path.write_bytes(contents)
            blob = self.git_command(package, "hash-object", "-w", "--stdin", data=contents).decode().strip()
            self.git_command(package, "update-index", "--add", "--cacheinfo",
                             git_mode + "," + blob + "," + path.relative_to(package).as_posix())

        add_alias(alias, raw, mode)
        if extra_alias is not None:
            add_alias(package / extra_alias, b"../target")
        self.git_command(package, "commit", "--quiet", "-m", "Pinned benchmark alias fixture")
        self.assertEqual(self.git_command(package, "status", "--porcelain", "--untracked-files=all"), b"")
        return host, package, alias, self.git_command(package, "rev-parse", "HEAD").decode().strip()

    @contextmanager
    def linux_alias_metadata_on_windows(self, alias):
        # Git may regard an existing symlink as already up to date even with
        # core.symlinks=false. Keep the Windows model linked until the helper
        # actually removes the verified leaf; readlink must not advance it.
        real_lstat, real_readlink, real_unlink = os.lstat, os.readlink, os.unlink
        initial = real_lstat(alias)
        pending = [os.name == "nt"]
        events = []
        reads = []
        if os.name != "nt":
            self.assertTrue(alias.is_symlink(), "Linux must exercise an actual symlink")

        def is_alias(path, kwargs):
            if kwargs.get("dir_fd") is None:
                return native_path(path) == native_path(alias)
            parent = os.fstat(kwargs["dir_fd"])
            actual_parent = real_lstat(alias.parent)
            return os.fsdecode(path) == alias.name and (parent.st_dev, parent.st_ino) == \
                (actual_parent.st_dev, actual_parent.st_ino)

        def lstat(path, *args, **kwargs):
            if pending[0] and is_alias(path, kwargs):
                return SimpleNamespace(st_mode=stat.S_IFLNK | 0o777, st_file_attributes=0,
                                       st_dev=initial.st_dev, st_ino=initial.st_ino,
                                       st_size=initial.st_size, st_mtime_ns=initial.st_mtime_ns)
            return real_lstat(path, *args, **kwargs)

        def readlink(path, *args, **kwargs):
            if pending[0] and is_alias(path, kwargs):
                reads.append("run")
                return "run"
            return real_readlink(path, *args, **kwargs)

        def unlink(path, *args, **kwargs):
            matched = is_alias(path, kwargs)
            result = real_unlink(path, *args, **kwargs)
            if matched:
                pending[0] = False
                events.append("removed")
                with self.assertRaises(FileNotFoundError):
                    real_lstat(alias)
            return result

        with patch.object(os, "lstat", side_effect=lstat), patch.object(Path, "lstat", new=lstat), \
                patch.object(os, "readlink", side_effect=readlink), patch.object(os, "unlink", side_effect=unlink):
            yield events
        if os.name == "nt":
            self.assertTrue(reads, "The modeled symlink branch must inspect its raw target")
            self.assertFalse(pending[0], "The modeled symlink must persist until its actual unlink")
        self.assertEqual(events, ["removed"], "The verified leaf must actually be removed once")
        self.assertTrue(stat.S_ISREG(real_lstat(alias).st_mode))
        events.append("recreated")

    def project(self, package, head, *, blob=None):
        return qualification._materialize_pinned_benchmark_alias(
            package, expected_commit=head, expected_blob=self.BLOB if blob is None else blob)

    def identity(self, package):
        return (self.git_command(package, "rev-parse", "HEAD"),
                self.git_command(package, "rev-parse", "HEAD^{tree}"),
                self.git_command(package, "ls-files", "--stage", "-z"),
                self.git_command(package, "status", "--porcelain", "--untracked-files=all"))

    def test_pinned_alias_projection_uses_real_git_and_keeps_source_identity(self):
        host, package, alias, head = self.fixture()
        before = self.identity(package)
        target = alias.parent / "run"
        target_before = target.read_bytes()
        with self.linux_alias_metadata_on_windows(alias) as events:
            record = self.project(package, head)
        self.assertEqual(events, ["removed", "recreated"])
        self.assertEqual(target.read_bytes(), target_before)
        self.assertEqual(self.identity(package), before)
        self.assertTrue(stat.S_ISREG(os.lstat(alias).st_mode))
        self.assertFalse(alias.is_symlink())
        self.assertEqual(alias.read_bytes(), b"run")
        self.assertEqual(record, {
            "policy": "EXACT_PINNED_BENCHMARK_LINK_TEXT_V1", "path": self.RELATIVE,
            "commit": head, "tree": before[1].decode().strip(), "git_mode": "120000",
            "git_blob": self.BLOB, "raw_link_text": "run", "input_leaf_kind": "SYMLINK",
            "checkout_leaf_kind": "REGULAR_LINK_TEXT", "checkout_core_symlinks": False,
            "checkout_sha256": sha256(b"run"), "target_dereferenced": False})
        self.assertEqual(self.git_command(package, "config", "--local", "--get", "core.symlinks"), b"false\n")
        relative = ".lake/packages/mathlib/" + self.RELATIVE
        self.assertIn(relative, snapshot.discover_source_paths(host))
        self.assertEqual(snapshot.hash_inventory(host, [relative]), {relative: sha256(b"run")})

    def test_regular_git_link_text_projection_is_idempotent(self):
        _, package, alias, head = self.fixture(regular=True)
        before = self.identity(package)
        with patch.object(os, "unlink", wraps=os.unlink) as unlink:
            first = self.project(package, head)
            second = self.project(package, head)
        unlink.assert_not_called()
        self.assertEqual(first, second)
        self.assertEqual(first["input_leaf_kind"], "REGULAR_LINK_TEXT")
        self.assertEqual(alias.read_bytes(), b"run")
        self.assertEqual(self.identity(package), before)

    def test_projection_rejects_wrong_pin_and_reviewed_blob(self):
        _, package, _, head = self.fixture(regular=True)
        before = self.identity(package)
        for expected_head, blob in (("0" * 40, self.BLOB), (head, "0" * 40)):
            with self.subTest(head=expected_head, blob=blob), self.assertRaises(ContractError):
                self.project(package, expected_head, blob=blob)
            self.assertEqual(self.identity(package), before)

    def test_projection_rejects_altered_tracked_blob_and_regular_git_mode(self):
        for raw, mode in ((b"other", "120000"), (b"run", "100644")):
            with self.subTest(raw=raw, mode=mode):
                _, package, _, head = self.fixture(raw=raw, mode=mode, regular=True)
                before = self.identity(package)
                with self.assertRaises(ContractError):
                    self.project(package, head)
                self.assertEqual(self.identity(package), before)

    def test_projection_rejects_altered_index_and_dirty_worktree(self):
        for mutation in ("index", "worktree"):
            with self.subTest(mutation=mutation):
                _, package, alias, head = self.fixture(regular=True)
                if mutation == "index":
                    blob = self.git_command(package, "hash-object", "-w", "--stdin", data=b"other").decode().strip()
                    self.git_command(package, "update-index", "--cacheinfo", "120000," + blob + "," + self.RELATIVE)
                else:
                    alias.write_bytes(b"other")
                before = self.identity(package)
                with self.assertRaises(ContractError):
                    self.project(package, head)
                self.assertEqual(self.identity(package), before)

    def test_projection_does_not_materialize_unreviewed_or_lean_source_aliases(self):
        for relative in ("scripts/unreviewed.py", "Mathlib/Injected.lean", "lakefile.toml"):
            with self.subTest(relative=relative):
                host, package, _, head = self.fixture(extra_alias=relative)
                unknown = package / relative
                self.project(package, head)
                self.assertEqual(self.git_command(package, "ls-files", "--stage", "--", relative).split()[0], b"120000")
                if os.name != "nt":
                    self.assertTrue(unknown.is_symlink())
                    with self.assertRaises(ContractError):
                        snapshot.discover_source_paths(host)
                else:
                    with leaf_links({unknown: "../target"}), self.assertRaises(ContractError):
                        snapshot.discover_source_paths(host)

    def test_projection_rejects_linked_or_reparse_parent(self):
        _, package, alias, head = self.fixture(regular=True)
        before = self.identity(package)
        with leaf_links({alias.parent: "other"}), self.assertRaises(ContractError):
            self.project(package, head)
        with leaf_links({}, reparse=[alias.parent]), self.assertRaises(ContractError):
            self.project(package, head)
        self.assertEqual(self.identity(package), before)

    def test_projection_rejects_reparse_leaf(self):
        _, package, alias, head = self.fixture(regular=True)
        before = self.identity(package)
        with leaf_links({}, reparse=[alias]), self.assertRaises(ContractError):
            self.project(package, head)
        self.assertEqual(self.identity(package), before)


class FailedNativeDiagnosticTests(unittest.TestCase):
    PROBE_SOURCES = {
        "stdlib": "import Lean\nopen Lean Elab Command\nrun_cmd do\n  let _ ← getEnv\n  pure ()\nexample : True := True.intro\n",
        "project": "import Zeta23.RHRC.OpicaComposition.FiniteWorlds\n"
                   "import Zeta23.RHRC.OpicaComposition.Export\n"
                   "run_cmd Zeta23.RHRC.OpicaComposition.exportTarget "
                   "`Zeta23.RHRC.OpicaComposition.FiniteWorlds.IdentityTarget \"value\"\n"}

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="opica-failed-native-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.native = self.root / "native-volume"
        self.repo.mkdir()
        self.native.mkdir()

    def collect(self, name):
        output = self.root / name
        output.mkdir()
        with patch.dict(os.environ, {"OPICA_NATIVE_OUTPUT": str(self.native)}):
            report = cli._collect_failed_native_diagnostics("CURRENT_COMPATIBILITY", self.repo, output)
        return output, report

    def smoke_worker(self, *, project=False):
        """Filesystem fixture only; no test invokes a real compiler or tracer."""
        toolchain = self.root / "toolchain"
        standard = toolchain / "lib" / "lean"
        standard.mkdir(parents=True, exist_ok=True)
        lean = toolchain / "bin" / "lean"
        lean.parent.mkdir(exist_ok=True)
        lean.write_bytes(b"compiler fixture: never executed")
        paths = [str(standard.resolve())]
        if project:
            compiled = self.repo / ".lake" / "build" / "lib" / "lean"
            for name in ("FiniteWorlds", "Export"):
                obj = compiled / "Zeta23" / "RHRC" / "OpicaComposition" / (name + ".olean")
                obj.parent.mkdir(parents=True, exist_ok=True)
                obj.write_bytes(b"prepared import fixture: never loaded")
            paths.insert(0, str(compiled.resolve()))
        return WorkerConfig(str(lean), str(toolchain), paths, production=True)

    def assert_probe_preparation_order(self):
        """Mock orchestration stops before qualification; no full PASS fixture."""
        worker = self.smoke_worker(project=True)
        standard = str((Path(worker.toolchain_root) / "lib" / "lean").resolve())
        compiled = str((self.repo / ".lake/build/lib/lean").resolve())
        (self.repo / "lean-toolchain").write_text(qualification.LEAN_PIN + "\n", encoding="utf-8")
        lake = "/fixture/lake"
        for failed_stage in ("stdlib", "project", "post-source"):
            events, commands = [], {}
            source_calls = [0]
            output = self.native / ("prepare-order-" + failed_stage)

            def source_scope(repo, modules):
                source_calls[0] += 1
                events.append("source-preflight" if source_calls[0] == 1 else "source-recheck")
                return {"fixture": ("e" if failed_stage == "post-source" and source_calls[0] > 1 else "f") * 64}

            def command(argv, repo, env, folder, label, seconds):
                events.append(label)
                commands[label] = (argv, seconds)
                payloads = {"volume": json.dumps({"filesystems": [{"fstype": "tmpfs", "size": 4294967296,
                            "target": str(self.native)}]}),
                            "compiler": "Lean (version 4.33.0-rc2, d8b18978322de05a8f3dba51ef03cf5461676c17)",
                            "prefix": worker.toolchain_root, "lean-path": worker.lean,
                            "selected-build": "mock selected build command only",
                            "import-paths": os.pathsep.join([compiled, standard])}
                raw = payloads[label].encode("utf-8")
                (folder / (label + ".stdout.log")).write_bytes(raw)
                (folder / (label + ".stderr.log")).write_bytes(b"")
                return {"argv": argv, "returncode": 0, "timeout": False,
                        "stdout": label + ".stdout.log", "stderr": label + ".stderr.log"}

            def probe(folder, config, *, probe="stdlib"):
                events.append("probe:" + probe)
                self.assertTrue(config.production)
                self.assertEqual(config.budget, asdict(SearchBudget()))
                self.assertEqual(config.lean, worker.lean)
                self.assertEqual(config.lean_paths, [standard] if probe == "stdlib" else [compiled, standard])
                self.assertEqual(folder, output / ("smoke" if probe == "stdlib" else "project-export-probe"))
                return {"status": "ENVIRONMENT_ERROR" if failed_stage == probe else "PASS_INFRASTRUCTURE_SMOKE",
                        "authority": "MOCK_ORCHESTRATION_ONLY_NOT_NATIVE", "probe": probe}

            def environment(config, *, manifest_output):
                events.append("worker-environment")
                manifest_output.write_bytes(b"{}")
                return {"authority": "MOCK_ORCHESTRATION_ONLY_NOT_NATIVE"}

            def git(repo, *args):
                if args[0] == "status":
                    return ""
                return ("b" if args[-1] == "HEAD^{tree}" else "a") * 40

            resource = SimpleNamespace(RLIMIT_NOFILE=1, getrlimit=lambda _: (65536, 65536))
            with self.subTest(failed_preparation_stage=failed_stage), \
                    patch.object(qualification.platform, "system", return_value="Linux"), \
                    patch.object(qualification, "git", side_effect=git), \
                    patch.object(qualification, "_packages", return_value={"fixture": "a" * 40}), \
                    patch.object(qualification, "frozen_atlas", return_value=[{"module": "Fixture.Module"}]), \
                    patch.object(qualification, "_source", side_effect=source_scope), \
                    patch.object(qualification, "_materialize_pinned_benchmark_alias", return_value={"fixture": "NO_GIT_WRITE"}), \
                    patch.object(qualification, "discover_source_paths", return_value={"lean-toolchain"}), \
                    patch.object(qualification.shutil, "which", return_value=lake), \
                    patch.object(qualification, "_command", side_effect=command), \
                    patch.object(qualification, "_native_infrastructure_smoke", side_effect=probe), \
                    patch.object(qualification, "worker_environment", side_effect=environment), \
                    patch.dict(sys.modules, {"resource": resource}), \
                    patch.dict(os.environ, {"OPICA_NATIVE_OUTPUT": str(self.native)}), self.assertRaises(ContractError):
                qualification.prepare_native(self.repo, output)
            self.assertLess(events.index("source-preflight"), events.index("probe:stdlib"))
            if failed_stage == "stdlib":
                self.assertNotIn("selected-build", commands)
                self.assertNotIn("probe:project", events)
            else:
                self.assertEqual(commands["selected-build"],
                    ([lake, "build", *sorted(set(qualification.CORE_MODULES) | {"Fixture.Module"})], 7200))
                self.assertLess(events.index("probe:stdlib"), events.index("selected-build"))
                self.assertLess(events.index("selected-build"), events.index("worker-environment"))
                self.assertLess(events.index("worker-environment"), events.index("probe:project"))
                if failed_stage == "post-source":
                    self.assertLess(events.index("probe:project"), events.index("source-recheck"))
            self.assertEqual(json.loads((output / "result.json").read_bytes())["status"], "ENVIRONMENT_ERROR")
            self.assertFalse((output / "worker.json").exists())

    def assert_startup_diagnostic_boundaries(self):
        from research.RHRC.integration.opica_round4 import math_gate
        worker = self.smoke_worker()
        budget = SearchBudget(wall_seconds=6)
        tracer = self.root / "trusted-strace-fixture"
        tracer.write_bytes(b"trusted tracer fixture: never executed")
        real_unlinked = qualification.unlinked
        observations = {"scope": "MOCK_DIAGNOSTIC_COORDINATOR_HOST_AND_CGROUP", "errors": []}

        def run_case(name, mode, *, probe="stdlib"):
            config = self.smoke_worker(project=probe == "project")
            output = self.native / name
            output.mkdir()
            source = output / "OpicaInfrastructureSmoke.lean"
            source.write_bytes(self.PROBE_SOURCES[probe].encode("utf-8"))
            if mode == "source-drift":
                source.write_bytes(b"example : True := True.intro\n")
            completed = mode not in {"timeout", "output-limit", "cleanup-error"}
            proc = SimpleNamespace(pid=314159, returncode=0 if completed else None)
            proc.poll = Mock(side_effect=lambda: proc.returncode)

            def reaped(timeout):
                self.assertEqual(timeout, 1)
                proc.returncode = 0 if completed else -9
                return proc.returncode

            proc.wait = Mock(side_effect=reaped)
            proc.kill = Mock(side_effect=lambda: setattr(proc, "returncode", -9))
            raw_log = b"diagnostic fixture only\n"
            raw_trace = b"mmap(...) = -1 ENOMEM\n::error::untrusted-text\x1b[31m\n"
            if mode == "output-limit":
                raw_log = b"l" * qualification.SMOKE_DIAGNOSTIC_LOG_BYTES
                raw_trace = b"t" * (qualification.SMOKE_DIAGNOSTIC_TRACE_BYTES + 1)
            aliases = {}
            reparse = []
            optional = output / "diagnostic-only" / {"object-alias": "OpicaInfrastructureSmoke.olean",
                "object-reparse": "OpicaInfrastructureSmoke.olean.private",
                "object-nonregular": "OpicaInfrastructureSmoke.olean.server"}.get(mode, "unused")
            outside_object = self.root / (name + "-outside-object")
            if mode == "object-alias":
                outside_object.write_bytes(b"outside optional object must never be followed")
                if os.name == "nt":
                    aliases[optional] = str(outside_object)
            elif mode == "object-reparse":
                reparse.append(optional)

            def dispatch(command, **kwargs):
                self.assertEqual(kwargs["cwd"], output / "diagnostic-only")
                self.assertEqual(kwargs["env"], {})
                self.assertIs(kwargs["start_new_session"], True)
                self.assertEqual(kwargs["stderr"], subprocess.STDOUT)
                self.assertNotIn("shell", kwargs)
                kwargs["stdout"].write(raw_log)
                kwargs["stdout"].flush()
                (kwargs["cwd"] / "syscalls.trace").write_bytes(raw_trace)
                if mode == "object-alias":
                    if os.name == "nt":
                        optional.write_bytes(b"placeholder must not qualify")
                    else:
                        optional.symlink_to(outside_object)
                elif mode == "object-reparse":
                    optional.write_bytes(b"reparse placeholder must not qualify")
                elif mode == "object-nonregular":
                    if os.name == "nt":
                        optional.mkdir()
                    else:
                        os.mkfifo(optional)
                return proc

            def trusted_path(path):
                if str(path) == "/usr/bin/strace":
                    return tracer if mode != "unavailable" else self.root / "missing-strace"
                return real_unlinked(path)

            real_copy = math_gate._copy_regular

            def copy_fixed_source(original, destination):
                if mode == "copy-race":
                    original.write_bytes(b"stable changed source after initial hash\n")
                return real_copy(original, destination)

            clock_calls = [0]

            def clock():
                clock_calls[0] += 1
                return 0 if clock_calls[0] == 1 or mode not in {"timeout", "cleanup-error"} else 6

            stderr = io.StringIO()
            kill_error = OSError("fixture group kill unavailable") if mode == "cleanup-error" else None
            with leaf_links(aliases, reparse=reparse), \
                    patch.object(qualification, "unlinked", side_effect=trusted_path), \
                    patch.object(qualification, "_smoke_resource_snapshot", return_value=observations) as observe, \
                    patch.object(qualification.subprocess, "Popen", side_effect=dispatch) as popen, \
                    patch.object(math_gate, "_copy_regular", side_effect=copy_fixed_source), \
                    patch.object(qualification.time, "monotonic", side_effect=clock), \
                    patch.object(qualification.time, "sleep") as sleep, \
                    patch.object(qualification.os, "killpg", side_effect=kill_error, create=True) as killpg, \
                    patch.object(qualification.signal, "SIGKILL", 9, create=True), \
                    patch.dict(os.environ, {"OPICA_DIAGNOSTIC_SECRET": "fixture-only-never-inherited"}), \
                    redirect_stderr(stderr):
                report = qualification._failed_smoke_diagnostics(output, config, budget, probe=probe)
            observe.assert_has_calls([unittest.mock.call(), unittest.mock.call()])
            self.assertEqual(report["status"], "DIAGNOSTIC_ONLY")
            self.assertEqual(report["probe"], probe)
            self.assertEqual(report["authority"], "NO_ACCEPTANCE_OR_PROOF_AUTHORITY")
            self.assertIs(report["accepted"], False)
            self.assertEqual(report["maximum_seconds"], 6)
            self.assertEqual(report["trace_capture_bytes"], 262144)
            self.assertEqual(report["log_capture_bytes"], 65536)
            self.assertEqual(report["per_file_hard_bytes"], budget.output_bytes)
            self.assertEqual(report["poll_output_limit_bytes"], 327680)
            self.assertEqual(report["trace_file_count"], 1)
            self.assertEqual(report["before"], observations)
            self.assertEqual(report["after"], observations)
            self.assertNotIn("fixture-only-never-inherited", stderr.getvalue())
            self.assertEqual(len(stderr.getvalue().splitlines()), 1)
            self.assertTrue(stderr.getvalue().startswith("OPICA_FAILED_SMOKE_DIAGNOSTIC_ONLY\t"))
            self.assertNotIn("\x1b", stderr.getvalue())
            self.assertIs(json.loads(stderr.getvalue().split("\t", 1)[1])["accepted"], False)
            if mode in {"unavailable", "source-drift", "copy-race"}:
                self.assertEqual(report["disposition"], "UNAVAILABLE" if mode == "unavailable" else "ERROR")
                popen.assert_not_called()
                killpg.assert_not_called()
                self.assertNotIn("exit_code", report)
            else:
                original, env = executor._recipe(config, output / "diagnostic-only",
                    "OpicaInfrastructureSmoke.lean", "OpicaInfrastructureSmoke.olean", budget)
                position = original.index(config.lean)
                expected = original[:position] + [str(tracer), "-f", "-qq", "-yy", "-s", "128", "-e",
                    "trace=openat,read,lseek,brk,mmap,mprotect,munmap,clone,clone3,prlimit64",
                    "-e", "status=failed", "-o", "/out/syscalls.trace", "--"] + original[position:]
                self.assertEqual(popen.call_args.args[0], expected)
                self.assertEqual(report["command"], expected)
                self.assertEqual((output / "diagnostic-only" / source.name).read_bytes(), source.read_bytes())
                self.assertEqual(report["source_sha256"], sha256(self.PROBE_SOURCES[probe].encode("utf-8")))
                self.assertEqual(report["same_worker_budget"], budget.to_dict())
                self.assertEqual(env, {})
                if mode == "completed":
                    self.assertEqual(report["disposition"], "COMPLETED")
                    self.assertEqual(report["exit_code"], 0)
                    killpg.assert_not_called()
                    sleep.assert_not_called()
                elif mode == "cleanup-error":
                    self.assertEqual(report["disposition"], "ERROR")
                    self.assertGreaterEqual(killpg.call_count, 2)
                    proc.kill.assert_called_once()
                elif mode.startswith("object-"):
                    self.assertEqual(report["disposition"], "ERROR")
                    killpg.assert_not_called()
                    if mode == "object-alias":
                        self.assertEqual(outside_object.read_bytes(), b"outside optional object must never be followed")
                else:
                    self.assertEqual(report["disposition"], "TIMED_OUT" if mode == "timeout" else "OUTPUT_LIMIT")
                    killpg.assert_called_once_with(proc.pid, 9)
                proc.wait.assert_called_once_with(timeout=1)
                if mode != "cleanup-error":
                    for key, raw, limit in (("log", raw_log, 65536), ("trace", raw_trace, 262144)):
                        self.assertEqual(report[key]["captured_bytes"], min(len(raw), limit))
                        self.assertEqual(report[key]["file_bytes"], len(raw))
                        self.assertEqual(report[key]["text"].encode(), raw[-limit:])
                        self.assertEqual(report[key]["sha256"], sha256(raw))
                        self.assertEqual(report[key]["truncated"], len(raw) > limit)
                        self.assertEqual(report[key]["capture"], "TAIL")
            stored = json.loads((output / "diagnostic-only" / "result.json").read_bytes())
            self.assertEqual(stored["status"], "DIAGNOSTIC_ONLY")
            self.assertIs(stored["accepted"], False)
            return report

        for probe, text in self.PROBE_SOURCES.items():
            self.assertEqual(qualification._infrastructure_probe_source(probe), text)
        for mode in ("completed", "timeout", "output-limit", "cleanup-error", "unavailable", "source-drift", "copy-race",
                     "object-alias", "object-reparse", "object-nonregular"):
            with self.subTest(diagnostic_mode=mode):
                run_case("trace-" + mode, mode)
        run_case("trace-project-completed", "completed", probe="project")

        linked_output = self.native / "linked-diagnostic-directory"
        linked_output.mkdir()
        outside = self.root / "diagnostic-outside"
        outside.mkdir()
        sentinel = outside / "result.json"
        sentinel.write_bytes(b"outside bytes must stay unchanged")
        child = linked_output / "diagnostic-only"
        if os.name == "nt":
            child.mkdir()
            links = {child: str(outside)}
        else:
            child.symlink_to(outside, target_is_directory=True)
            links = {}
        with leaf_links(links), \
                patch.object(qualification, "_smoke_resource_snapshot", return_value=observations), \
                patch.object(qualification.subprocess, "Popen") as popen, redirect_stderr(io.StringIO()):
            report = qualification._failed_smoke_diagnostics(linked_output, worker, budget)
        self.assertEqual(report["disposition"], "ERROR")
        self.assertIs(report["accepted"], False)
        popen.assert_not_called()
        self.assertEqual(sentinel.read_bytes(), b"outside bytes must stay unchanged")

        # Capture uses actual regular bytes and refuses linked/reparse leaves.
        regular = self.native / "capture.log"
        raw = b"first bytes\nlast bytes\n"
        regular.write_bytes(raw)
        real_open = os.open
        with patch.object(qualification.os, "open", wraps=real_open) as opened:
            capture = qualification._smoke_diagnostic_capture(regular, 8)
        self.assertEqual(capture["text"].encode(), raw[-8:])
        self.assertEqual(capture["sha256"], sha256(raw))
        flags = opened.call_args.args[1]
        self.assertEqual(flags & getattr(os, "O_NOFOLLOW", 0), getattr(os, "O_NOFOLLOW", 0))
        self.assertEqual(flags & getattr(os, "O_NONBLOCK", 0), getattr(os, "O_NONBLOCK", 0))
        alias = self.native / "linked-capture.log"
        if os.name == "nt":
            alias.write_bytes(b"placeholder must not be read")
            links = {alias: str(regular)}
        else:
            alias.symlink_to(regular)
            links = {}
        with leaf_links(links), self.assertRaises(ContractError):
            qualification._smoke_diagnostic_capture(alias, 8)
        with leaf_links({}, reparse=[regular]), self.assertRaises(ContractError):
            qualification._smoke_diagnostic_capture(regular, 8)
        if os.name != "nt":
            fifo = self.native / "capture.fifo"
            os.mkfifo(fifo)
            with self.assertRaises(ContractError):
                qualification._smoke_diagnostic_capture(fifo, 8)

    def test_failed_lane_retains_partial_native_files_and_original_exception(self):
        batch = self.native / "atlas"
        batch.mkdir()
        files = {"atlas/batch.stdout.log": b"partial exact compiler output\nerror: diagnostic fixture\n",
                 "atlas/result.json": b'{"status":"ENVIRONMENT_ERROR"}\n',
                 "atlas/Driver.lean": b"example : True := True.intro\n"}
        for path, data in files.items():
            (self.native / path).write_bytes(data)
        primary = ContractError("primary native atlas batch failed")
        output = self.root / "failed-lane"
        with patch.dict(os.environ, {"OPICA_NATIVE_OUTPUT": str(self.native)}), \
                patch.object(cli, "_run_lane_impl", side_effect=primary), self.assertRaises(ContractError) as caught:
            cli.run_lane("CURRENT_COMPATIBILITY", self.repo, output, {})
        self.assertIs(caught.exception, primary)
        report = json.loads((output / "failure-diagnostics" / "index.json").read_bytes())
        self.assertEqual(report["authority"], "DIAGNOSTIC_ONLY_NOT_ACCEPTANCE")
        self.assertEqual({row["path"] for row in report["files"]}, {"native/" + path for path in files})
        for row in report["files"]:
            retained = output / "failure-diagnostics" / row["path"]
            self.assertEqual(retained.read_bytes(), files[row["path"].removeprefix("native/")])
            self.assertEqual(sha256(retained.read_bytes()), row["sha256"])
        self.assertFalse((output / "lane.json").exists())
        self.assertFalse((output / "results.json").exists())
        stderr = io.StringIO()
        with patch.object(cli, "_run_lane_impl", side_effect=primary), \
                patch.object(cli, "_collect_failed_native_diagnostics", side_effect=RuntimeError("secondary failure")), \
                redirect_stderr(stderr), self.assertRaises(ContractError) as caught:
            cli.run_lane("CURRENT_COMPATIBILITY", self.repo, self.root / "collector-failed", {})
        self.assertIs(caught.exception, primary)
        self.assertIn("OPICA_DIAGNOSTIC_ONLY_COLLECTION_FAILED", stderr.getvalue())
        with patch.object(cli, "_run_lane_impl", side_effect=primary), \
                patch.object(cli, "_collect_failed_native_diagnostics", side_effect=RuntimeError("secondary failure")), \
                patch.object(cli.sys, "stderr", None), self.assertRaises(ContractError) as caught:
            cli.run_lane("CURRENT_COMPATIBILITY", self.repo, self.root / "stderr-unavailable", {})
        self.assertIs(caught.exception, primary)

        # A diagnostic replay reporting exit0 must never replace the failed
        # actual worker, including a resource-exhausted worker that left output.
        worker = self.smoke_worker()
        diagnostic = {"schema": "OPICA_FAILED_SMOKE_DIAGNOSTIC_V1", "status": "DIAGNOSTIC_ONLY",
                      "disposition": "COMPLETED", "authority": "NO_ACCEPTANCE_OR_PROOF_AUTHORITY",
                      "accepted": False, "exit_code": 0}
        for index, (code, resource) in enumerate(((1, None), (0, "RESOURCE_EXHAUSTED"))):
            with self.subTest(actual_exit=code, resource=resource):
                native = {"exit_code": code, "resource_status": resource, "capability": "LINUX_ISOLATED"}

                def failed_actual(config, output, source, obj, budget):
                    self.assertEqual(config, worker)
                    (output / (source + ".log")).write_bytes(b"failed to create thread\n")
                    if code == 0:
                        (output / obj).write_bytes(b"incomplete fixture output")
                    return native

                output = self.native / ("failed-smoke-" + str(index))
                with patch.object(qualification, "run_worker", side_effect=failed_actual), \
                        patch.object(qualification, "_failed_smoke_diagnostics", return_value=diagnostic) as trace:
                    report = qualification._native_infrastructure_smoke(output, worker)
                trace.assert_called_once()
                self.assertEqual(trace.call_args.args[:2], (output, worker))
                self.assertEqual(trace.call_args.args[2], SearchBudget())
                self.assertEqual(trace.call_args.kwargs, {"probe": "stdlib"})
                self.assertEqual(report["status"], "ENVIRONMENT_ERROR")
                self.assertIs(report["native"], native)
                self.assertEqual(report["diagnostics"], diagnostic)
                self.assertNotIn("object_sha256", report)
                stored = json.loads((output / "result.json").read_bytes())
                self.assertEqual(stored["status"], "ENVIRONMENT_ERROR")
                self.assertEqual(stored["native"]["exit_code"], code)
                self.assertEqual(stored["native"]["resource_status"], resource)
        for disposition in ("UNAVAILABLE", "ERROR"):
            with self.subTest(optional_diagnostic=disposition):
                native = {"exit_code": 1, "resource_status": None, "capability": "LINUX_ISOLATED"}
                unavailable = {"status": "DIAGNOSTIC_ONLY", "disposition": "UNAVAILABLE", "accepted": False}
                output = self.native / ("optional-smoke-" + disposition.lower())
                with patch.object(qualification, "run_worker", return_value=native), \
                        patch.object(qualification, "_failed_smoke_diagnostics", return_value=unavailable,
                                     side_effect=OSError("diagnostic fixture unavailable") if disposition == "ERROR" else None):
                    report = qualification._native_infrastructure_smoke(output, worker)
                self.assertEqual(report["status"], "ENVIRONMENT_ERROR")
                self.assertIs(report["native"], native)
                self.assertEqual(report["diagnostics"]["disposition"], disposition)
                self.assertIs(report["diagnostics"]["accepted"], False)
                self.assertNotIn("object_sha256", report)

        # A raised worker call has no returned execution receipt. Observe the
        # boundary, preserve the identical exception, and never replay guards.
        failures = (OSError("launch fixture: " + "x" * 5000),
                    ContractError("namespace/cgroup fixture refused before dispatch"),
                    subprocess.SubprocessError("process launch fixture failed"))
        for index, primary in enumerate(failures):
            original_args = primary.args
            for diagnostic_failure in (False, True):
                with self.subTest(raised_worker=type(primary).__name__, diagnostic_failure=diagnostic_failure):
                    output = self.native / ("raised-smoke-" + str(index) + "-" + str(diagnostic_failure))
                    observations = [{"scope": "MOCK_BEFORE_WORKER"}, {"scope": "MOCK_AFTER_WORKER"}]
                    with patch.object(qualification, "run_worker", side_effect=primary) as actual, \
                            patch.object(qualification, "_smoke_resource_snapshot", side_effect=observations) as observe, \
                            patch.object(qualification, "_failed_smoke_diagnostics") as replay, \
                            patch.object(qualification, "_raised_smoke_diagnostics", wraps=qualification._raised_smoke_diagnostics,
                                side_effect=RuntimeError("optional diagnostic fixture failed") if diagnostic_failure else None) as disposition, \
                            self.assertRaises(type(primary)) as caught:
                        qualification._native_infrastructure_smoke(output, worker)
                    self.assertIs(caught.exception, primary)
                    self.assertEqual(primary.args, original_args)
                    actual.assert_called_once()
                    observe.assert_has_calls([unittest.mock.call(), unittest.mock.call()])
                    self.assertEqual(observe.call_count, 2)
                    disposition.assert_called_once_with(primary)
                    replay.assert_not_called()
                    stored = json.loads((output / "result.json").read_bytes())
                    self.assertEqual(stored["status"], "ENVIRONMENT_ERROR")
                    self.assertIsNone(stored["native"])
                    self.assertEqual(stored["resource_observations"], {
                        "authority": "DIAGNOSTIC_ONLY", "before": observations[0], "after": observations[1]})
                    boundary = stored["diagnostics"]
                    self.assertEqual(boundary["status"], "DIAGNOSTIC_ONLY")
                    self.assertEqual(boundary["authority"], "NO_ACCEPTANCE_OR_PROOF_AUTHORITY")
                    self.assertIs(boundary["accepted"], False)
                    self.assertIs(boundary["replay_attempted"], False)
                    self.assertEqual(boundary["execution_boundary"], "NO_RETURNED_NATIVE_RECEIPT")
                    self.assertEqual(boundary["compiler_reached"], "NOT_ESTABLISHED")
                    self.assertFalse({"command", "exit_code", "trace", "object_sha256"} & set(boundary))
                    if diagnostic_failure:
                        self.assertEqual(boundary["disposition"], "ERROR")
                    else:
                        self.assertEqual(boundary["disposition"], "NOT_REPLAYED_WORKER_EXCEPTION")
                        self.assertEqual(boundary["exception_type"], type(primary).__name__)
                        self.assertEqual(boundary["maximum_exception_message_characters"], 4096)
                        self.assertEqual(boundary["exception_message"], str(primary)[:4096])
                        self.assertEqual(boundary["exception_message_truncated"], len(str(primary)) > 4096)
                    self.assertFalse((output / "diagnostic-only").exists())

        primary = OSError("primary worker fixture survives observation failure")
        output = self.native / "raised-smoke-snapshot-error"
        with patch.object(qualification, "run_worker", side_effect=primary), \
                patch.object(qualification, "_smoke_resource_snapshot", side_effect=RuntimeError("optional snapshot failed")), \
                patch.object(qualification, "_failed_smoke_diagnostics") as replay, self.assertRaises(OSError) as caught:
            qualification._native_infrastructure_smoke(output, worker)
        self.assertIs(caught.exception, primary)
        replay.assert_not_called()
        stored = json.loads((output / "result.json").read_bytes())
        self.assertEqual(stored["status"], "ENVIRONMENT_ERROR")
        for phase in ("before", "after"):
            self.assertEqual(stored["resource_observations"][phase]["errors"],
                             ["RESOURCE_SNAPSHOT_UNAVAILABLE:RuntimeError"])
        with patch.object(qualification, "run_worker", side_effect=primary), \
                patch.object(qualification, "_smoke_resource_snapshot", return_value={"scope": "MOCK"}), \
                patch.object(qualification.Path, "write_bytes", side_effect=OSError("secondary report write failed")), \
                patch.object(qualification, "_failed_smoke_diagnostics") as replay, self.assertRaises(OSError) as caught:
            qualification._native_infrastructure_smoke(self.native / "raised-smoke-result-write-error", worker)
        self.assertIs(caught.exception, primary)
        replay.assert_not_called()

    def test_failure_collection_refuses_links_and_records_all_boundaries(self):
        (self.native / "a-good.log").write_bytes(b"abc")
        (self.native / "b-extra.log").write_bytes(b"def")
        (self.native / "c-oversize.log").write_bytes(b"x" * 10)
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "secret.log").write_bytes(b"must never be copied")
        leaf = self.native / "d-linked.log"
        directory = self.native / "e-linked-directory"
        reparse = self.native / "f-reparse-directory"
        reparse.mkdir()
        (reparse / "secret.log").write_bytes(b"must never be copied")
        if os.name == "nt":
            leaf.write_bytes(b"must never be copied")
            directory.mkdir()
            (directory / "secret.log").write_bytes(b"must never be copied")
            links = {leaf: str(outside / "secret.log"), directory: str(outside)}
        else:
            leaf.symlink_to(outside / "secret.log")
            directory.symlink_to(outside, target_is_directory=True)
            links = {}
        with leaf_links(links, reparse=[reparse]), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_FILES", 1), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_FILE_BYTES", 8), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES", 4), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_OMISSIONS", 2):
            output, report = self.collect("bounded-files")
        self.assertEqual(report["retained_bytes"], 3)
        self.assertEqual([row["path"] for row in report["files"]], ["native/a-good.log"])
        self.assertEqual(report["omission_counts"]["LINK_OR_REPARSE_REFUSED"], 3)
        self.assertEqual(report["omission_counts"]["PER_FILE_LIMIT"], 1)
        self.assertEqual(report["omission_counts"]["FILE_COUNT_LIMIT"], 1)
        self.assertTrue(report["omissions_truncated"])
        self.assertEqual(len(report["omissions"]), 2)
        self.assertEqual((output / "failure-diagnostics" / "native" / "a-good.log").read_bytes(), b"abc")
        with leaf_links(links, reparse=[reparse]), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_FILES", 10), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_FILE_BYTES", 8), \
                patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_TOTAL_BYTES", 4):
            _, report = self.collect("bounded-bytes")
        self.assertEqual(report["omission_counts"]["TOTAL_BYTES_LIMIT"], 1)
        with leaf_links(links, reparse=[reparse]), patch.object(cli, "FAILURE_DIAGNOSTIC_MAX_ENTRIES", 1):
            _, report = self.collect("bounded-traversal")
        self.assertTrue(report["traversal_truncated"])
        self.assertEqual(report["omission_counts"]["TRAVERSAL_LIMIT"], 1)
        self.assert_startup_diagnostic_boundaries()

    def test_failure_dump_cannot_qualify_a_lane_or_change_success_behavior(self):
        (self.native / "lane.json").write_bytes(b'{"conclusion":"success"}')
        (self.native / "partial.log").write_bytes(b"actual partial output")
        output, report = self.collect("diagnostic-only")
        self.assertEqual(report["omission_counts"]["ACCEPTANCE_RECORD_REFUSED"], 1)
        self.assertFalse((output / "lane.json").exists())
        with self.assertRaises((FileNotFoundError, ContractError)):
            verify_lane_bundle({"id": "CURRENT_COMPATIBILITY"}, output, experiment={}, replay=lambda *_: True)
        record = {"conclusion": "success", "sentinel": "unchanged implementation return"}
        with patch.object(cli, "_run_lane_impl", return_value=record), \
                patch.object(cli, "_collect_failed_native_diagnostics") as collector:
            actual = cli.run_lane("CURRENT_COMPATIBILITY", self.repo, self.root / "success", {})
        self.assertIs(actual, record)
        collector.assert_not_called()
        self.assertFalse((self.root / "success" / "failure-diagnostics").exists())
        with patch.object(cli, "_run_lane_impl") as implementation, self.assertRaises(ContractError):
            cli.run_lane("CURRENT_COMPATIBILITY", self.repo, self.repo / "forbidden-output", {})
        implementation.assert_not_called()
        self.assertFalse((self.repo / "forbidden-output").exists())
        unsafe_output = self.root / "unsafe-native-location"
        unsafe_output.mkdir()
        for native in (self.repo, unsafe_output):
            with self.subTest(native=native), patch.dict(os.environ, {"OPICA_NATIVE_OUTPUT": str(native)}), \
                    self.assertRaises(ContractError):
                cli._collect_failed_native_diagnostics("CURRENT_COMPATIBILITY", self.repo, unsafe_output)
        self.assertFalse((unsafe_output / "failure-diagnostics").exists())

        # A mocked successful worker is used only to check dispatch policy;
        # this fixture does not supply a native qualification receipt.
        expression = {"format": "LEAN_EXPR_DAG_V1", "nodes": [["const", ["str", ["anonymous"], "True"], []]], "root": "0"}
        target_row = b"OPICA_TARGET\t" + json.dumps(expression).encode() + b"\n"
        direct_budget = SearchBudget(heartbeats=314159, wall_seconds=17, output_bytes=512345)
        for probe in ("stdlib", "project"):
            worker = replace(self.smoke_worker(project=probe == "project"), budget=asdict(direct_budget))

            def successful_actual(config, output, source, obj, budget):
                self.assertEqual(config, worker)
                self.assertEqual(budget, direct_budget)
                self.assertEqual(source, "OpicaInfrastructureSmoke.lean")
                self.assertEqual(obj, "OpicaInfrastructureSmoke.olean")
                self.assertEqual((output / source).read_bytes(), self.PROBE_SOURCES[probe].encode("utf-8"))
                (output / obj).write_bytes(b"mock compiler object")
                (output / (source + ".log")).write_bytes(target_row if probe == "project" else b"")
                return {"exit_code": 0, "resource_status": None, "capability": "LINUX_ISOLATED"}

            with self.subTest(success_probe=probe), patch.object(qualification, "run_worker", side_effect=successful_actual), \
                    patch.object(qualification, "_failed_smoke_diagnostics") as trace:
                report = qualification._native_infrastructure_smoke(self.native / ("mock-success-" + probe), worker, probe=probe)
            self.assertEqual(report["status"], "PASS_INFRASTRUCTURE_SMOKE")
            self.assertEqual(report["authority"], "INFRASTRUCTURE_ONLY_NO_RH_AUTHORITY")
            self.assertEqual(report["probe"], probe)
            self.assertEqual(report["source_sha256"], sha256(self.PROBE_SOURCES[probe].encode("utf-8")))
            if probe == "project":
                self.assertEqual(report["target_type_expression_sha256"], qualification.expression_hash(expression))
            trace.assert_not_called()
            self.assertNotIn("diagnostics", report)

        worker = self.smoke_worker(project=True)
        native = {"exit_code": 1, "resource_status": None, "capability": "LINUX_ISOLATED"}
        diagnostic = {"status": "DIAGNOSTIC_ONLY", "accepted": False, "disposition": "COMPLETED", "exit_code": 0}
        with patch.object(qualification, "run_worker", return_value=native), \
                patch.object(qualification, "_failed_smoke_diagnostics", return_value=diagnostic) as trace:
            report = qualification._native_infrastructure_smoke(self.native / "project-returned-error", worker, probe="project")
        self.assertEqual(report["status"], "ENVIRONMENT_ERROR")
        self.assertIs(report["native"], native)
        self.assertEqual(trace.call_args.kwargs, {"probe": "project"})
        self.assertNotIn("target_type_expression_sha256", report)

        for index, raw in enumerate((b"", target_row + target_row)):
            output = self.native / ("project-invalid-export-" + str(index))

            def invalid_export(config, folder, source, obj, budget):
                (folder / obj).write_bytes(b"mock compiler object without one complete export")
                (folder / (source + ".log")).write_bytes(raw)
                return {"exit_code": 0, "resource_status": None, "capability": "LINUX_ISOLATED"}

            with patch.object(qualification, "run_worker", side_effect=invalid_export), \
                    patch.object(qualification, "_failed_smoke_diagnostics") as trace, self.assertRaises(ContractError):
                qualification._native_infrastructure_smoke(output, worker, probe="project")
            trace.assert_not_called()
            self.assertEqual(json.loads((output / "result.json").read_bytes())["status"], "ENVIRONMENT_ERROR")

        for index, selector in enumerate(("unknown", "../project", None, {})):
            output = self.native / ("unknown-profile-" + str(index))
            with self.subTest(selector=selector), patch.object(qualification, "run_worker") as actual, \
                    patch.object(qualification.subprocess, "Popen") as trace, self.assertRaises(ContractError):
                qualification._native_infrastructure_smoke(output, worker, probe=selector)
            actual.assert_not_called()
            trace.assert_not_called()
            self.assertFalse(output.exists())
            with patch.object(qualification.subprocess, "Popen") as trace, self.assertRaises(ContractError):
                qualification._failed_smoke_diagnostics(output, worker, SearchBudget(), probe=selector)
            trace.assert_not_called()
            self.assertFalse(output.exists())
        for probe, config in (("stdlib", worker), ("project", self.smoke_worker())):
            output = self.native / ("wrong-import-profile-" + probe)
            with self.subTest(wrong_import_profile=probe), patch.object(qualification, "run_worker") as actual, \
                    self.assertRaises(ContractError):
                qualification._native_infrastructure_smoke(output, config, probe=probe)
            actual.assert_not_called()
            self.assertFalse(output.exists())
        export = Path(worker.lean_paths[0]) / "Zeta23/RHRC/OpicaComposition/Export.olean"
        export.unlink()
        output = self.native / "missing-fixed-project-exporter"
        with patch.object(qualification, "run_worker") as actual, self.assertRaises(ContractError):
            qualification._native_infrastructure_smoke(output, worker, probe="project")
        actual.assert_not_called()
        self.assertFalse(output.exists())
        self.assert_probe_preparation_order()


if __name__ == "__main__":
    unittest.main()
