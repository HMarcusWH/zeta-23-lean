"""Portable regressions for pinned toolchain aliases and environment identity.

These are filesystem/identity tests, not native compiler qualification. Real
temporary files supply the bytes. Only leaf lstat/readlink results model Linux
symlinks, so Windows hosts need no symlink creation privilege. The compiler
version subprocess is fixed test data and never supplies proof authority.
Pinned benchmark projection tests use real Git objects and checkout commands;
Linux tests create actual symlinks rather than skipping their conversion.
"""
from contextlib import contextmanager, redirect_stderr
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_composition import cli, executor, qualification, snapshot
from research.RHRC.integration.opica_composition.accept import verify_lane_bundle
from research.RHRC.integration.opica_composition.canonical import ContractError
from research.RHRC.integration.opica_composition.contracts import WorkerConfig


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


if __name__ == "__main__":
    unittest.main()
