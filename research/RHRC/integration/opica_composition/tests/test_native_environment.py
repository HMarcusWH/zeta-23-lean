"""Portable regressions for pinned toolchain aliases and environment identity.

These are filesystem/identity tests, not native compiler qualification. Real
temporary files supply the bytes. Only leaf lstat/readlink results model Linux
symlinks, so Windows hosts need no symlink creation privilege. The compiler
version subprocess is fixed test data and never supplies proof authority.
"""
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from research.RHRC.integration.opica_composition import executor, snapshot
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


if __name__ == "__main__":
    unittest.main()
