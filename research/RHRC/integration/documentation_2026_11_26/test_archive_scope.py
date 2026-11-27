from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from . import archive_scope as scope


class ArchiveScopeTests(unittest.TestCase):
    def setUp(self):
        self.repo_dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.repo_dir.cleanup)
        self.repo = Path(self.repo_dir.name)
        scope.git(self.repo, "init", "--quiet")
        scope.git(self.repo, "config", "user.name", "Paper scope test")
        scope.git(self.repo, "config", "user.email", "paper-scope@example.invalid")
        (self.repo / "historical").mkdir()
        (self.repo / "historical" / "historical.pdf").write_bytes(b"%PDF-1.7\nHistorical source\xff\n")
        self.commit("Historical research archive")
        self.base = self.rev()
        self.base_tree = self.rev("HEAD^{tree}")
        self.directory = self.repo / scope.PAPER_PREFIX
        self.directory.mkdir(parents=True)
        for i in range(1, 7):
            (self.directory / f"paper-{i}.pdf").write_bytes(b"%PDF-1.7\n\xff binary document " + bytes([i]))
        (self.directory / "README.md").write_bytes(b"# Reader guide\n")
        (self.directory / "paper-7.md").write_bytes(b"# Closing argument\n")
        files = []
        for path in sorted(self.directory.glob("*.pdf")):
            row = self.file_row(path)
            files.append({"path": path.relative_to(self.repo).as_posix(),
                          "git_blob_sha1": row["git_blob"], "size_bytes": row["size_bytes"],
                          "sha256": row["sha256"]})
        manifest = {"files": files, "total_pdf_files": len(files),
                    "total_pdf_bytes": sum(row["size_bytes"] for row in files),
                    "new_manuscript": {"path": scope.PAPER_PREFIX + "paper-7.md"}}
        (self.directory / "MANIFEST.json").write_bytes(json.dumps(manifest).encode("ascii"))
        self.commit("Archive six PDFs and Paper XXXIII")
        self.archive = self.rev()
        self.policy = {"base_commit": self.base, "base_tree": self.base_tree,
                       "archive_commit": self.archive, "archive_tree": self.rev("HEAD^{tree}"),
                       "added": {p.relative_to(self.repo).as_posix(): self.file_row(p)
                                 for p in self.directory.iterdir()}}

    def commit(self, title):
        scope.git(self.repo, "add", "--all")
        scope.git(self.repo, "commit", "--quiet", "-m", title)

    def rev(self, what="HEAD"):
        return scope.git(self.repo, "rev-parse", what).decode("ascii").strip()

    def file_row(self, path):
        data = path.read_bytes()
        return {"git_blob": scope.git(self.repo, "hash-object", "--no-filters", str(path)).decode().strip(),
                "size_bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
                "file_kind": "BINARY_PDF" if path.suffix == ".pdf" else "TEXT"}

    def test_inspection_reports_binary_archive_without_proof_authority(self):
        result = scope.inspect_archive(self.repo, self.policy)
        self.assertEqual(result["status"], "PASS_ARCHIVE_BYTES_ONLY")
        self.assertEqual(result["archive_commit"], self.archive)
        self.assertEqual(result["article_pdf_count"], 6)
        self.assertFalse(result["proof_acceptance"])

    def test_does_not_substitute_current_working_bytes(self):
        (self.directory / "paper-1.pdf").write_bytes(b"changed working tree only")
        result = scope.inspect_archive(self.repo, self.policy)
        self.assertEqual(result["archive_commit"], self.archive)

    def test_rejects_wrong_predecessor_tree(self):
        self.policy["base_tree"] = self.policy["archive_tree"]
        with self.assertRaisesRegex(scope.ArchiveError, "Unexpected tree"):
            scope.inspect_archive(self.repo, self.policy)

    def test_rejects_unreviewed_added_path(self):
        base = scope.tree(self.repo, self.base)
        archive = scope.tree(self.repo, self.archive)
        archive["foreign.lean"] = archive[scope.PAPER_PREFIX + "README.md"]
        with self.assertRaisesRegex(scope.ArchiveError, "Unexpected archive delta"):
            scope.check_delta(base, archive, self.policy["added"])

    def test_rejects_inherited_archive_edit_and_deletion(self):
        base = scope.tree(self.repo, self.base)
        archive = scope.tree(self.repo, self.archive)
        prior = "historical/historical.pdf"
        with self.assertRaisesRegex(scope.ArchiveError, "edited inherited paths"):
            scope.check_delta(base, {**archive, prior: archive[scope.PAPER_PREFIX + "README.md"]},
                              self.policy["added"])
        del archive[prior]
        with self.assertRaisesRegex(scope.ArchiveError, "removed an inherited path"):
            scope.check_delta(base, archive, self.policy["added"])

    def test_rejects_blob_mode_and_sha256_substitutions(self):
        base = scope.tree(self.repo, self.base)
        archive = scope.tree(self.repo, self.archive)
        path = scope.PAPER_PREFIX + "paper-1.pdf"
        bad_mode = ("120000", "blob", self.policy["added"][path]["git_blob"])
        with self.assertRaisesRegex(scope.ArchiveError, "mode or Git blob differs"):
            scope.check_delta(base, {**archive, path: bad_mode}, self.policy["added"])
        self.policy["added"][path]["sha256"] = "0" * 64
        with self.assertRaisesRegex(scope.ArchiveError, "SHA-256 differs"):
            scope.inspect_archive(self.repo, self.policy)

    def test_policy_is_content_pinned(self):
        path = self.repo / "substitution.json"
        path.write_bytes(scope.ARCHIVE_POLICY.read_bytes() + b"\n")
        with patch.object(scope, "ARCHIVE_POLICY", path):
            with self.assertRaisesRegex(scope.ArchiveError, "policy bytes differ"):
                scope.read_policy()


if __name__ == "__main__":
    unittest.main()
