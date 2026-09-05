import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.retro.aliases import expanded_terms, load_alias_map
from control_v2.retro.archive import ArchiveManifestError
from control_v2.retro.ingest import ingest_text_source
from control_v2.retro.replay import assert_receipt_as_of, replay_concept
from control_v2.retro.search import search_concept


class RetroTests(unittest.TestCase):
    def _git(self, repo: Path, *args: str) -> str:
        proc = subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True, text=True)
        return proc.stdout.strip()

    def _fixture_repo(self) -> tuple[tempfile.TemporaryDirectory, Path, str, str]:
        td = tempfile.TemporaryDirectory()
        repo = Path(td.name)
        self._git(repo, "init")
        self._git(repo, "config", "user.email", "test@example.com")
        self._git(repo, "config", "user.name", "RHRC Test")
        (repo / "research" / "RHRC").mkdir(parents=True)
        p = repo / "research" / "RHRC" / "old.md"
        p.write_text("residual headroom appears here\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(repo, "commit", "-m", "old clue")
        old = self._git(repo, "rev-parse", "HEAD")
        p.write_text("residual headroom appears here\nfuture resonance clue\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(repo, "commit", "-m", "future clue")
        new = self._git(repo, "rev-parse", "HEAD")
        return td, repo, old, new

    def test_aliases_recover_old_vocabulary(self):
        aliases = load_alias_map(RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        terms = expanded_terms("deformation_budget", aliases)
        self.assertIn("residual headroom", terms)
        self.assertIn("detectability budget", terms)

    def test_as_of_search_does_not_see_future_commit(self):
        td, repo, old, new = self._fixture_repo()
        self.addCleanup(td.cleanup)
        receipt = search_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old,
                                 aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
                                 mode="COUNTERFACTUAL_REPLAY")
        assert_receipt_as_of(repo, receipt)
        self.assertEqual(receipt.search_scope, "ANCHOR_REACHABLE_ONLY")
        self.assertTrue(all(hit.source_commit != new for hit in receipt.hits if hit.source_commit))
        self.assertTrue(any("residual headroom" in hit.excerpt for hit in receipt.hits))

    def test_archaeology_searches_unmerged_historical_branch(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        self._git(repo, "checkout", "-b", "old-unmerged", old)
        branch_file = repo / "research" / "RHRC" / "branch.md"
        branch_file.write_text("detectability budget branch clue\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(repo, "commit", "-m", "unmerged historical clue")
        branch_commit = self._git(repo, "rev-parse", "HEAD")
        # Anchor after the branch commit so the archaeology time cutoff admits it.
        self._git(repo, "checkout", "master")
        anchor = self._git(repo, "rev-parse", "HEAD")
        receipt = search_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=anchor,
                                 aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        self.assertEqual(receipt.search_scope, "ALL_REFS_BEFORE_ANCHOR")
        self.assertTrue(any(hit.source_commit == branch_commit for hit in receipt.hits))

    def test_counterfactual_replay_enforces_anchor(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        receipt = replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old)
        self.assertEqual(receipt.mode, "COUNTERFACTUAL_REPLAY")
        assert_receipt_as_of(repo, receipt)

    def test_receipt_hash_is_deterministic(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        kwargs = dict(repo_root=repo, concept_id="deformation_budget", as_of_ref=old,
                      aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
                      mode="COUNTERFACTUAL_REPLAY")
        a = search_concept(**kwargs)
        b = search_concept(**kwargs)
        self.assertEqual(a.receipt_id, b.receipt_id)
        self.assertTrue(a.search_complete)

    def test_external_counterfactual_requires_manifest(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        with tempfile.TemporaryDirectory() as archive_dir:
            archive = Path(archive_dir)
            (archive / "old.txt").write_text("residual headroom\n", encoding="utf-8")
            with self.assertRaises(ArchiveManifestError):
                replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old, archive_root=archive)

    def test_external_counterfactual_excludes_future_source_and_checks_hash(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        with tempfile.TemporaryDirectory() as archive_dir:
            archive = Path(archive_dir)
            old_file = archive / "old.txt"
            future_file = archive / "future.txt"
            old_file.write_text("residual headroom old\n", encoding="utf-8")
            future_file.write_text("residual headroom future\n", encoding="utf-8")
            manifest = {
                "sources": [
                    {"path": "old.txt", "available_from_utc": "2000-01-01T00:00:00Z", "sha256": hashlib.sha256(old_file.read_bytes()).hexdigest()},
                    {"path": "future.txt", "available_from_utc": "2099-01-01T00:00:00Z", "sha256": hashlib.sha256(future_file.read_bytes()).hexdigest()}
                ]
            }
            (archive / "RETRO_ARCHIVE_MANIFEST.json").write_text(json.dumps(manifest), encoding="utf-8")
            receipt = replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old, archive_root=archive)
            paths = {hit.source_path for hit in receipt.hits if hit.source_commit is None}
            self.assertIn("old.txt", paths)
            self.assertNotIn("future.txt", paths)

    def test_ingest_builds_hash_bound_manifest(self):
        with tempfile.TemporaryDirectory() as td, tempfile.TemporaryDirectory() as ad:
            source = Path(td) / "ICW.txt"
            source.write_text("residual headroom\n", encoding="utf-8")
            entry = ingest_text_source(
                source=source,
                archive_root=Path(ad),
                source_family="ICW_NSG",
                source_version="1.0",
                authority="HISTORICAL_ARCHITECTURE",
                available_from_utc="2026-08-01T00:00:00Z",
            )
            self.assertEqual(entry["sha256"], hashlib.sha256(source.read_bytes()).hexdigest())
            manifest = json.loads((Path(ad) / "RETRO_ARCHIVE_MANIFEST.json").read_text())
            self.assertEqual(len(manifest["sources"]), 1)


if __name__ == "__main__":
    unittest.main()
