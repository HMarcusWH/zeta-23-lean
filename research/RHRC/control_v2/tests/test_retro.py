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
                                 aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        assert_receipt_as_of(repo, receipt)
        self.assertTrue(all(hit.source_commit != new for hit in receipt.hits if hit.source_commit))
        self.assertTrue(any("residual headroom" in hit.excerpt for hit in receipt.hits))

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
                      aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        a = search_concept(**kwargs)
        b = search_concept(**kwargs)
        self.assertEqual(a.receipt_id, b.receipt_id)

    def test_external_counterfactual_requires_manifest(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        with tempfile.TemporaryDirectory() as archive_dir:
            archive = Path(archive_dir)
            (archive / "old.txt").write_text("residual headroom\n", encoding="utf-8")
            with self.assertRaises(ArchiveManifestError):
                replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old, archive_root=archive)

    def test_external_counterfactual_excludes_future_source(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        with tempfile.TemporaryDirectory() as archive_dir:
            archive = Path(archive_dir)
            (archive / "old.txt").write_text("residual headroom old\n", encoding="utf-8")
            (archive / "future.txt").write_text("residual headroom future\n", encoding="utf-8")
            manifest = {
                "sources": [
                    {"path": "old.txt", "available_from_utc": "2000-01-01T00:00:00Z"},
                    {"path": "future.txt", "available_from_utc": "2099-01-01T00:00:00Z"}
                ]
            }
            (archive / "RETRO_ARCHIVE_MANIFEST.json").write_text(json.dumps(manifest), encoding="utf-8")
            receipt = replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old, archive_root=archive)
            paths = {hit.source_path for hit in receipt.hits if hit.source_commit is None}
            self.assertIn("old.txt", paths)
            self.assertNotIn("future.txt", paths)


if __name__ == "__main__":
    unittest.main()
