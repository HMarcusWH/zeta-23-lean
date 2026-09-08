import hashlib
import json
import os
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
from control_v2.retro.search import DEFAULT_GIT_SEARCH_PATHS, search_concept


class RetroTests(unittest.TestCase):
    def _git(self, repo: Path, *args: str, commit_date: str | None = None) -> str:
        env = os.environ.copy()
        if commit_date is not None:
            env.update(GIT_AUTHOR_DATE=commit_date, GIT_COMMITTER_DATE=commit_date)
        proc = subprocess.run(
            ["git", *args], cwd=repo, env=env, check=True, capture_output=True, text=True
        )
        return proc.stdout.strip()

    def _fixture_repo(self) -> tuple[tempfile.TemporaryDirectory, Path, str, str]:
        td = tempfile.TemporaryDirectory()
        repo = Path(td.name)
        self._git(repo, "init", "--initial-branch=main")
        self._git(repo, "config", "user.email", "test@example.com")
        self._git(repo, "config", "user.name", "RHRC Test")
        (repo / "research" / "RHRC").mkdir(parents=True)
        p = repo / "research" / "RHRC" / "old.md"
        p.write_text("residual headroom appears here\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(repo, "commit", "-m", "old clue", commit_date="2001-01-01T00:00:00Z")
        old = self._git(repo, "rev-parse", "HEAD")
        p.write_text("residual headroom appears here\nfuture resonance clue\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(repo, "commit", "-m", "future clue", commit_date="2001-01-03T00:00:00Z")
        new = self._git(repo, "rev-parse", "HEAD")
        return td, repo, old, new

    def test_aliases_recover_old_vocabulary_without_generic_noise(self):
        aliases = load_alias_map(RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        terms = expanded_terms("deformation_budget", aliases)
        self.assertIn("residual headroom", terms)
        self.assertIn("detectability budget", terms)
        self.assertNotIn("fold", terms)
        self.assertNotIn("rupture", terms)
        self.assertNotIn("slack", terms)

    def test_e4a4_source_actions_use_source_specific_archaeology_aliases(self):
        aliases = load_alias_map(RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json")
        terms = expanded_terms("canonical_source_exclusion", aliases)
        for term in (
            "canonicalSourceMatrix",
            "evenQuadraticSourceMoment",
            "centeredQuadraticNormal",
            "source normalization",
            "prime contribution",
            "archimedean contribution",
        ):
            self.assertIn(term, terms)
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        for action_id in (
            "E4_A4_SOURCE_EXPANDED_ROOT_INTERFACE",
            "E4_A4_REGULAR_SOURCE_EXCLUSION",
            "E4_A4_RESONANT_SOURCE_EXCLUSION",
            "E4_A4_GLOBAL_FIRST_BAD_EXCLUSION",
        ):
            self.assertEqual(
                registry["actions"][action_id]["concept_id"],
                "canonical_source_exclusion",
            )

    def test_as_of_search_does_not_see_future_commit(self):
        td, repo, old, new = self._fixture_repo()
        self.addCleanup(td.cleanup)
        receipt = search_concept(
            repo_root=repo,
            concept_id="deformation_budget",
            as_of_ref=old,
            aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
            mode="COUNTERFACTUAL_REPLAY",
        )
        assert_receipt_as_of(repo, receipt)
        self.assertEqual(receipt.search_scope, "ANCHOR_REACHABLE_ONLY_IN_DECLARED_PATHS")
        self.assertEqual(receipt.search_paths, DEFAULT_GIT_SEARCH_PATHS)
        self.assertTrue(all(hit.source_commit != new for hit in receipt.hits if hit.source_commit))
        self.assertTrue(any("residual headroom" in hit.excerpt for hit in receipt.hits))

    def test_archaeology_searches_unmerged_historical_branch(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        self._git(repo, "checkout", "-b", "old-unmerged", old)
        branch_file = repo / "research" / "RHRC" / "branch.md"
        branch_file.write_text("detectability budget branch clue\n", encoding="utf-8")
        self._git(repo, "add", ".")
        # Git archaeology uses commit time, not the order fixture commits are made.
        self._git(
            repo, "commit", "-m", "unmerged historical clue",
            commit_date="2001-01-02T00:00:00Z",
        )
        branch_commit = self._git(repo, "rev-parse", "HEAD")
        self._git(repo, "checkout", "main")
        anchor = self._git(repo, "rev-parse", "HEAD")
        receipt = search_concept(
            repo_root=repo,
            concept_id="deformation_budget",
            as_of_ref=anchor,
            aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
        )
        self.assertEqual(receipt.search_scope, "ALL_REFS_BEFORE_ANCHOR_IN_DECLARED_PATHS")
        self.assertEqual(receipt.search_paths, DEFAULT_GIT_SEARCH_PATHS)
        self.assertTrue(any(hit.source_commit == branch_commit for hit in receipt.hits))

    def test_archaeology_excludes_unmerged_branch_after_anchor(self):
        td, repo, old, anchor = self._fixture_repo()
        self.addCleanup(td.cleanup)
        self._git(repo, "checkout", "-b", "future-unmerged", old)
        branch_file = repo / "research" / "RHRC" / "branch.md"
        branch_file.write_text("detectability budget future branch clue\n", encoding="utf-8")
        self._git(repo, "add", ".")
        self._git(
            repo, "commit", "-m", "unmerged future clue",
            commit_date="2001-01-04T00:00:00Z",
        )
        branch_commit = self._git(repo, "rev-parse", "HEAD")
        self._git(repo, "checkout", "main")
        receipt = search_concept(
            repo_root=repo,
            concept_id="deformation_budget",
            as_of_ref=anchor,
            aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
        )
        self.assertTrue(receipt.hits)
        self.assertTrue(all(hit.source_commit != branch_commit for hit in receipt.hits))

    def test_receipt_hash_binds_declared_paths(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        common = dict(
            repo_root=repo,
            concept_id="deformation_budget",
            as_of_ref=old,
            aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
            mode="COUNTERFACTUAL_REPLAY",
        )
        a = search_concept(**common, git_search_paths=("research/RHRC",))
        b = search_concept(**common, git_search_paths=("research/RHRC", "Zeta23"))
        self.assertNotEqual(a.receipt_id, b.receipt_id)

    def test_counterfactual_replay_enforces_anchor(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        receipt = replay_concept(repo_root=repo, concept_id="deformation_budget", as_of_ref=old)
        self.assertEqual(receipt.mode, "COUNTERFACTUAL_REPLAY")
        assert_receipt_as_of(repo, receipt)

    def test_receipt_hash_is_deterministic(self):
        td, repo, old, _ = self._fixture_repo()
        self.addCleanup(td.cleanup)
        kwargs = dict(
            repo_root=repo,
            concept_id="deformation_budget",
            as_of_ref=old,
            aliases_path=RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json",
            mode="COUNTERFACTUAL_REPLAY",
        )
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
                    {"path": "future.txt", "available_from_utc": "2099-01-01T00:00:00Z", "sha256": hashlib.sha256(future_file.read_bytes()).hexdigest()},
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
