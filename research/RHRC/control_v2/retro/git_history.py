from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import subprocess


@dataclass(frozen=True)
class GitHit:
    commit: str
    path: str
    line_number: int | None
    text: str
    term: str


def _run(repo: Path, args: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        check=check,
        capture_output=True,
        text=True,
    )


def reachable_commits(repo: Path, as_of_ref: str) -> set[str]:
    proc = _run(repo, ["rev-list", as_of_ref])
    return {line.strip() for line in proc.stdout.splitlines() if line.strip()}


def commit_time(repo: Path, ref: str) -> str:
    return _run(repo, ["show", "-s", "--format=%cI", ref]).stdout.strip()


def _candidate_commits(repo: Path, term: str, as_of_ref: str,
                       paths: tuple[str, ...], *, all_refs_before_anchor: bool,
                       max_commits: int | None) -> tuple[str, ...]:
    regex = re.escape(term)
    args = ["log", "--format=%H", "--regexp-ignore-case", f"-G{regex}"]
    if all_refs_before_anchor:
        args.extend(["--all", f"--before={commit_time(repo, as_of_ref)}"])
    else:
        args.append(as_of_ref)
    args.extend(["--", *paths])
    proc = _run(repo, args)
    commits: list[str] = []
    for line in proc.stdout.splitlines():
        sha = line.strip()
        if sha and sha not in commits:
            commits.append(sha)
        if max_commits is not None and len(commits) >= max_commits:
            break

    # The anchor snapshot catches terms whose introduction predates the local
    # bounded history.  Unmerged historical branches are covered by --all in
    # archaeology mode through their change commits.
    return tuple(dict.fromkeys([as_of_ref, *commits]))


def search_git_history(repo: Path, terms: tuple[str, ...], *, as_of_ref: str,
                       paths: tuple[str, ...] = ("research/RHRC", "Zeta23"),
                       all_refs_before_anchor: bool = False,
                       max_commits_per_term: int | None = None,
                       max_hits: int | None = None) -> tuple[GitHit, ...]:
    """Search historical content, optionally across every ref existing before the anchor time.

    `all_refs_before_anchor=True` is the archaeology mode used to recover clues
    from old unmerged branches as well as mainline history. Counterfactual replay
    must keep it False and therefore stays inside the anchor's reachable DAG.
    """
    hits: list[GitHit] = []
    seen: set[tuple[str, str, int | None, str]] = set()

    for term in terms:
        for commit in _candidate_commits(
            repo, term, as_of_ref, paths,
            all_refs_before_anchor=all_refs_before_anchor,
            max_commits=max_commits_per_term,
        ):
            proc = _run(
                repo,
                ["grep", "-n", "-i", "--fixed-strings", term, commit, "--", *paths],
                check=False,
            )
            if proc.returncode not in (0, 1):
                raise RuntimeError(proc.stderr.strip() or "git grep failed")
            for row in proc.stdout.splitlines():
                parts = row.split(":", 3)
                if len(parts) != 4:
                    continue
                _, path, line_s, text = parts
                try:
                    line_number = int(line_s)
                except ValueError:
                    line_number = None
                key = (commit, path, line_number, text)
                if key in seen:
                    continue
                seen.add(key)
                hits.append(GitHit(commit, path, line_number, text.strip(), term))
                if max_hits is not None and len(hits) >= max_hits:
                    return tuple(sorted(hits, key=lambda h: (h.commit, h.path, h.line_number or 0, h.term)))

    return tuple(sorted(hits, key=lambda h: (h.commit, h.path, h.line_number or 0, h.term)))
