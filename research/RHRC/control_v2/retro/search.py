from __future__ import annotations

from pathlib import Path

from control_v2.retro.aliases import expanded_terms, load_alias_map
from control_v2.retro.archive import search_archive
from control_v2.retro.git_history import search_git_history
from control_v2.retro.schemas import HistoricalClue, RetroSearchReceipt

RETRO = Path(__file__).resolve().parent
DEFAULT_GIT_SEARCH_PATHS = ("research/RHRC", "Zeta23")


def search_concept(*, repo_root: Path, concept_id: str, as_of_ref: str,
                   archive_root: Path | None = None,
                   aliases_path: Path | None = None,
                   mode: str = "ARCHAEOLOGY",
                   exhaustive: bool = True,
                   git_search_paths: tuple[str, ...] = DEFAULT_GIT_SEARCH_PATHS) -> RetroSearchReceipt:
    """Search old implementations with vocabulary expansion.

    Archaeology searches all Git refs whose commits predate the anchor, within
    the explicitly declared Git search paths. Counterfactual replay is
    deliberately narrower: only commits reachable from the historical anchor
    are eligible. `exhaustive=True` removes hit/commit caps and is required for
    claim-like statements about having searched that declared domain.
    """
    if not git_search_paths:
        raise ValueError("at least one Git search path is required")
    if aliases_path is None:
        aliases_path = RETRO / "CONCEPT_ALIAS_MAP.json"
    aliases = load_alias_map(aliases_path)
    terms = expanded_terms(concept_id, aliases)

    archaeology = mode == "ARCHAEOLOGY"
    git_hits = search_git_history(
        repo_root,
        terms,
        as_of_ref=as_of_ref,
        paths=git_search_paths,
        all_refs_before_anchor=archaeology,
        max_commits_per_term=None if exhaustive else 25,
        max_hits=None if exhaustive else 200,
    )
    clues: list[HistoricalClue] = [
        HistoricalClue(
            concept_id=concept_id,
            term=hit.term,
            source_family="RHRC_GIT",
            source_version=None,
            source_path=hit.path,
            source_commit=hit.commit,
            line_number=hit.line_number,
            excerpt=hit.text,
            authority="REPOSITORY_HISTORY",
        )
        for hit in git_hits
    ]
    searched = ["RHRC_GIT"]

    if archive_root is not None:
        clues.extend(search_archive(
            archive_root,
            concept_id=concept_id,
            terms=terms,
            mode=mode,
            repo_root=repo_root,
            as_of_ref=as_of_ref,
            max_hits=None if exhaustive else 200,
        ))
        searched.append("EXTERNAL_ARCHIVE")

    clues = sorted(
        clues,
        key=lambda h: (
            h.source_family,
            h.source_commit or "",
            h.source_path,
            h.line_number or 0,
            h.term,
        ),
    )
    return RetroSearchReceipt(
        concept_id=concept_id,
        terms=terms,
        mode=mode,
        as_of_ref=as_of_ref,
        search_scope="ALL_REFS_BEFORE_ANCHOR_IN_DECLARED_PATHS" if archaeology else "ANCHOR_REACHABLE_ONLY_IN_DECLARED_PATHS",
        search_complete=exhaustive,
        searched_sources=tuple(searched),
        search_paths=tuple(git_search_paths),
        hits=tuple(clues),
    )
