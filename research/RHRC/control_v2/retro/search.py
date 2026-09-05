from __future__ import annotations

from pathlib import Path

from control_v2.retro.aliases import expanded_terms, load_alias_map
from control_v2.retro.git_history import search_git_history
from control_v2.retro.schemas import HistoricalClue, RetroSearchReceipt

RETRO = Path(__file__).resolve().parent
TEXT_SUFFIXES = {".md", ".txt", ".json", ".py", ".lean", ".yml", ".yaml"}


def _search_archive(root: Path, concept_id: str, terms: tuple[str, ...], max_hits: int = 100) -> list[HistoricalClue]:
    hits: list[HistoricalClue] = []
    if not root.exists():
        return hits
    for path in sorted(root.rglob("*")):
        if not path.is_file() or path.suffix.lower() not in TEXT_SUFFIXES:
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for number, line in enumerate(lines, 1):
            folded = line.casefold()
            for term in terms:
                if term.casefold() in folded:
                    hits.append(HistoricalClue(
                        concept_id=concept_id,
                        term=term,
                        source_family="EXTERNAL_ARCHIVE",
                        source_version=None,
                        source_path=str(path.relative_to(root)),
                        source_commit=None,
                        line_number=number,
                        excerpt=line.strip(),
                        authority="HISTORICAL_ARCHIVE",
                    ))
                    break
            if len(hits) >= max_hits:
                return hits
    return hits


def search_concept(*, repo_root: Path, concept_id: str, as_of_ref: str,
                   archive_root: Path | None = None,
                   aliases_path: Path | None = None,
                   mode: str = "ARCHAEOLOGY") -> RetroSearchReceipt:
    if aliases_path is None:
        aliases_path = RETRO / "CONCEPT_ALIAS_MAP.json"
    aliases = load_alias_map(aliases_path)
    terms = expanded_terms(concept_id, aliases)

    git_hits = search_git_history(repo_root, terms, as_of_ref=as_of_ref)
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
        clues.extend(_search_archive(archive_root, concept_id, terms))
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
        searched_sources=tuple(searched),
        hits=tuple(clues),
    )
