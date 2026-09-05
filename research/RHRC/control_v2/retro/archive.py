from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from control_v2.retro.schemas import HistoricalClue

TEXT_SUFFIXES = {".md", ".txt", ".json", ".py", ".lean", ".yml", ".yaml"}
MANIFEST_NAME = "RETRO_ARCHIVE_MANIFEST.json"


class ArchiveManifestError(RuntimeError):
    pass


@dataclass(frozen=True)
class ArchiveEntry:
    path: str
    source_family: str
    source_version: str | None
    authority: str
    available_from_utc: datetime | None


def _parse_utc(value: str | None) -> datetime | None:
    if value is None:
        return None
    dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def anchor_commit_time(repo_root: Path, as_of_ref: str) -> datetime:
    proc = subprocess.run(
        ["git", "show", "-s", "--format=%cI", as_of_ref],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    return _parse_utc(proc.stdout.strip()) or datetime.min.replace(tzinfo=timezone.utc)


def load_manifest(root: Path) -> tuple[ArchiveEntry, ...]:
    path = root / MANIFEST_NAME
    if not path.is_file():
        raise ArchiveManifestError(
            f"counterfactual external-archive replay requires {MANIFEST_NAME}"
        )
    data = json.loads(path.read_text(encoding="utf-8"))
    entries: list[ArchiveEntry] = []
    for raw in data.get("sources", []):
        entries.append(ArchiveEntry(
            path=str(raw["path"]),
            source_family=str(raw.get("source_family", "EXTERNAL_ARCHIVE")),
            source_version=raw.get("source_version"),
            authority=str(raw.get("authority", "HISTORICAL_ARCHIVE")),
            available_from_utc=_parse_utc(raw.get("available_from_utc")),
        ))
    return tuple(entries)


def _scan_file(path: Path, *, root: Path, concept_id: str, terms: tuple[str, ...],
               family: str, version: str | None, authority: str,
               max_hits: int) -> list[HistoricalClue]:
    if path.suffix.lower() not in TEXT_SUFFIXES:
        return []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except UnicodeDecodeError:
        return []
    hits: list[HistoricalClue] = []
    for number, line in enumerate(lines, 1):
        folded = line.casefold()
        for term in terms:
            if term.casefold() in folded:
                hits.append(HistoricalClue(
                    concept_id=concept_id,
                    term=term,
                    source_family=family,
                    source_version=version,
                    source_path=str(path.relative_to(root)),
                    source_commit=None,
                    line_number=number,
                    excerpt=line.strip(),
                    authority=authority,
                ))
                break
        if len(hits) >= max_hits:
            break
    return hits


def search_archive(root: Path, *, concept_id: str, terms: tuple[str, ...],
                   mode: str, repo_root: Path, as_of_ref: str,
                   max_hits: int = 100) -> tuple[HistoricalClue, ...]:
    if not root.exists():
        return ()

    hits: list[HistoricalClue] = []
    if mode == "COUNTERFACTUAL_REPLAY":
        cutoff = anchor_commit_time(repo_root, as_of_ref)
        for entry in load_manifest(root):
            if entry.available_from_utc is None:
                # Unknown historical availability is not admitted into a time-travel replay.
                continue
            if entry.available_from_utc > cutoff:
                continue
            path = root / entry.path
            if not path.is_file():
                continue
            hits.extend(_scan_file(
                path,
                root=root,
                concept_id=concept_id,
                terms=terms,
                family=entry.source_family,
                version=entry.source_version,
                authority=entry.authority,
                max_hits=max_hits - len(hits),
            ))
            if len(hits) >= max_hits:
                break
    else:
        # Archaeology may inspect the whole supplied archive.  Authority remains
        # historical and every clue still requires revalidation.
        for path in sorted(root.rglob("*")):
            if path.name == MANIFEST_NAME or not path.is_file():
                continue
            hits.extend(_scan_file(
                path,
                root=root,
                concept_id=concept_id,
                terms=terms,
                family="EXTERNAL_ARCHIVE",
                version=None,
                authority="HISTORICAL_ARCHIVE",
                max_hits=max_hits - len(hits),
            ))
            if len(hits) >= max_hits:
                break

    return tuple(sorted(hits, key=lambda h: (h.source_family, h.source_path, h.line_number or 0, h.term)))
