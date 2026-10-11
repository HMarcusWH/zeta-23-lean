"""Fixed shard layout for the source-only candidate dependency receipt.

The receipt is one logical dataset: rows sorted by ``declaration``, each
rendered as one canonical JSON line. It is stored as 16 fixed shards keyed on
the first hex digit of sha256(declaration), so no single tracked file nears
GitHub's 50 MiB warning or 100 MiB limit. Each shard keeps the global
declaration order, so merging the shards by declaration reproduces the
former single-file byte stream exactly, and ``logical_sha256`` equals the
sha256 of that former file.

Standard library only; producers and readers load this file by path.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]

SHARD_KEYS = "0123456789abcdef"
SHARD_DIR = "research/RHRC/integration/generated/source_only_dependencies"
SHARD_PATHS = [
    f"{SHARD_DIR}/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-{key}.jsonl" for key in SHARD_KEYS
]
LEGACY_PATH = "research/RHRC/integration/generated/SOURCE_ONLY_CANDIDATE_DEPENDENCIES.jsonl"
SHARD_MAX_BYTES = 50 * 1024 * 1024


def shard_key(declaration: str) -> str:
    return hashlib.sha256(declaration.encode("utf-8")).hexdigest()[0]


def render_row(row: dict) -> str:
    return json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"


def render_shards(rows: list[dict]) -> dict[str, bytes]:
    """Render every shard, empty ones included, in global declaration order."""
    buckets: dict[str, list[str]] = {key: [] for key in SHARD_KEYS}
    for row in sorted(rows, key=lambda r: r["declaration"]):
        buckets[shard_key(row["declaration"])].append(render_row(row))
    return {
        path: "".join(buckets[key]).encode("utf-8")
        for key, path in zip(SHARD_KEYS, SHARD_PATHS)
    }


def shard_file_errors(repo: Path = REPO) -> list[str]:
    """Exact shard file set, no legacy monolith, per-shard size cap."""
    errors: list[str] = []
    if (repo / LEGACY_PATH).exists():
        errors.append(f"legacy monolithic receipt {LEGACY_PATH} must be removed")
    shard_dir = repo / SHARD_DIR
    declared = set(SHARD_PATHS)
    present = (
        {p.relative_to(repo).as_posix() for p in shard_dir.rglob("*") if p.is_file()}
        if shard_dir.exists()
        else set()
    )
    if present != declared:
        errors.append(
            "source-only shard set drift: "
            f"missing={sorted(declared - present)}, extra={sorted(present - declared)}"
        )
    for path in SHARD_PATHS:
        full = repo / path
        if full.exists() and full.stat().st_size > SHARD_MAX_BYTES:
            errors.append(f"{path} exceeds the {SHARD_MAX_BYTES} byte shard cap")
    return errors


def load_rows(repo: Path = REPO) -> list[dict]:
    """Read all shards as one dataset in global declaration order."""
    errors = shard_file_errors(repo)
    if errors:
        raise SystemExit("source_only_shards: " + "; ".join(errors))
    rows: list[dict] = []
    for key, path in zip(SHARD_KEYS, SHARD_PATHS):
        previous = None
        for line in (repo / path).read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            name = row["declaration"]
            if shard_key(name) != key:
                raise SystemExit(f"source_only_shards: {name} is in the wrong shard {path}")
            if previous is not None and name <= previous:
                raise SystemExit(f"source_only_shards: {path} is not strictly declaration-sorted")
            previous = name
            rows.append(row)
    rows.sort(key=lambda r: r["declaration"])
    return rows


def logical_sha256(repo: Path = REPO) -> str:
    """sha256 of the logical single-stream receipt (the former monolithic file)."""
    digest = hashlib.sha256()
    for row in load_rows(repo):
        digest.update(render_row(row).encode("utf-8"))
    return digest.hexdigest()
