from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

from control_v2.retro.archive import MANIFEST_NAME, TEXT_SUFFIXES


def _safe_name(value: str) -> str:
    out = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    return out or "source.txt"


def ingest_text_source(*, source: Path, archive_root: Path, source_family: str,
                       source_version: str | None, authority: str,
                       available_from_utc: str) -> dict:
    if source.suffix.lower() not in TEXT_SUFFIXES:
        raise ValueError("retro ingestion accepts normalized text/code files only")
    raw = source.read_bytes()
    # Validate UTF-8 now so archive search remains deterministic later.
    raw.decode("utf-8")
    sha = hashlib.sha256(raw).hexdigest()
    corpus = archive_root / "corpus"
    corpus.mkdir(parents=True, exist_ok=True)
    destination = corpus / f"{sha[:12]}_{_safe_name(source.name)}"
    if not destination.exists():
        shutil.copyfile(source, destination)

    manifest_path = archive_root / MANIFEST_NAME
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    else:
        manifest = {"schema_version": "RHRC-retro-archive-1.0", "sources": []}

    entry = {
        "path": str(destination.relative_to(archive_root)),
        "source_family": source_family,
        "source_version": source_version,
        "authority": authority,
        "available_from_utc": available_from_utc,
        "sha256": sha,
    }
    existing = {item.get("sha256") for item in manifest.get("sources", [])}
    if sha not in existing:
        manifest.setdefault("sources", []).append(entry)
        manifest["sources"] = sorted(
            manifest["sources"],
            key=lambda item: (item.get("available_from_utc", ""), item.get("source_family", ""), item.get("path", "")),
        )
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return entry


def main() -> int:
    parser = argparse.ArgumentParser(description="Ingest a normalized historical text source for RHRC retro replay")
    parser.add_argument("source", type=Path)
    parser.add_argument("--archive-root", type=Path, required=True)
    parser.add_argument("--source-family", required=True)
    parser.add_argument("--source-version")
    parser.add_argument("--authority", default="HISTORICAL_ARCHITECTURE")
    parser.add_argument("--available-from-utc", required=True)
    args = parser.parse_args()
    entry = ingest_text_source(
        source=args.source,
        archive_root=args.archive_root,
        source_family=args.source_family,
        source_version=args.source_version,
        authority=args.authority,
        available_from_utc=args.available_from_utc,
    )
    print(json.dumps(entry, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
