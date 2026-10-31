"""Exact immutable source-blob verification of the inspected Round 3 archive.

This is an integrity preflight, NOT a replacement for actual checked source
identity, accepted merge/head, Lean compilation, or human approval.
"""
from __future__ import annotations
from hashlib import sha1, sha256
import json
from pathlib import Path, PurePosixPath
from zipfile import ZipFile

ARCHIVE_ROOT = "zeta-23-lean-research-opica-round3/"


def git_blob(data: bytes) -> str:
    return sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def safe_archive_name(name: str) -> str:
    if type(name) is not str or not name or "\\" in name or name.startswith("/"):
        raise ValueError("unsafe archive path")
    pieces = name.split("/")
    if any(not p or p in {".", ".."} or ":" in p or "\x00" in p for p in pieces):
        raise ValueError("unsafe archive path component")
    return name


def compare_locked_sources(repository_zip: Path, locks: dict[str, str]) -> dict[str, object]:
    if not isinstance(locks, dict) or not locks:
        raise ValueError("empty source lock")
    archive = Path(repository_zip)
    if not archive.is_file():
        raise FileNotFoundError(archive)
    results: dict[str, str] = {}
    with ZipFile(archive) as bundle:
        names = bundle.namelist()
        if len(names) != len(set(names)):
            raise ValueError("duplicate zip entries")
        for name in names:
            safe_archive_name(name.rstrip("/"))
        for path, expected in sorted(locks.items()):
            safe_archive_name(path)
            name = ARCHIVE_ROOT + path
            try:
                data = bundle.read(name)
            except KeyError as exc:
                raise ValueError(f"missing locked source {path}") from exc
            got = git_blob(data)
            if got != expected:
                raise ValueError(f"blob mismatch for {path}: {got} != {expected}")
            results[path] = got
    return {"archive_path": str(archive), "archive_sha256": sha256(archive.read_bytes()).hexdigest(),
            "verified_git_blobs": results, "status": "SOURCE_BLOBS_MATCH_INSPECTED_SNAPSHOT_ONLY"}
