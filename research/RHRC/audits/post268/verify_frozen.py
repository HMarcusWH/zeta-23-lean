#!/usr/bin/env python3
"""Fail-closed verifier for the byte-frozen post-268 audit corpus.

The 102 listed files are checked against the original bundle SHA-256 ledger.
BUNDLE_SHA256SUMS.txt is the 103rd file and is intentionally not self-hashed.
This verifier creates no theorem authority; it verifies historical audit bytes.
"""

from __future__ import annotations

import hashlib
from pathlib import Path, PurePosixPath

HERE = Path(__file__).resolve().parent
FROZEN = HERE / "frozen"
SUMS = FROZEN / "BUNDLE_SHA256SUMS.txt"
EXPECTED_LISTED = 102
EXPECTED_TOTAL = 103


def fail(message: str) -> None:
    raise SystemExit("post268_frozen_verify: " + message)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    if not FROZEN.is_dir():
        fail("frozen corpus is missing")
    if not SUMS.is_file():
        fail("BUNDLE_SHA256SUMS.txt is missing")

    rows: list[tuple[str, str]] = []
    seen: set[str] = set()
    for number, raw in enumerate(SUMS.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw.strip():
            continue
        try:
            digest, name = raw.split("  ", 1)
        except ValueError:
            fail(f"malformed checksum line {number}")
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            fail(f"invalid sha256 on line {number}")
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or not rel.parts:
            fail(f"unsafe path on line {number}: {name!r}")
        if name in seen:
            fail(f"duplicate checksum path: {name}")
        seen.add(name)
        path = FROZEN.joinpath(*rel.parts)
        if not path.is_file() or path.is_symlink():
            fail(f"missing or unsafe frozen file: {name}")
        actual = sha256(path)
        if actual != digest:
            fail(f"sha256 mismatch: {name}: {actual} != {digest}")
        rows.append((digest, name))

    if len(rows) != EXPECTED_LISTED:
        fail(f"checksum population drift: {len(rows)} != {EXPECTED_LISTED}")

    actual_files = {
        path.relative_to(FROZEN).as_posix()
        for path in FROZEN.rglob("*")
        if path.is_file()
    }
    expected_files = seen | {"BUNDLE_SHA256SUMS.txt"}
    if actual_files != expected_files:
        fail(
            "frozen file-set drift: "
            f"missing={sorted(expected_files - actual_files)} "
            f"extra={sorted(actual_files - expected_files)}"
        )
    if len(actual_files) != EXPECTED_TOTAL:
        fail(f"frozen file count drift: {len(actual_files)} != {EXPECTED_TOTAL}")

    manifest = FROZEN / "results" / "file_manifest.jsonl"
    if len(manifest.read_text(encoding="utf-8").splitlines()) != 1207:
        fail("reconstructed post-268 base manifest no longer has 1207 rows")

    print(
        "POST268 FROZEN AUDIT: PASS "
        f"({EXPECTED_LISTED} hash-bound files + checksum ledger; "
        "historical evidence only; RH_OPEN)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
