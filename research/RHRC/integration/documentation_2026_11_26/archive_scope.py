"""Verify the exact November 26 paper archive independently of compiler work."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ARCHIVE_POLICY = Path(__file__).with_name("ARCHIVE_BYTES.json")
ARCHIVE_POLICY_SHA256 = "5bd485dc96709af030f50345d02498db334ff464c8aab8db3c8cfe41c966df8e"
PAPER_PREFIX = "papers/2026-11-26/"


class ArchiveError(ValueError):
    """The committed paper archive does not match the reviewed byte policy."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArchiveError(message)


def git(repo: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout


def tree(repo: Path, rev: str) -> dict[str, tuple[str, str, str]]:
    output = git(repo, "ls-tree", "-r", "-z", rev)
    result = {}
    for entry in output.split(b"\0"):
        if not entry:
            continue
        attributes, path = entry.split(b"\t", 1)
        mode, kind, blob = attributes.decode("ascii").split(" ")
        result[path.decode("utf-8")] = (mode, kind, blob)
    return result


def read_policy() -> dict:
    raw = ARCHIVE_POLICY.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == ARCHIVE_POLICY_SHA256,
            "Paper archive policy bytes differ from the reviewed version")
    return json.loads(raw)


def check_delta(base: dict, archive: dict, expected: dict) -> None:
    require(base.keys() <= archive.keys(), "Archive removed an inherited path")
    changed = sorted(name for name in base if archive[name] != base[name])
    require(not changed, "Archive edited inherited paths: " + repr(changed))
    added = archive.keys() - base.keys()
    require(added == expected.keys(), "Unexpected archive delta: " + repr(sorted(added ^ expected.keys())))
    for path, row in expected.items():
        require(path.startswith(PAPER_PREFIX), "Archive path outside its dated directory: " + path)
        require(archive[path] == ("100644", "blob", row["git_blob"]),
                "Archive file mode or Git blob differs: " + path)


def inspect_archive(repo: Path, policy: dict) -> dict:
    base, archive = policy["base_commit"], policy["archive_commit"]
    for commit, key in [(base, "base_tree"), (archive, "archive_tree")]:
        actual = git(repo, "rev-parse", commit + "^{tree}").decode("ascii").strip()
        require(actual == policy[key], "Unexpected tree at " + commit)
    ancestry = git(repo, "rev-list", "--parents", "--max-count=1", archive).decode("ascii").split()
    require(ancestry == [archive, base], "Reviewed archive commit has a different parent")
    expected = policy["added"]
    check_delta(tree(repo, base), tree(repo, archive), expected)
    require(len(expected) == 9, "Expected nine archived files")
    verified = {}
    for path, row in sorted(expected.items()):
        raw = git(repo, "cat-file", "blob", row["git_blob"])
        require(len(raw) == row["size_bytes"], "Archive file length differs: " + path)
        require(hashlib.sha256(raw).hexdigest() == row["sha256"], "Archive SHA-256 differs: " + path)
        if path.endswith(".pdf"):
            require(row["file_kind"] == "BINARY_PDF" and raw.startswith(b"%PDF-"),
                    "Archive PDF is missing its binary document header: " + path)
        else:
            require(row["file_kind"] == "TEXT", "Unexpected archive file class: " + path)
            raw.decode("utf-8")
        verified[path] = row

    manifest = json.loads(git(repo, "cat-file", "blob", archive + ":" + PAPER_PREFIX + "MANIFEST.json"))
    expected_pdfs = {path: row for path, row in verified.items() if row["file_kind"] == "BINARY_PDF"}
    require(len(expected_pdfs) == 6 == manifest["total_pdf_files"], "Manifest PDF count differs")
    require(len(manifest["files"]) == 6 == len({row["path"] for row in manifest["files"]}),
            "Manifest PDF paths are incomplete or duplicated")
    manifest_pdfs = {row["path"]: {"git_blob": row["git_blob_sha1"], "size_bytes": row["size_bytes"],
                                    "sha256": row["sha256"], "file_kind": "BINARY_PDF"}
                     for row in manifest["files"]}
    require(manifest_pdfs == expected_pdfs, "Manifest does not agree with the independently reviewed PDF inventory")
    require(sum(row["size_bytes"] for row in expected_pdfs.values()) == manifest["total_pdf_bytes"],
            "Manifest total PDF bytes differ")
    manuscript = manifest["new_manuscript"]["path"]
    require(manuscript in verified and manuscript.endswith(".md"), "Missing Markdown manuscript source")
    return {
        "schema": "RHRC_PAPER_ARCHIVE_BYTE_INSPECTION_V1",
        "status": "PASS_ARCHIVE_BYTES_ONLY",
        "archive_commit": archive,
        "archive_tree": policy["archive_tree"],
        "base_commit": base,
        "base_tree": policy["base_tree"],
        "articles": verified,
        "past_research_archive_preserved": True,
        "article_pdf_count": len(expected_pdfs),
        "article_pdf_bytes": manifest["total_pdf_bytes"],
        "proof_acceptance": False,
        "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED",
        "RH": "OPEN",
        "Step4": "OPEN",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        result = inspect_archive(args.repo.resolve(), read_policy())
    except (ArchiveError, UnicodeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Paper archive scope failed: {error}\n")
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
