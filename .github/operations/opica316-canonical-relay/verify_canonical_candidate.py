"""Verify the exact #316 canonical patch and the resulting tree in an isolated Git index."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path
from zipfile import ZipFile


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git(repo: Path, *args: str, env: dict[str, str] | None = None) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), *args], env=env)


def require_hash(value: str) -> None:
    need(isinstance(value, str) and len(value) == 64
         and all(character in "0123456789abcdef" for character in value),
         "Invalid digest in canonical receipt")


def verify_receipt(
    receipt: dict, patch: bytes, census: dict, head: str, tree: str
) -> dict[str, dict]:
    need(receipt.get("schema") == "OPICA_CANONICAL_CANDIDATE_V3"
         and receipt.get("status") == "REVIEW_ONLY_GENERATED_STATE"
         and receipt.get("phase") == "COMPLETE",
         "Canonical artifact is incomplete")
    need(receipt.get("source_head") == head and receipt.get("source_tree") == tree,
         "Canonical candidate source identity differs")
    need(receipt.get("proof_acceptance") is False
         and all(receipt.get(name) == "OPEN" for name in ("RH", "C1", "Step4")),
         "Canonical candidate claim scope differs")

    need(census["head_trees"]["316"] == {"head": head, "tree": tree},
         "Census is not for the exact candidate head and tree")
    products = {record["path"]: record for record in census["products"]}
    need(len(census["products"]) == len(products) == receipt["total_count"] == 81,
         "Canonical product inventory is incomplete")
    active = {name for name, record in products.items() if record["role"] == "ACTIVE"}
    frozen = {name for name, record in products.items() if record["role"] == "FROZEN"}
    need(len(active) == receipt["active_count"] == 77
         and len(frozen) == receipt["frozen_count"] == 4,
         "Canonical active/frozen count differs")

    before, after, checked = (
        receipt[name] for name in ("before_sha256", "after_write_sha256", "after_check_sha256")
    )
    need(set(before) == set(after) == set(checked) == set(products), "Product path map differs")
    for sha in {*before.values(), *after.values(), *checked.values()}:
        require_hash(sha)
    need(checked == after, "Canonical output changed on check")
    changed = sorted(name for name in products if before[name] != after[name])
    need(set(changed) <= active and changed == receipt["changed_paths"]
         and len(changed) == receipt["changed_count"],
         "Changed product inventory differs")
    need(receipt["frozen_git_oids"] ==
         {name: products[name]["trees"]["316"] for name in frozen},
         "Frozen product Git identities differ")
    need(digest(patch) == receipt["patch_sha256"], "Canonical patch digest mismatch")
    return products


def verify_applied_tree(repo: Path, patch: bytes, receipt: dict, products: dict) -> str:
    head, tree = receipt["source_head"], receipt["source_tree"]
    need(git(repo, "rev-parse", head + "^{tree}").decode().strip() == tree,
         "Repository is missing the exact source tree")
    for path, record in products.items():
        need(git(repo, "rev-parse", f"{head}:{path}").decode().strip()
             == record["trees"]["316"], f"Original Git blob differs: {path}")
        need(digest(git(repo, "show", f"{head}:{path}")) == receipt["before_sha256"][path],
             f"Original product bytes differ: {path}")

    with tempfile.TemporaryDirectory(prefix="opica-canonical-index-") as directory:
        staging = Path(directory)
        env = {**os.environ, "GIT_INDEX_FILE": str(staging / "index")}
        git(repo, "read-tree", head, env=env)
        if patch:
            patch_file = staging / "candidate.patch"
            patch_file.write_bytes(patch)
            git(repo, "apply", "--cached", "--whitespace=error-all", str(patch_file), env=env)
        names = git(repo, "diff", "--cached", "--name-status", "--no-renames", "-z", head, env=env)
        fields = names.rstrip(b"\x00").decode("utf-8").split("\x00") if names else []
        need(len(fields) == 2 * len(receipt["changed_paths"])
             and all(status == "M" for status in fields[::2])
             and sorted(fields[1::2]) == receipt["changed_paths"],
             "Patch includes an undeclared path, mode change, addition or deletion")
        for path in products:
            index_entry = git(repo, "ls-files", "--stage", "--", path, env=env)
            need(index_entry.startswith(b"100644 "), f"Applied product file mode differs: {path}")
            need(digest(git(repo, "show", f":{path}", env=env)) == receipt["after_write_sha256"][path],
                 f"Applied product bytes differ: {path}")
        return git(repo, "write-tree", env=env).decode().strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--archive-sha256", required=True)
    parser.add_argument("--census", required=True, type=Path)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--expected-tree", required=True)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    with args.archive.open("rb") as outer:
        need(hashlib.file_digest(outer, "sha256").hexdigest() == args.archive_sha256,
             "Actions artifact archive digest mismatch")
        with ZipFile(outer) as archive:
            need(len(archive.namelist()) == len(set(archive.namelist())),
                 "Duplicate evidence members")
            receipt = json.loads(archive.read("receipt.json"))
            patch = archive.read("generated-state.patch")
            for name, expected in receipt["logs_sha256"].items():
                need(digest(archive.read(name)) == expected, f"Log digest differs: {name}")
        outer.seek(0)
        need(hashlib.file_digest(outer, "sha256").hexdigest() == args.archive_sha256,
             "Artifact archive changed while being read")

    census = json.loads(args.census.read_bytes())
    products = verify_receipt(receipt, patch, census, args.expected_head, args.expected_tree)
    result_tree = verify_applied_tree(args.repo, patch, receipt, products)

    result = {
        "schema": "RH_WORKMODE_CANONICAL_CANDIDATE_INDEPENDENT_REVIEW_V1",
        "status": "PASS_SCOPED_PATCH_REPLAY_ONLY",
        "source_head": args.expected_head,
        "source_tree": args.expected_tree,
        "result_tree": result_tree,
        "artifact_archive_sha256": args.archive_sha256,
        "generated_patch_sha256": digest(patch),
        "changed_paths": receipt["changed_paths"],
        "proof_acceptance": False,
    }
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        json.dump(result, output, ensure_ascii=False, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
