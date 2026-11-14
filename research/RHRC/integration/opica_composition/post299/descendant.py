"""Reviewed-candidate post-299 source-scope validator.

This is a successor scope, NOT a change to the sealed OPICA4 descendant
checker. The original descendant.py, Round4 manifest, test baselines and
workflow selectors are inherited byte-for-byte. Versioned review of this
source and its bounded file allowance remains a release prerequisite.

It authenticates the exact accepted PR299 merge tree before allowing ANY
subsequent source change. No source/provider wildcard is admitted.
Derived-state files are handled only as exact preexisting generated products;
the separate RHKG --check gate must validate their actual contents.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from ..canonical import require
from ..snapshot import file_hash, unlinked
from ..descendant import (
    REPO, MANIFEST as INHERITED_MANIFEST, AUDITED_PATH_POLICY as V1_POLICY,
    validate_workflow_migration,
)

PARENT = "df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
PARENT_TREE = "5fc2aa4793b658c58dd89c1d36b0ceee756d400d"

# Exact approved candidate source blobs, not a self-authorizing manifest.
# Changes require a new reviewed successor version and fresh compiler receipts.
ADDED_SOURCE = {
    ".github/workflows/rhrc_post299_parity_candidate.yml":
        "931f6b11340cf16446b3f60a84eb469aad2c306f",
    "Zeta23/OPICARound5/ParityMomentBridge.lean":
        "acecc7d2cd78bf2178c67b03019de40fcb2eab79",
}
THIS_VALIDATOR = (
    "research/RHRC/integration/opica_composition/post299/descendant.py"
)
CHANGED_SOURCE = {
    "research/RHRC/integration/opica_composition/cli.py": "e587c38e32ecc416df403133e5eef1038c00b176",
    "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json":
        "8851d0a9cd5bc234af376cf35ca0c9894dcee0df",
}
GENERATED_ROOTS = (
    "research/RHRC/graph/compiler/",
    "research/RHRC/graph/generated/",
    "research/RHRC/integration/generated/",
    "research/RHRC/ffbbp/generated/",
    "research/RHRC/ool/generated/",
)
# New generated paths may only be introduced in a separately reviewed version.
ADDED = frozenset((*ADDED_SOURCE, THIS_VALIDATOR))
EDITED = frozenset(CHANGED_SOURCE)


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True
    ).strip()


def classify_delta(rows: list[tuple[str, str]],
                   parent_paths: set[str]) -> tuple[list[str], list[str], list[str]]:
    """Fail closed on additions, deletions, unknown edits, and mode changes."""
    added, edited, generated = [], [], []
    for status, path in rows:
        require(status in ("A", "M"), "successor deletion, rename or mode change: " + path)
        if status == "A":
            require(path in ADDED, "undeclared successor source: " + path)
            require(path not in parent_paths, "source addition already present in parent: " + path)
            added.append(path)
        else:
            require(path in parent_paths, "unanchored modification: " + path)
            if path in EDITED:
                edited.append(path)
            else:
                require(
                    any(path.startswith(prefix) for prefix in GENERATED_ROOTS)
                    and path.endswith((".json", ".jsonl")),
                    "protected parent bytes changed: " + path,
                )
                generated.append(path)
    require(set(added) == ADDED, "mandatory successor source missing")
    require(set(edited) == EDITED, "mandatory governed successor edits missing")
    require(len(set(added + edited + generated)) == len(rows),
            "duplicate source operation")
    return sorted(added), sorted(edited), sorted(generated)


def validate_descendant(repo: Path = REPO, *, require_clean: bool = False) -> dict:
    """Current-head post299 gate; never interprets V1 as current-head acceptance."""
    repo = unlinked(repo).resolve()
    require(git(repo, "rev-parse", PARENT + "^{tree}") == PARENT_TREE,
            "accepted PR299 parent tree changed")
    require(subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", PARENT, "HEAD"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    ).returncode == 0, "successor is not descended from PR299")
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "dirty successor checkout")
    parent_rows = git(repo, "ls-tree", "-r", PARENT).splitlines()
    parent_modes = {}
    for row in parent_rows:
        left, path = row.split("\t", 1)
        mode, kind, _ = left.split()
        require(kind == "blob", "unexpected parent source object type")
        parent_modes[path] = mode
    diff = git(repo, "diff", "--no-renames", "--name-status", PARENT, "HEAD")
    changes = []
    if diff:
        for line in diff.splitlines():
            status, path = line.split("\t", 1)
            changes.append((status, path))
    added, edited, generated = classify_delta(changes, set(parent_modes))
    for path in added + edited:
        file = unlinked(repo / path)
        require(file.is_file() and not file.is_symlink(),
                "missing, nonfile or symlinked reviewed source: " + path)
        mode = git(repo, "ls-tree", "HEAD", "--", path).split()[0]
        require(mode == "100644", "new source has nonstandard file mode: " + path)
        expected = ADDED_SOURCE.get(path, CHANGED_SOURCE.get(path))
        if path != THIS_VALIDATOR:
            require(re.fullmatch("[0-9a-f]{40}", expected or "") is not None,
                    "source proof digest not pinned: " + path)
            require(git(repo, "hash-object", "--", path) == expected,
                    "reviewed source blob changed: " + path)
    for path in generated:
        require(parent_modes[path] == "100644",
                "generated file does not have a regular parent source")
        file = unlinked(repo / path)
        require(file.is_file() and not file.is_symlink(),
                "invalid generated artifact")
        require(git(repo, "ls-tree", "HEAD", "--", path).split()[0] == "100644",
                "generated file mode changed")
    # Preserve historical selector counts exactly as in the original checker.
    # The V1 checker itself and its manifest cannot change under classify_delta.
    validate_workflow_migration(repo)
    ignored = git(repo, "ls-files", "--others", "--ignored", "--exclude-standard")
    for path in ignored.splitlines():
        if path.startswith(("Zeta23/", "research/", ".github/")) and path.endswith(
            (".lean", ".lean.in", ".py", ".yml")
        ):
            require(False, "ignored executable/source provider: " + path)
    policy = {
        "schema": "OPICA5_POST299_SUCCESSOR_SOURCE_POLICY_V1",
        "parent": PARENT,
        "parent_tree": PARENT_TREE,
        "v1_policy": V1_POLICY,
        "added_source": dict(sorted(ADDED_SOURCE.items())),
        "validator": THIS_VALIDATOR,
        "changed_source": dict(sorted(CHANGED_SOURCE.items())),
        "generated_roots": GENERATED_ROOTS,
        "source_validation": "EXACT_GIT_BLOB_SHA_AND_CLOSED_OPERATIONS",
        "generated_validation": "SEPARATE_RHKG_EXACT_SOURCE_CHECK_REQUIRED",
    }
    policy_digest = hashlib.sha256(
        json.dumps(policy, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        "schema": "OPICA5_POST299_SUCCESSOR_SOURCE_INSPECTION_V1",
        "status": "PASS_SOURCE_SCOPE_ONLY",
        "checked_commit": git(repo, "rev-parse", "HEAD"),
        "checked_tree": git(repo, "rev-parse", "HEAD^{tree}"),
        "base": PARENT,
        "base_tree": PARENT_TREE,
        "historical_v1_source_policy": V1_POLICY,
        "path_policy": policy_digest,
        "manifest_sha256": file_hash(repo / INHERITED_MANIFEST),
        "delta": {"added": added, "edited": edited,
                  "generated": generated, "deleted": []},
        "current_compiler_accepted": False,
        "full_round4_accepted": False,
        "successor_human_review": "PENDING",
        "RH": "OPEN",
        "Step4": "OPEN",
    }


def _selftest() -> None:
    parent = {"old.lean", "old.json", "research/RHRC/graph/generated/nodes.json", *EDITED}
    valid = [
        ("A", THIS_VALIDATOR),
        *(( "A", p) for p in ADDED_SOURCE),
        *(( "M", p) for p in EDITED),
        ("M", "research/RHRC/graph/generated/nodes.json"),
    ]
    assert len(classify_delta(valid, parent)[2]) == 1
    for mutation in [
        [*valid, ("A", "Zeta23/Undeclared.lean")],
        [*valid, ("M", "old.lean")],
        [*valid, ("D", "old.lean")],
        [*valid, ("A", "research/RHRC/graph/generated/phantom.json")],
        [row for row in valid if row[1] != THIS_VALIDATOR],
    ]:
        try:
            classify_delta(mutation, parent)
        except Exception:
            pass
        else:
            raise AssertionError("successor scope accepted an invalid mutation")
    print("POST299 successor closed-path negative controls: PASS")


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        _selftest()
    else:
        print(json.dumps(validate_descendant(REPO, require_clean=True),
                         sort_keys=True, indent=2))
