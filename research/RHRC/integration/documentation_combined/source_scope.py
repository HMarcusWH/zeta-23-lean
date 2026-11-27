"""Authenticate the combined registration and paper source without granting theorem authority."""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from ..documentation_2026_11_21 import source_scope as historical
from ..documentation_2026_11_26 import source_scope as paper
from ..documentation_2026_11_26.archive_scope import git, inspect_archive, read_policy, tree
from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import MANIFEST, REPO, validate_workflow_migration
from ..opica_composition.snapshot import file_hash, unlinked
from ..opica_dispatch_registration import gate as registration

MAIN = "d4c7fc7114e5f1b61b90ea9037890969358ff0cc"
PAPER = "30b3a430c350eeeef9ff1aa8c99d10cd30dc3fb3"
LAYOUT = "f3c45bf57d9d084f8337616978a3f15e4fa9df4d"
BASE = "0242ac003843a5d9bf612d72491d23189e319203"
BASE_TREE = "dd10422dc0b48b5e3494823910464a10048edc94"
TREES = {MAIN: "7ab96c28f455d0bfdd280856b6d9e0bcf7015e5c",
         PAPER: "dbbbdd2dfc7c78f462b89a7a85001aa58341a221",
         LAYOUT: "1f5bc26c013592a9049b3e8eba2294dd710192a5", BASE: BASE_TREE}
WORKFLOW = ".github/workflows/documentation.yml"
CLI = "research/RHRC/integration/opica_composition/cli.py"
SERVICE = "research/RHRC/integration/opica_composition/service.py"
PREFIX = "research/RHRC/integration/documentation_combined/"
POLICY = PREFIX + "SOURCE_SCOPE.json"
VALIDATOR = PREFIX + "source_scope.py"
TEST = PREFIX + "test_source_scope.py"
POLICY_SHA256 = "a882ca9fd8ce897521410c81011f624c11ac9791e2f64fc708226d3ed770f27c"
SCHEMA = "RHRC_COMBINED_DOCUMENTATION_SOURCE_INSPECTION_V1"
POLICY_SCHEMA = "RHRC_COMBINED_DOCUMENTATION_SOURCE_POLICY_V1"
ADDED = {POLICY, VALIDATOR, TEST}
EDITED = {WORKFLOW, CLI}
REGULAR = ("100644", "blob")


def value(repo, *args):
    return git(repo, *args).decode("ascii").strip()


def authenticate_layout(repo, active, frozen, archive):
    """Check every inherited source against its original parents and their common base."""
    for commit, expected in TREES.items():
        require(value(repo, "rev-parse", commit + "^{tree}") == expected, "Unexpected tree for " + commit)
    require(value(repo, "show", "-s", "--format=%P", LAYOUT).split() == [MAIN, PAPER],
            "Combined layout parents differ")
    require(value(repo, "show", "-s", "--format=%P", BASE) == LAYOUT, "Canonical replay parent differs")
    ancestor = value(repo, "merge-base", "--all", MAIN, PAPER)
    require(re.fullmatch("[0-9a-f]{40}", ancestor), "Expected one common ancestor")
    common, left, right, layout, base = (tree(repo, ref) for ref in (ancestor, MAIN, PAPER, LAYOUT, BASE))
    require(set(layout) == left.keys() | right.keys() and base.keys() == layout.keys(),
            "Combined layout lost or introduced a path")
    for name, row in layout.items():
        if name in active:
            require(row == right[name] and base[name][:2] == REGULAR, "Unexpected product seed: " + name)
            continue
        require(base[name] == row, "Replay modified protected path: " + name)
        if name in {WORKFLOW, CLI, SERVICE}:
            # Conflict resolutions are sealed by the layout tree above.
            continue
        a, b, c = left.get(name), right.get(name), common.get(name)
        require(a == b or a == c or b == c, "Unreconciled inherited source: " + name)
        require(row == (b if a == c else a), "Incorrectly inherited source: " + name)
    require(all(left[p] == right[p] == layout[p] == base[p] for p in frozen), "Frozen parent products differ")
    for name, item in archive["articles"].items():
        require(base[name] == (*REGULAR, item["git_blob"]), "Archived article changed: " + name)
    return base


def introduction(repo, head):
    """Bind descendants to their unique original source-policy child of the product baseline."""
    git(repo, "merge-base", "--is-ancestor", BASE, head)
    records = git(repo, "rev-list", "--ancestry-path", "--parents", BASE + ".." + head).decode().splitlines()
    children = [fields[0] for row in records if (fields := row.split())[1:] == [BASE]]
    require(len(children) == 1, "Expected one combined policy introduction")
    require(value(repo, "show", "-s", "--format=%P", children[0]) == BASE,
            "Combined policy introduction parent differs")
    return children[0]


def classify(base, current, policy, active, initial):
    require(set(policy) == {"schema", "blobs", "validator_template_sha256"} and
            policy["schema"] == POLICY_SCHEMA and set(policy["blobs"]) == EDITED | {TEST},
            "Combined policy inventory differs")
    require(current.keys() == base.keys() | ADDED, "Combined source added, removed or renamed a path")
    changed = {name for name, row in base.items() if current[name] != row}
    require(changed - active == EDITED, "Unexpected combined source edits: " + repr(sorted((changed - active) ^ EDITED)))
    validate_path_inventory(sorted(changed | ADDED))
    require(all(current[p][:2] == REGULAR for p in changed | ADDED), "Combined edit changed mode or type")
    for path, blob in policy["blobs"].items():
        require(current[path] == (*REGULAR, blob), "Changed combined source blob: " + path)
    require(all(current[p] == initial.get(p) for p in ADDED | EDITED),
            "Source policy changed since introduction")
    return {"added": sorted(ADDED), "edited": sorted(EDITED), "generated": sorted(changed & active), "deleted": []}


def validate_descendant(repo: Path = REPO, *, require_clean: bool = False) -> dict:
    repo = unlinked(repo).resolve()
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Dirty combined checkout")
    head = value(repo, "rev-parse", "HEAD")
    first = introduction(repo, head)
    current = tree(repo, head)
    require(current.get(POLICY, ())[:2] == REGULAR, "Combined policy is absent")
    raw = git(repo, "cat-file", "blob", current[POLICY][2])
    require(sha256(raw).hexdigest() == POLICY_SHA256, "Combined policy digest differs")
    policy = load_bytes(raw)
    archive = inspect_archive(repo, read_policy())
    git(repo, "merge-base", "--is-ancestor", archive["archive_commit"], PAPER)
    active = set(paper.policy_from_archive(repo, archive["archive_commit"])["generated"])
    frozen = set(historical.round6.FROZEN_PRODUCTS)
    rows = load_bytes(git(repo, "show", BASE + ":" + MANIFEST))["generated"]
    require(len(rows) == 81 and {row["path"] for row in rows} == active | frozen and
            len(active) == 77 and len(frozen) == 4 and active.isdisjoint(frozen), "Product inventory differs")
    base = authenticate_layout(repo, active, frozen, archive)
    delta = classify(base, current, policy, active, tree(repo, first))
    require(historical.round6.validator_template_hash(git(repo, "cat-file", "blob", current[VALIDATOR][2]),
            POLICY_SHA256) == policy["validator_template_sha256"], "Combined validator template differs")
    historical.check_worktree(repo, current)
    for path, row in current.items():
        require(bool((repo / path).stat().st_mode & 0o111) == (row[0] == "100755"),
                "Working-tree executable mode differs: " + path)
    validate_workflow_migration(repo)
    for raw_name in git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0"):
        name = raw_name.decode("utf-8")
        require(not (name.startswith(("Zeta23/", "research/", ".github/", "docs/examples/")) and
                     name.endswith((".lean", ".lean.in", ".py", ".yml", ".yaml"))),
                "Ignored executable/source provider: " + name)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Checkout changed during inspection")
    require(head == value(repo, "rev-parse", "HEAD"), "HEAD changed during combined source review")
    return {"schema": SCHEMA, "status": "PASS_SOURCE_SCOPE_ONLY", "checked_commit": head,
            "checked_tree": value(repo, "rev-parse", head + "^{tree}"), "base": BASE, "base_tree": BASE_TREE,
            "source_introduction": first, "layout": LAYOUT, "source_parents": [MAIN, PAPER],
            "manifest_sha256": file_hash(repo / MANIFEST), "paper_archive": archive, "path_policy": POLICY_SHA256,
            "delta": delta, "canonical_product_count": len(active), "unchanged_historical_product_count": len(frozen),
            "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED", "current_compiler_accepted": False,
            "full_round4_accepted": False, "proof_acceptance": False, "independent_approval": False,
            "canonical_admission": False, "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN"}


def check_classification(repo=REPO):
    validate_descendant(repo, require_clean=True)
    require(paper.check_classification(), "Inherited paper and historical classification failed")
    classes = load_bytes((repo / paper.CLASSIFICATION_PATH).read_bytes())
    for path in sorted(registration.ADDED | registration.EDITED | ADDED | EDITED):
        first = next((rule for rule in classes["rules"] if re.fullmatch(rule["pattern"], path)), None)
        require(first and first["file_class"] != classes["unknown_class"] and first["trust_zone"] == "AUDIT_ONLY",
                "Unexpected combined audit classification: " + path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-classification", required=True, action="store_true")
    parser.parse_args()
    check_classification()
    print(json.dumps({"schema": SCHEMA, "classification": "PASS_AUDIT_ONLY"}))
