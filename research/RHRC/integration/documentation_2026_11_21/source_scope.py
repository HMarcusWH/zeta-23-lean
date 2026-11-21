"""Authenticate the archive and an exact, content-bound documentation successor.

The Round 4, post299 and Round 6 validators remain unchanged. This layer first
replays the Round 6 tree policy at the last research commit, accounts for every
archive operation, then checks the explicitly reviewed documentation delta.
Canonical generated products retain their existing, separate freshness gate.
Passing this module does not establish compiler or mathematical acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unittest

from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import (
    MANIFEST, REPO, preserve_agent_instructions, preserve_documentation_renderer,
    validate_workflow_migration,
)
from ..opica_composition.snapshot import file_hash, unlinked
from ..opica_round6 import source_scope as round6

PARENT = "7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9"
PARENT_TREE = "9248b76d7aff60aab3bb775c4be9750dc6006003"
RESEARCH_PARENT = "3835cc66641fa48d78db932db1d32b57687f728c"
RESEARCH_PARENT_TREE = "f90fe234adcc9ddabe481c6569230cf64bfc98ac"
PREFIX = "research/RHRC/integration/documentation_2026_11_21/"
POLICY = PREFIX + "SOURCE_SCOPE.json"
VALIDATOR = PREFIX + "source_scope.py"
POLICY_SHA256 = "759f99c0248bcf4f192a817062251b3de75badf276372cbb0234de1efa052218"
SCHEMA = "RHRC_DOCUMENTATION_SOURCE_INSPECTION_V1"
POLICY_SCHEMA = "RHRC_DOCUMENTATION_CLOSED_SOURCE_POLICY_V1"


def git(repo: Path, *args: str, data: bytes | None = None) -> bytes:
    return round6.git(repo, *args, data=data)


def blob(repo: Path, rows: dict, name: str) -> bytes:
    require(name in rows and rows[name][:2] == ("100644", "blob"),
            "Expected regular source blob: " + name)
    return git(repo, "cat-file", "blob", rows[name][2])


def check_policy(policy: dict) -> None:
    fields = {"schema", "parent", "parent_tree", "research_parent", "research_parent_tree",
              "validator_template_sha256", "archive_added", "archive_edited",
              "added", "edited", "generated"}
    require(type(policy) is dict and set(policy) == fields, "Unexpected documentation policy fields")
    require((policy["schema"], policy["parent"], policy["parent_tree"],
             policy["research_parent"], policy["research_parent_tree"]) ==
            (POLICY_SCHEMA, PARENT, PARENT_TREE, RESEARCH_PARENT, RESEARCH_PARENT_TREE),
            "Incorrect documentation policy schema or baseline")
    require(isinstance(policy["validator_template_sha256"], str) and
            round6.SHA256.fullmatch(policy["validator_template_sha256"]),
            "Unpinned documentation validator template")
    for field in ("archive_added", "archive_edited", "added", "edited"):
        rows = policy[field]
        require(type(rows) is dict and all(isinstance(value, str) and
                round6.SHA1.fullmatch(value) for value in rows.values()),
                "Unpinned documentation operation: " + field)
        validate_path_inventory(list(rows))
    products = policy["generated"]
    require(type(products) is list and products == sorted(set(products)),
            "Generated names must be unique and sorted")
    validate_path_inventory(products)
    require(all(name.startswith(round6.post299.GENERATED_ROOTS) and
                name.endswith((".json", ".jsonl")) for name in products),
            "Unrecognized canonical generated product")
    require(round6.FROZEN_PRODUCTS.isdisjoint([*products, *policy["edited"]]),
            "Frozen historical product included in documentation modifications")
    paths = [*policy["added"], *policy["edited"], *products, POLICY, VALIDATOR]
    require(len(paths) == len(set(paths)), "Overlapping documentation operations")
    validate_path_inventory(paths)
    require(set(policy["archive_edited"]) == {"README.md"}, "Archive edit inventory differs")
    archive_paths = set(policy["archive_added"])
    nonpapers = {"papers/README.md", "papers/MANIFEST_2026-11-21.json",
                 "docs/RESEARCH_ARCHIVE_2026-11-21.md"}
    require(nonpapers <= archive_paths and len(archive_paths) == 46 and
            all(name.startswith("papers/2026-11-21/") and name.endswith(".pdf")
                for name in archive_paths - nonpapers), "Archive addition inventory differs")


def classify(parent: dict, current: dict, policy: dict) -> dict:
    """Charge every changed tree entry to a named operation and exact blob."""
    check_policy(policy)
    added = set(current) - set(parent)
    require(added == set(policy["added"]) | {POLICY, VALIDATOR},
            "Documentation added paths differ: " + repr(sorted(
                added ^ (set(policy["added"]) | {POLICY, VALIDATOR}))))
    require(set(parent) <= set(current), "Documentation deleted or renamed a parent path")
    edited = {name for name in parent if parent[name] != current[name]}
    products = set(policy["generated"])
    require(products <= set(parent), "Canonical product absent from archive baseline")
    generated = edited & products
    require(edited - generated == set(policy["edited"]),
            "Documentation modified paths differ: " + repr(sorted(
                (edited - generated) ^ set(policy["edited"]))))
    for name in added | edited:
        require(current[name][:2] == ("100644", "blob"), "Nonregular documentation source: " + name)
        if name in parent:
            require(current[name][:2] == parent[name][:2], "Documentation file mode changed: " + name)
    for name, value in {**policy["added"], **policy["edited"]}.items():
        require(current[name][2] == value, "Reviewed documentation blob changed: " + name)
    return {"added": sorted(added), "edited": sorted(policy["edited"]),
            "generated": sorted(generated), "deleted": []}


def check_archive(research: dict, archive: dict, policy: dict) -> None:
    """Verify all 46 additions and the sole README edit at the archive commit."""
    require(set(research) <= set(archive), "Archive deleted research source")
    added = set(archive) - set(research)
    edited = {name for name in research if research[name] != archive[name]}
    require(added == set(policy["archive_added"]) and edited == set(policy["archive_edited"]),
            "Archive delta differs from the recorded research freeze")
    for name, expected in {**policy["archive_added"], **policy["archive_edited"]}.items():
        require(archive[name] == ("100644", "blob", expected), "Archive blob differs: " + name)


def inspect_committed_tree(repo: Path = REPO) -> dict:
    """Read Git objects only. This works in a sparse clone and is not a worktree gate."""
    repo = unlinked(repo).resolve()
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    current = round6.tree(repo, head)
    require(POLICY in current, "Documentation policy absent from committed tree")
    for revision, expected in ((PARENT, PARENT_TREE), (RESEARCH_PARENT, RESEARCH_PARENT_TREE),
                               (round6.PARENT, round6.PARENT_TREE)):
        require(git(repo, "rev-parse", revision + "^{tree}").decode().strip() == expected,
                "Authenticated baseline tree differs: " + revision)
    for older, newer in ((round6.PARENT, RESEARCH_PARENT), (RESEARCH_PARENT, PARENT), (PARENT, head)):
        subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", older, newer], check=True)
    raw = blob(repo, current, POLICY)
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, "Documentation policy digest differs")
    policy = load_bytes(raw)
    check_policy(policy)
    research, archive = round6.tree(repo, RESEARCH_PARENT), round6.tree(repo, PARENT)
    inherited_raw = blob(repo, research, round6.POLICY)
    require(hashlib.sha256(inherited_raw).hexdigest() == round6.POLICY_SHA256,
            "Inherited Round 6 policy digest differs")
    inherited = load_bytes(inherited_raw)
    historical_delta = round6.classify(round6.tree(repo, round6.PARENT), research, inherited)
    require(round6.validator_template_hash(blob(repo, research, round6.VALIDATOR),
            round6.POLICY_SHA256) == inherited["validator_template_sha256"],
            "Historical Round 6 validator template differs")
    require(policy["generated"] == inherited["generated"], "Canonical generated allowance changed")
    baseline_products = {row["path"] for row in load_bytes(blob(repo, archive, MANIFEST))["generated"]}
    require(len(baseline_products) == 81 and baseline_products - round6.FROZEN_PRODUCTS ==
            set(policy["generated"]), "Inherited 77 active / four frozen product inventory differs")
    check_archive(research, archive, policy)
    delta = classify(archive, current, policy)
    require(round6.validator_template_hash(blob(repo, current, VALIDATOR), POLICY_SHA256) ==
            policy["validator_template_sha256"], "Documentation validator template differs")
    for name in policy["edited"]:
        if name.endswith(".md"):
            preserve_documentation_renderer(blob(repo, current, name), blob(repo, archive, name), path=name)
    if "AGENTS.md" in policy["edited"]:
        preserve_agent_instructions(blob(repo, current, "AGENTS.md"), blob(repo, archive, "AGENTS.md"))
    require(head == git(repo, "rev-parse", "HEAD").decode().strip(), "Source changed during tree inspection")
    return {
        "schema": SCHEMA, "status": "PASS_COMMITTED_TREE_SCOPE_ONLY", "checked_commit": head,
        "checked_tree": git(repo, "rev-parse", head + "^{tree}").decode().strip(),
        "base": PARENT, "base_tree": PARENT_TREE, "research_base": RESEARCH_PARENT,
        "research_base_tree": RESEARCH_PARENT_TREE, "path_policy": POLICY_SHA256,
        "validator_blob": current[VALIDATOR][2], "delta": delta,
        "archive_delta": {"added": sorted(policy["archive_added"]), "edited": sorted(policy["archive_edited"])},
        "historical_round6_delta": historical_delta, "canonical_product_count": 77,
        "unchanged_historical_product_count": 4, "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED",
        "current_compiler_accepted": False, "full_round4_accepted": False,
        "successor_human_review": "PENDING", "RH": "OPEN", "Step4": "OPEN",
    }


def check_worktree(repo: Path, current: dict) -> None:
    """Bind every tracked blob, including unchanged source and ignored-index flags."""
    flags = git(repo, "ls-files", "-v", "-z").split(b"\0")
    require(all(not item or (item[:1] != b"S" and not item[:1].islower()) for item in flags),
            "Sparse/skip-worktree or assume-unchanged index state cannot qualify")
    paths = sorted(current)
    for name in paths:
        require(current[name][1] == "blob" and current[name][0] in ("100644", "100755"),
                "Unsupported tracked source object: " + name)
        require(unlinked(repo / name).is_file(), "Missing tracked working-tree subject: " + name)
    hashes = git(repo, "hash-object", "--no-filters", "--stdin-paths",
                 data=("\n".join(paths) + "\n").encode()).decode().splitlines()
    require(hashes == [current[name][2] for name in paths], "Tracked working-tree bytes differ from Git")


def validate_descendant(repo: Path = REPO, *, require_clean: bool = False) -> dict:
    """Production source gate, including the actual governed working-tree bytes."""
    repo = unlinked(repo).resolve()
    current = round6.tree(repo, "HEAD")
    if POLICY not in current:
        return round6.validate_descendant(repo, require_clean=require_clean)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Dirty documentation checkout")
    report = inspect_committed_tree(repo)
    # Unchanged mathematical source and pins matter as much as the new overlay.
    # This rejects incomplete sparse trees and edits hidden from `git status`.
    current = round6.tree(repo, report["checked_commit"])
    check_worktree(repo, current)
    validate_workflow_migration(repo)
    ignored = git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0")
    for raw_name in ignored:
        name = raw_name.decode()
        require(not (name.startswith(("Zeta23/", "research/", ".github/", "docs/examples/")) and
                     name.endswith((".lean", ".lean.in", ".py", ".yml", ".yaml"))),
                "Ignored executable/source provider: " + name)
    require(report["checked_commit"] == git(repo, "rev-parse", "HEAD").decode().strip(),
            "Source changed during working-tree inspection")
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Checkout changed during inspection")
    report["status"] = "PASS_SOURCE_SCOPE_ONLY"
    report["manifest_sha256"] = file_hash(repo / MANIFEST)
    return report


def documentation_classification_rules(policy: dict) -> list[dict]:
    """Four exact additional rules; all inherited rules and roles stay ordered."""
    def rule(identity: str, paths: list[str], file_class: str) -> dict:
        return {"id": identity, "pattern": r"\A(?:" + "|".join(
            re.escape(path) for path in sorted(paths)) + r")\Z",
            "file_class": file_class, "trust_zone": "AUDIT_ONLY"}
    return [
        rule("documentation_2026_11_21_examples", ["docs/examples/exact_examples.py",
             "docs/examples/infrastructure_replay.py"], "RESEARCH_EXECUTABLE"),
        rule("documentation_2026_11_21_scope", [PREFIX + name for name in
             ("__init__.py", "source_scope.py", "test_source_scope.py", "check_documentation.py")],
             "RESEARCH_EXECUTABLE"),
        rule("research_archive_2026_11_21_papers", [name for name in policy["archive_added"]
             if name.endswith(".pdf")], "DOCUMENTATION"),
        rule("research_snapshot_citation", ["CITATION.cff"], "LICENSE_OR_METADATA"),
    ]


def check_classification() -> bool:
    """Retain the complete inherited assertions with the named documentation prefix."""
    from ..opica_round2.tests.test_file_classes import ExactRound2FileClasses
    raw = (REPO / POLICY).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, "Classification policy digest differs")
    policy = load_bytes(raw)
    check_policy(policy)
    extra = documentation_classification_rules(policy)

    class ExactDocumentationFileClasses(ExactRound2FileClasses):
        @classmethod
        def setUpClass(cls):
            super().setUpClass()
            require(cls.classes["rules"][:len(extra)] == extra,
                    "Exact documentation classification prefix differs")
            roles = {"Zeta23.OPICARound5.ParityMomentBridge": "OPICA5_PARITY_SEED_FORMAL_SUPPORT",
                     **round6.ROLES}
            require(cls.round4 and cls.round4_roles.keys().isdisjoint(roles),
                    "Inherited classification roles overlap the research successors")
            require(all(cls.modules.get(name) == name.replace(".", "/") + ".lean" for name in roles),
                    "Exact Round 5/6 classification subjects required")
            cls.round4_roles = {**cls.round4_roles, **roles}
            # The inherited equality test still compares the entire ordered list;
            # no old assertion is removed or replaced by a prefix-only check.
            cls.round4_rules = extra + cls.round4_rules

    return unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(
        ExactDocumentationFileClasses)).wasSuccessful()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="check committed policy and clean governed worktree")
    mode.add_argument("--check-tree", action="store_true", help="inspect committed Git objects only; sparse-clone review")
    mode.add_argument("--check-classification", action="store_true", help="check exact added rules and inherited research classifications")
    args = parser.parse_args()
    if args.check_classification:
        return 0 if check_classification() else 1
    result = inspect_committed_tree() if args.check_tree else validate_descendant(require_clean=True)
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
