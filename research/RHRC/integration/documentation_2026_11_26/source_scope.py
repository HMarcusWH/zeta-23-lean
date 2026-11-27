"""Authenticate the narrow documentation successor after the November 26 archive."""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import unittest

from .archive_scope import git, inspect_archive, read_policy, tree
from ..documentation_2026_11_21 import source_scope as predecessor
from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import MANIFEST, REPO, validate_workflow_migration
from ..opica_composition.snapshot import file_hash, unlinked


PREFIX = "research/RHRC/integration/documentation_2026_11_26/"
POLICY = PREFIX + "SOURCE_SCOPE.json"
VALIDATOR = PREFIX + "source_scope.py"
POLICY_SHA256 = "187a6cf36c905022dc7a77d54fe9c2e6327af7438db4f4f2fb72d0d09685059b"
SCHEMA = "RHRC_PAPER_DOCUMENTATION_SOURCE_INSPECTION_V1"
POLICY_SCHEMA = "RHRC_PAPER_DOCUMENTATION_CLOSED_SOURCE_POLICY_V1"
CLASSIFICATION_PATH = "research/RHRC/graph/FILE_CLASSES.json"
EDIT_PATHS = {
    ".github/workflows/documentation.yml",
    "research/RHRC/integration/opica_composition/cli.py",
    "research/RHRC/integration/opica_composition/service.py",
    "research/RHRC/integration/opica_composition/tests/test_end_to_end.py",
    CLASSIFICATION_PATH,
}
PYTHON_FILES = {PREFIX + name for name in ("archive_scope.py", "source_scope.py", "test_archive_scope.py",
                                          "test_source_scope.py")}
ADD_PATHS = PYTHON_FILES - {VALIDATOR} | {PREFIX + "ARCHIVE_BYTES.json"}


def policy_from_archive(repo: Path, archive: str) -> dict:
    raw = git(repo, "cat-file", "blob", archive + ":" + predecessor.POLICY)
    require(sha256(raw).hexdigest() == predecessor.POLICY_SHA256, "Changed predecessor policy")
    inherited = load_bytes(raw)
    predecessor.check_policy(inherited)
    return inherited


def classify(parent: dict, current: dict, policy: dict, allowed_generated: set[str]) -> dict:
    require(set(policy) == {"schema", "added", "edited", "validator_template_sha256"} and
            policy["schema"] == POLICY_SCHEMA, "Unexpected November 26 source policy")
    require(set(policy["added"]) == ADD_PATHS and set(policy["edited"]) == EDIT_PATHS,
            "Paper successor policy path inventory differs")
    added = current.keys() - parent.keys()
    require(added == ADD_PATHS | {POLICY, VALIDATOR},
            "Unexpected paper successor additions: " + repr(sorted(added ^ (ADD_PATHS | {POLICY, VALIDATOR}))))
    require(parent.keys() <= current.keys(), "Paper successor removed or renamed an archived path")
    edited = {name for name in parent if parent[name] != current[name]}
    generated = edited & allowed_generated
    require(edited - generated == EDIT_PATHS, "Unexpected paper successor edits: " +
            repr(sorted((edited - generated) ^ EDIT_PATHS)))
    validate_path_inventory(sorted(added | edited))
    require(all(current[path][:2] == ("100644", "blob") for path in added | edited),
            "Paper successor path changed type or mode")
    for path, blob in {**policy["added"], **policy["edited"]}.items():
        require(current[path] == ("100644", "blob", blob), "Changed reviewed paper successor blob: " + path)
    return {"added": sorted(added), "edited": sorted(EDIT_PATHS), "generated": sorted(generated), "deleted": []}


def inspect_committed_tree(repo: Path = REPO) -> dict:
    repo = unlinked(repo).resolve()
    head = git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    current = tree(repo, head)
    require(current.get(POLICY, ())[:2] == ("100644", "blob"), "No committed November 26 source policy")
    raw = git(repo, "cat-file", "blob", current[POLICY][2])
    require(sha256(raw).hexdigest() == POLICY_SHA256, "November 26 policy digest differs")
    policy = load_bytes(raw)

    archive = inspect_archive(repo, read_policy())
    boundary = archive["archive_commit"]
    git(repo, "merge-base", "--is-ancestor", boundary, head)
    inherited = policy_from_archive(repo, boundary)
    allowed_generated = set(inherited["generated"])
    require(len(allowed_generated) == 77 and allowed_generated.isdisjoint(predecessor.round6.FROZEN_PRODUCTS),
            "Inherited canonical product inventory differs")
    delta = classify(tree(repo, boundary), current, policy, allowed_generated)
    validator = git(repo, "cat-file", "blob", current[VALIDATOR][2])
    observed_hash = predecessor.round6.validator_template_hash(validator, POLICY_SHA256)
    require(observed_hash == policy["validator_template_sha256"], "Changed November 26 validator template")
    require(head == git(repo, "rev-parse", "HEAD").decode("ascii").strip(), "HEAD changed during scope review")
    return {
        "schema": SCHEMA,
        "status": "PASS_COMMITTED_TREE_SCOPE_ONLY",
        "checked_commit": head,
        "checked_tree": git(repo, "rev-parse", head + "^{tree}").decode("ascii").strip(),
        "base": archive["base_commit"],
        "base_tree": archive["base_tree"],
        "paper_archive_commit": boundary,
        "paper_archive_tree": archive["archive_tree"],
        "paper_archive": archive,
        "path_policy": POLICY_SHA256,
        "validator_blob": current[VALIDATOR][2],
        "delta": delta,
        "canonical_product_count": 77,
        "unchanged_historical_product_count": 4,
        "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED",
        "current_compiler_accepted": False,
        "full_round4_accepted": False,
        "successor_human_review": "PENDING",
        "RH": "OPEN",
        "Step4": "OPEN",
    }


def validate_descendant(repo: Path = REPO, *, require_clean: bool = False) -> dict:
    repo = unlinked(repo).resolve()
    if POLICY not in tree(repo, "HEAD"):
        return predecessor.validate_descendant(repo, require_clean=require_clean)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Dirty paper checkout")
    result = inspect_committed_tree(repo)
    predecessor.check_worktree(repo, tree(repo, result["checked_commit"]))
    validate_workflow_migration(repo)
    for item in git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0"):
        name = item.decode("utf-8")
        require(not (name.startswith(("Zeta23/", "research/", ".github/", "docs/examples/")) and
                     name.endswith((".lean", ".lean.in", ".py", ".yml", ".yaml"))),
                "Ignored executable/source provider: " + name)
    require(result["checked_commit"] == git(repo, "rev-parse", "HEAD").decode("ascii").strip(),
            "HEAD changed during worktree inspection")
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Checkout changed during inspection")
    result["status"] = "PASS_SOURCE_SCOPE_ONLY"
    result["manifest_sha256"] = file_hash(repo / MANIFEST)
    return result


def classification_rules() -> list[dict]:
    def rule(identity: str, paths: set[str], file_class: str) -> dict:
        return {"id": identity, "pattern": r"\A(?:" + "|".join(re.escape(path) for path in sorted(paths)) + r")\Z",
                "file_class": file_class, "trust_zone": "AUDIT_ONLY"}

    pdfs = {path for path, item in read_policy()["added"].items() if item["file_kind"] == "BINARY_PDF"}
    return [rule("research_archive_2026_11_26_papers", pdfs, "RESEARCH_FIXTURE"),
            rule("documentation_2026_11_26_scope", PYTHON_FILES, "RESEARCH_EXECUTABLE")]


def check_classification() -> bool:
    from ..opica_round2.tests.test_file_classes import ExactRound2FileClasses

    inherited = policy_from_archive(REPO, read_policy()["archive_commit"])
    extra = classification_rules() + predecessor.documentation_classification_rules(inherited)

    class ExactPaperDocumentationClasses(ExactRound2FileClasses):
        @classmethod
        def setUpClass(cls):
            super().setUpClass()
            require(cls.classes["rules"][:len(extra)] == extra, "Paper and predecessor classification prefix differs")
            roles = {"Zeta23.OPICARound5.ParityMomentBridge": "OPICA5_PARITY_SEED_FORMAL_SUPPORT",
                     **predecessor.round6.ROLES}
            require(cls.round4 and cls.round4_roles.keys().isdisjoint(roles), "Inherited source roles overlap")
            require(all(cls.modules.get(name) == name.replace(".", "/") + ".lean" for name in roles),
                    "Exact inherited source subjects required")
            cls.round4_roles = {**cls.round4_roles, **roles}
            cls.round4_rules = extra + cls.round4_rules

    return unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(
        ExactPaperDocumentationClasses)).wasSuccessful()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-tree", action="store_true")
    mode.add_argument("--check-classification", action="store_true")
    args = parser.parse_args()
    if args.check_classification:
        return 0 if check_classification() else 1
    result = inspect_committed_tree() if args.check_tree else validate_descendant(require_clean=True)
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
