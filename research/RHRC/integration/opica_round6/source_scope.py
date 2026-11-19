"""Authenticate the exact research successor before live Round 4 workers consume it."""
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
import unittest
from pathlib import Path

from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import AUDITED_PATH_POLICY, MANIFEST, REPO, validate_workflow_migration
from ..opica_composition.post299 import descendant as post299
from ..opica_composition.snapshot import file_hash, unlinked

PARENT = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
PARENT_TREE = "573cda1f06d2d7a0e61349a53183311e4ba621fc"
PREFIX = "research/RHRC/integration/opica_round6/"
VALIDATOR = PREFIX + "source_scope.py"
POLICY = PREFIX + "SOURCE_SCOPE.json"
POLICY_SHA256 = "4ee97c0595dcc590af1b231f7babcb4f61053f987f6caa833f84b47d6b14127f"
SHA1 = re.compile("[0-9a-f]{40}\\Z")
SHA256 = re.compile("[0-9a-f]{64}\\Z")
FROZEN_PRODUCTS = {
    "research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl",
    "research/RHRC/ffbbp/generated/history/RHKG_CANDIDATE_REDUCTION_ASSURANCE_v1_PR265.json",
    "research/RHRC/ool/generated/history/RHKG_OOL_PHASE_ATLAS_v1_PR266.json",
    "research/RHRC/ool/generated/history/RHKG_OOL_ROUTE_CONTACTS_v1_PR266.jsonl",
}
ROLES = {
    "Zeta23.OPICARound6.PrimeFactorPaths." + name:
        ("OPICA6_FINITE_ARITHMETIC_AUDIT" if name == "Verify" else "OPICA6_FINITE_ARITHMETIC_SUPPORT")
    for name in (
        "DivisorStrip", "FactorialKnot", "FinitePairKernel", "FiniteRenewal",
        "FiniteSelectorEnergy", "FiniteWeightedGram", "PrimeAreaIntegral",
        "PrimitiveEulerMultiplier", "RoughNodeCharges", "SquarefreePrimeCost",
        "StoppedPrimeArea", "TwoShellCalibration", "Verify",
    )
}


def git(repo, *args, data=None):
    return subprocess.check_output(["git", "-C", str(repo), *args], input=data)


def tree(repo, rev):
    rows = {}
    for item in git(repo, "ls-tree", "-rz", "--full-tree", rev).split(b"\0"):
        if item:
            header, raw = item.split(b"\t", 1)
            mode, kind, blob = header.decode("ascii").split()
            rows[raw.decode("utf-8")] = (mode, kind, blob)
    return rows


def check_policy(policy):
    require(type(policy) is dict and set(policy) == {"schema", "parent", "parent_tree",
            "validator_template_sha256", "added", "edited", "generated"}, "Unexpected Round 6 policy fields")
    require(policy["schema"] == "OPICA6_CLOSED_SOURCE_POLICY_V1"
            and (policy["parent"], policy["parent_tree"]) == (PARENT, PARENT_TREE),
            "Incorrect Round 6 policy parent or schema")
    for field in ("added", "edited"):
        require(type(policy[field]) is dict and all(isinstance(v, str) and SHA1.fullmatch(v)
                for v in policy[field].values()), "Unpinned Round 6 source: " + field)
    products = policy["generated"]
    require(isinstance(policy["validator_template_sha256"], str) and
            SHA256.fullmatch(policy["validator_template_sha256"]), "Missing reviewed validator template")
    require(type(products) is list and products == sorted(set(products)),
            "Generated names must be unique and sorted")
    require(all(p.startswith(post299.GENERATED_ROOTS) and p.endswith((".json", ".jsonl"))
                for p in products), "Unrecognized canonical generated product")
    require(FROZEN_PRODUCTS.isdisjoint([*products, *policy["edited"]]),
            "Immutable historical product included in Round 6 modifications")
    paths = [*policy["added"], *policy["edited"], *products, POLICY, VALIDATOR]
    require(len(paths) == len(set(paths)), "Overlapping Round 6 operations")
    validate_path_inventory(paths)


def validator_template_hash(raw: bytes, policy_pin: str) -> str:
    """Bind the validator's complete Git bytes while breaking its one digest cycle."""
    lines = raw.splitlines(keepends=True)
    definition = ('POLICY_SHA256 = "' + policy_pin + '"\n').encode("ascii")
    require(lines.count(definition) == 1, "Validator must contain exactly the reviewed policy pin")
    lines[lines.index(definition)] = b'POLICY_SHA256 = "<policy-sha256>"\n'
    return hashlib.sha256(b"".join(lines)).hexdigest()


def classify(parent, current, policy):
    """Compare Git modes and blob IDs, charging every changed tree entry."""
    check_policy(policy)
    added = set(current) - set(parent)
    expected_added = set(policy["added"]) | {POLICY, VALIDATOR}
    require(added == expected_added, "Round 6 added paths differ: " +
            repr(sorted(added ^ expected_added)))
    require(set(parent) <= set(current), "Round 6 deleted or renamed a parent path")
    edited = {name for name in parent if parent[name] != current[name]}
    expected_edits = set(policy["edited"])
    products = set(policy["generated"])
    require(products <= set(parent), "Canonical product missing from authenticated parent")
    require(all(parent[name][:2] == ("100644", "blob") for name in products),
            "Canonical product lacks ordinary parent blob")
    generated = edited & products
    require(edited - generated == expected_edits, "Round 6 modified paths differ: " +
            repr(sorted((edited - generated) ^ expected_edits)))
    for name in sorted(added | edited):
        require(current[name][:2] == ("100644", "blob"), "Nonregular Round 6 source: " + name)
        if name in parent:
            require(parent[name][:2] == current[name][:2], "Round 6 file mode changed: " + name)
    for name, blob in {**policy["added"], **policy["edited"]}.items():
        require(current[name][2] == blob, "Round 6 reviewed source blob changed: " + name)
    return {"added": sorted(added), "edited": sorted(expected_edits),
            "generated": sorted(generated), "deleted": []}


def validate_descendant(repo: Path = REPO, *, require_clean: bool = False) -> dict:
    repo = unlinked(repo).resolve()
    head = post299.git(repo, "rev-parse", "HEAD")
    current = tree(repo, head)
    if POLICY not in current:
        return post299.validate_descendant(repo, require_clean=require_clean)
    require(post299.git(repo, "rev-parse", PARENT + "^{tree}") == PARENT_TREE,
            "Merged Round 5 parent tree differs")
    subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", PARENT, head], check=True)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Dirty Round 6 checkout")
    raw = git(repo, "cat-file", "blob", current[POLICY][2])
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256,
            "Round 6 policy digest differs")
    policy = load_bytes(raw)
    parent = tree(repo, PARENT)
    inherited = load_bytes(git(repo, "cat-file", "blob", parent[MANIFEST][2]))
    products = {row["path"] for row in inherited["generated"]}
    require(len(products) == len(inherited["generated"]) == 81 and FROZEN_PRODUCTS <= products
            and set(policy["generated"]) == products - FROZEN_PRODUCTS,
            "Round 6 canonical inventory differs from the 77 active and four frozen parent products")
    require(all(parent[name] == current.get(name) for name in FROZEN_PRODUCTS),
            "Frozen generated historical subject changed")
    delta = classify(parent, current, policy)
    validator = git(repo, "cat-file", "blob", current[VALIDATOR][2])
    require(validator_template_hash(validator, POLICY_SHA256) == policy["validator_template_sha256"],
            "Round 6 validator differs from reviewed template")
    paths = sorted(delta["added"] + delta["edited"] + delta["generated"])
    for name in paths:
        path = unlinked(repo / name)
        require(path.is_file(), "Missing regular Round 6 subject: " + name)
    # Richer source receipts remain cheap when each independent check binds hundreds of blobs.
    # --stdin-paths reads the same clean-filtered bytes used by Git on this platform.
    blobs = git(repo, "hash-object", "--stdin-paths", data=("\n".join(paths) + "\n").encode()).decode().splitlines()
    require(blobs == [current[name][2] for name in paths], "Round 6 working tree differs from Git")
    validate_workflow_migration(repo)
    ignored = git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0")
    for raw_name in ignored:
        name = raw_name.decode("utf-8")
        if name.startswith(("Zeta23/", "research/", ".github/")) and name.endswith(
                (".lean", ".lean.in", ".py", ".yml", ".yaml")):
            require(False, "Ignored executable/source provider: " + name)
    require(head == post299.git(repo, "rev-parse", "HEAD"), "Round 6 source changed during inspection")
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Round 6 checkout changed during inspection")
    return {
        "schema": "OPICA6_CURRENT_SOURCE_INSPECTION_V1", "status": "PASS_SOURCE_SCOPE_ONLY",
        "checked_commit": head, "checked_tree": post299.git(repo, "rev-parse", head + "^{tree}"),
        "base": PARENT, "base_tree": PARENT_TREE, "historical_v1_source_policy": AUDITED_PATH_POLICY,
        "path_policy": POLICY_SHA256, "manifest_sha256": file_hash(repo / MANIFEST),
        "validator_blob": current[VALIDATOR][2], "delta": delta, "canonical_product_count": 77,
        "unchanged_historical_product_count": 4, "current_compiler_accepted": False,
        "full_round4_accepted": False, "successor_human_review": "PENDING", "RH": "OPEN", "Step4": "OPEN",
    }


def check_classification() -> bool:
    from ..opica_round2.tests.test_file_classes import ExactRound2FileClasses

    class ExactRound6FileClasses(ExactRound2FileClasses):
        @classmethod
        def setUpClass(cls):
            super().setUpClass()
            roles = {"Zeta23.OPICARound5.ParityMomentBridge": "OPICA5_PARITY_SEED_FORMAL_SUPPORT", **ROLES}
            require(cls.round4 and cls.round4_roles.keys().isdisjoint(roles),
                    "Inherited roles overlap the reviewed successors")
            require(all(cls.modules.get(name) == name.replace(".", "/") + ".lean" for name in roles),
                    "Exact successor classification subjects required")
            cls.round4_roles = {**cls.round4_roles, **roles}

    return unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(
        ExactRound6FileClasses)).wasSuccessful()


if __name__ == "__main__":
    if sys.argv[1:] != ["--check-classification"]:
        raise SystemExit("expected --check-classification")
    raise SystemExit(0 if check_classification() else 1)
