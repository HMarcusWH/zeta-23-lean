"""Authenticate the exact direct-window candidate without granting proof authority.

This is a separate successor to the pinned strict-source repair. Historical
source policies are replayed on their own commits, never widened to accept the
new proof route. A policy refresh seals the explicitly listed current files;
it cannot add a path to the authorized inventory.
"""

from __future__ import annotations

import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import re

from ...graph.views import reachability_view
from ...tools.lean_imports import import_modules
from ..documentation_2026_11_26.archive_scope import git, tree
from ..opica_composition.canonical import load_bytes, require
from ..opica_composition.descendant import preserve_documentation_renderer
from . import source_scope as combined
from . import strict_scope

BASE = "3aefdaa46a4a16c5fd9978b9cf65b251c38ca2c1"
BASE_TREE = "388cc6faa6a37bafa10538679bed54e978f1716b"
SCHEMA = "RHRC_DIRECT_WINDOW_SOURCE_INSPECTION_V1"
POLICY_SCHEMA = "RHRC_DIRECT_WINDOW_SOURCE_POLICY_V1"
POLICY_SHA256 = "dcc797bd1c9cdbdd131d7b143908aaed7dd2f5cb061f5542464c17f493213b2e"
POLICY = combined.PREFIX + "DIRECT_WINDOW_SCOPE.json"
VALIDATOR = combined.PREFIX + "direct_window_scope.py"
TEST = combined.PREFIX + "test_direct_window_scope.py"
CLASSES = "research/RHRC/graph/FILE_CLASSES.json"
SEMANTICS = "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json"
VERIFICATION = "verification/direct-arithmetic-window/"
WORKFLOW = ".github/workflows/direct-arithmetic-window-review.yml"

# These names are an exact source inventory, not directory-prefix permissions.
MATH_ROLES = {
    "Zeta23WindowArithmetic/ProvedInputs.lean": "DIRECT_ARITHMETIC_WINDOW_PROVED_INPUTS",
    "Zeta23WindowArithmetic/PrincipalNormalization.lean": "DIRECT_ARITHMETIC_WINDOW_PRINCIPAL_NORMALIZATION",
    "Zeta23WindowArithmetic/WindowExtraction.lean": "DIRECT_ARITHMETIC_WINDOW_EXTRACTION",
    "Zeta23WindowArithmetic/PrincipalWindowSupply.lean": "DIRECT_ARITHMETIC_WINDOW_SUPPLIER",
    "Zeta23/RHReference/DirectWindowContract.lean": "DIRECT_ARITHMETIC_WINDOW_CONTRACT",
    "Zeta23/RHReference/DirectWindowSource.lean": "DIRECT_ARITHMETIC_WINDOW_LITERAL_NORMALIZATION",
    "Zeta23/RHReference/DirectWindowEnergy.lean": "DIRECT_ARITHMETIC_WINDOW_ENERGY_TRANSFER",
    "Zeta23/RHReference/CofinalEnergyClosure.lean": "DIRECT_ARITHMETIC_WINDOW_COFINAL_CONSUMER",
    "Zeta23/RHReference/DirectWindowAdapter.lean": "DIRECT_ARITHMETIC_WINDOW_TERMINAL_SOURCE",
}
CHECKER_FIXTURES = {VERIFICATION + name for name in (
    "AuditCore.lean", "AuditSupplier.lean", "AuditNative.lean", "AuditTerminal.lean",
    "Expected.lean", "SmokeFixtures.lean", "AuditSmoke.lean",
    "comparator/DirectWindowChallenge.lean", "comparator/DirectWindowSolution.lean",
)}
CHECKER_SCRIPTS = {VERIFICATION + name for name in (
    "stage.py", "run.py", "evidence.py", "controls.py", "acquire.sh", "cleanup_completed.py",
)}
CHECKER_CONFIG = {VERIFICATION + name for name in (
    "SOURCE_LOCK.json", "OWNERSHIP.json", "COMPATIBILITY.json", "ROOTS.json",
    "epoch-lean-4.33.1/lean-toolchain", "epoch-lean-4.33.1/lakefile.toml",
    "epoch-lean-4.33.1/lake-manifest.json", "comparator/config.json",
)}
# Every subsequently required compatibility overlay must be named here and
# resealed in the policy. An empty set admits no overlay files.
COMPATIBILITY_OVERLAYS: set[str] = set()
DOCUMENTS = {"docs/direct-arithmetic-window.md", VERIFICATION + "README.md"}
ADDED = (set(MATH_ROLES) | CHECKER_FIXTURES | CHECKER_SCRIPTS | CHECKER_CONFIG |
         COMPATIBILITY_OVERLAYS | DOCUMENTS | {WORKFLOW, POLICY, VALIDATOR, TEST})
EDITED = {"README.md", combined.WORKFLOW, combined.CLI, CLASSES, SEMANTICS,
          "research/RHRC/graph/build.py"}


def exact_rules():
    groups = (
        ("mathematics", set(MATH_ROLES), "LEAN_SOURCE", "AUXILIARY_FORMALIZATION"),
        ("checker_inputs", CHECKER_FIXTURES | COMPATIBILITY_OVERLAYS,
         "RESEARCH_FIXTURE", "AUDIT_ONLY"),
        ("tools", CHECKER_SCRIPTS | {VALIDATOR, TEST}, "RESEARCH_EXECUTABLE", "AUDIT_ONLY"),
        ("manifests", CHECKER_CONFIG | {POLICY}, "EXTERNAL_SOURCE_MANIFEST", "AUDIT_ONLY"),
        ("documentation", DOCUMENTS, "DOCUMENTATION", "AUDIT_ONLY"),
        ("workflow", {WORKFLOW}, "CI_WORKFLOW", "AUDIT_ONLY"),
    )
    require(set().union(*(paths for _, paths, _, _ in groups)) == ADDED,
            "Direct-window file dispositions do not cover the exact addition set")
    return [{"id": "direct_arithmetic_window_" + name,
             "pattern": r"\A(?:" + "|".join(re.escape(p) for p in sorted(paths)) + r")\Z",
             "file_class": file_class, "trust_zone": trust_zone}
            for name, paths, file_class, trust_zone in groups if paths]


def expected_classification(repo):
    old_classes = load_bytes(git(repo, "show", BASE + ":" + CLASSES))
    old_semantics = load_bytes(git(repo, "show", BASE + ":" + SEMANTICS))
    roles = {path.removesuffix(".lean").replace("/", "."): role
             for path, role in MATH_ROLES.items()}
    require(not roles.keys() & old_semantics["standalone_module_roles"].keys(),
            "Direct-window module name duplicates a historical role")
    # Exact rules come first so existing broad descriptive rules cannot hide an
    # omitted disposition. They match no historical path.
    classes = {**old_classes, "rules": exact_rules() + old_classes["rules"]}
    semantics = {**old_semantics, "standalone_module_roles":
                 {**old_semantics["standalone_module_roles"], **roles}}
    return classes, semantics


def classify(base, current, active, policy):
    require(set(policy) == {"schema", "blobs", "validator_template_sha256"} and
            policy["schema"] == POLICY_SCHEMA and
            set(policy["blobs"]) == (ADDED | EDITED) - {POLICY, VALIDATOR},
            "Invalid exact direct-window source inventory")
    require(ADDED.isdisjoint(base) and EDITED <= base.keys() and
            active.isdisjoint(ADDED | EDITED), "Overlapping source/product dispositions")
    require(current.keys() == base.keys() | ADDED,
            "Missing, extra, deleted or renamed direct-window source path")
    changed = {p for p in base if current[p] != base[p]}
    require(changed - active == EDITED,
            "Unexpected authored source delta: " + repr(sorted((changed - active) ^ EDITED)))
    require(all(current[p][:2] == combined.REGULAR for p in ADDED | changed),
            "Direct-window source mode or object kind differs")
    for path, blob in policy["blobs"].items():
        require(current[path] == (*combined.REGULAR, blob),
                "Different sealed direct-window source bytes: " + path)
    return {"added": sorted(ADDED), "edited": sorted(EDITED),
            "generated": sorted(changed & active), "deleted": []}


def baseline(repo):
    require(combined.value(repo, "rev-parse", BASE + "^{tree}") == BASE_TREE,
            "Unexpected strict-repair base tree")
    base = tree(repo, BASE)
    archive = combined.inspect_archive(repo, combined.read_policy())
    active = set(combined.paper.policy_from_archive(repo, archive["archive_commit"])["generated"])
    frozen = set(combined.historical.round6.FROZEN_PRODUCTS)
    rows = load_bytes(git(repo, "show", BASE + ":" + combined.MANIFEST))["generated"]
    require(len(rows) == 81 and len(active) == 77 and len(frozen) == 4 and
            active.isdisjoint(frozen) and {r["path"] for r in rows} == active | frozen,
            "Inherited canonical product boundary differs")
    strict_base, _ = strict_scope.import_baseline(repo)
    raw = git(repo, "show", BASE + ":" + strict_scope.POLICY)
    require(sha256(raw).hexdigest() == strict_scope.POLICY_SHA256,
            "Pinned strict policy changed")
    policy = load_bytes(raw)
    strict_scope.classify(strict_base, base, base, active, policy)
    require(combined.historical.round6.validator_template_hash(
        git(repo, "show", BASE + ":" + strict_scope.VALIDATOR), strict_scope.POLICY_SHA256)
        == policy["validator_template_sha256"], "Pinned strict validator changed")
    return base, active, archive


def validate_descendant(repo=combined.REPO, *, require_clean=False):
    repo = combined.unlinked(repo).resolve()
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Dirty direct-window source checkout")
    head = combined.value(repo, "rev-parse", "HEAD")
    git(repo, "merge-base", "--is-ancestor", BASE, head)
    base, active, archive = baseline(repo)
    current = tree(repo, head)
    require(current.get(POLICY, ())[:2] == combined.REGULAR,
            "Missing direct-window source policy")
    raw = git(repo, "cat-file", "blob", current[POLICY][2])
    require(sha256(raw).hexdigest() == POLICY_SHA256,
            "Direct-window policy digest differs; review and explicitly reseal the exact candidate")
    policy = load_bytes(raw)
    delta = classify(base, current, active, policy)
    require(combined.historical.round6.validator_template_hash(
        git(repo, "cat-file", "blob", current[VALIDATOR][2]), POLICY_SHA256)
        == policy["validator_template_sha256"], "Direct-window validator template differs")
    preserve_documentation_renderer(git(repo, "cat-file", "blob", current["README.md"][2]),
                                   git(repo, "cat-file", "blob", base["README.md"][2]), path="README.md")
    combined.historical.check_worktree(repo, current)
    for path, row in current.items():
        require(bool((repo / path).stat().st_mode & 0o111) == (row[0] == "100755"),
                "Working-tree mode differs: " + path)
    combined.validate_workflow_migration(repo)
    protected = ("Zeta23/", "Zeta23Arithmetic/", "Zeta23WindowArithmetic/",
                 "verification/", "research/", ".github/", "docs/examples/")
    for raw_path in git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0"):
        path = raw_path.decode()
        require(not (path.startswith(protected) and
                     path.endswith((".lean", ".lean.in", ".py", ".sh", ".yml", ".yaml"))),
                "Ignored source or executable provider: " + path)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Checkout changed during direct-window inspection")
    require(head == combined.value(repo, "rev-parse", "HEAD"), "HEAD changed during source inspection")
    return {"schema": SCHEMA, "status": "PASS_SOURCE_SCOPE_ONLY", "checked_commit": head,
            "checked_tree": combined.value(repo, "rev-parse", head + "^{tree}"),
            "base": BASE, "base_tree": BASE_TREE, "path_policy": POLICY_SHA256,
            "manifest_sha256": combined.file_hash(repo / combined.MANIFEST),
            "delta": delta, "paper_archive": archive, "canonical_product_count": len(active),
            "unchanged_historical_product_count": 4,
            "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED",
            "current_compiler_accepted": False, "full_round4_accepted": False,
            "proof_acceptance": False, "independent_approval": False, "canonical_admission": False,
            "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN"}


def check_classification(repo=combined.REPO):
    repo = Path(repo)
    validate_descendant(repo, require_clean=True)
    expected_classes, expected_semantics = expected_classification(repo)
    require(load_bytes((repo / CLASSES).read_bytes()) == expected_classes,
            "Exact direct-window file classes or historical rules differ")
    require(load_bytes((repo / SEMANTICS).read_bytes()) == expected_semantics,
            "Exact direct-window standalone roles or historical roles differ")
    rules = [(re.compile(r["pattern"]), r["file_class"]) for r in expected_classes["rules"]]
    modules = {}
    for path in tree(repo, "HEAD"):
        file_class = next((kind for pattern, kind in rules if pattern.search(path)), None)
        require(file_class is not None and file_class != expected_classes["unknown_class"],
                "Unclassified tracked path: " + path)
        if file_class in ("LEAN_ROOT", "LEAN_SOURCE"):
            require(path == "Zeta23.lean" or
                    path.startswith(("Zeta23/", "Zeta23Arithmetic/", "comparator/")) or
                    path in MATH_ROLES, "Unexpected local module root: " + path)
            name = path.removeprefix("comparator/").removesuffix(".lean").replace("/", ".")
            require(name not in modules, "Duplicate local Lean module: " + name)
            modules[name] = path
    imports = {name: import_modules((repo / path).read_text(encoding="utf-8"))
               for name, path in modules.items()}
    comparators = [name for name, path in modules.items()
                   if path.startswith("comparator/") and path.count("/") == 1]
    standalone = set(reachability_view(imports, comparators)["standalone_or_auxiliary"])
    require(standalone == expected_semantics["standalone_module_roles"].keys(),
            "Standalone census differs from the exact historical plus direct-window roles")
    return {"schema": SCHEMA, "classification": "PASS", "new_paths": len(ADDED),
            "new_mathematics_modules": len(MATH_ROLES), "terminal_claim": "RH_OPEN"}


def refresh_policy(repo=combined.REPO):
    """Explicit authoring operation: seal bytes only for the named candidate paths."""
    repo = Path(repo).resolve()
    base, active, _ = baseline(repo)
    names = {p.decode() for p in git(repo, "ls-files", "-z", "--cached", "--others",
                                    "--exclude-standard").split(b"\0") if p}
    require(names == base.keys() | ADDED,
            "Cannot seal an incomplete or extra path inventory: " + repr(sorted(names ^ (base.keys() | ADDED))))
    classes, semantics = expected_classification(repo)
    for path, value in ((CLASSES, classes), (SEMANTICS, semantics)):
        (repo / path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    changed = {p.decode() for p in git(repo, "diff", "--no-ext-diff", "--no-renames",
                                      "--name-only", "-z", BASE, "--").split(b"\0") if p}
    require(changed <= ADDED | EDITED | active,
            "Cannot seal a protected-source edit: " + repr(sorted(changed - ADDED - EDITED - active)))
    # This authoring helper need not load the preserved binary archive into
    # memory. The committed acceptance gate still checks the complete worktree.
    raw_files = {p: combined.unlinked(repo / p).read_bytes() for p in ADDED | EDITED | changed}
    blobs = {p: sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
             for p, raw in raw_files.items()}
    current = {**base, **{p: ("100755" if (repo / p).stat().st_mode & 0o111 else "100644", "blob", blob)
                         for p, blob in blobs.items()}}
    policy = {"schema": POLICY_SCHEMA,
              "blobs": {p: blobs[p] for p in sorted((ADDED | EDITED) - {POLICY, VALIDATOR})},
              "validator_template_sha256": combined.historical.round6.validator_template_hash(
                  raw_files[VALIDATOR], POLICY_SHA256)}
    classify(base, current, active, policy)
    raw = (json.dumps(policy, sort_keys=True, indent=2) + "\n").encode()
    digest = sha256(raw).hexdigest()
    validator = raw_files[VALIDATOR].replace(
        ('POLICY_SHA256 = "' + POLICY_SHA256 + '"\n').encode(),
        ('POLICY_SHA256 = "' + digest + '"\n').encode())
    (repo / POLICY).write_bytes(raw)
    (repo / VALIDATOR).write_bytes(validator)
    return {"schema": POLICY_SCHEMA, "sealed_policy_sha256": digest,
            "added_paths": len(ADDED), "edited_paths": len(EDITED),
            "acceptance": "AUTHORING_ONLY_COMMIT_AND_RUN_SOURCE_CHECKS"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=combined.REPO)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--check-classification", action="store_true")
    modes.add_argument("--refresh-policy", action="store_true")
    args = parser.parse_args()
    result = (refresh_policy(args.repo) if args.refresh_policy else
              check_classification(args.repo) if args.check_classification else
              validate_descendant(args.repo, require_clean=True))
    print(json.dumps(result, sort_keys=True, indent=2))
