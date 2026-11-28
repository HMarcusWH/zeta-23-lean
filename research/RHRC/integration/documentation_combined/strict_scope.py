"""Verify main's strict proof import and its reviewed CI repair against their Git objects."""

import argparse
from hashlib import sha256
import json

from ..documentation_2026_11_26.archive_scope import git, tree
from ..opica_composition.canonical import load_bytes, require
from ..opica_composition.descendant import preserve_documentation_renderer
from . import source_scope as combined

PREVIOUS = "4044e7335bc0499d77d6961a1bc20bdf46283224"
PREVIOUS_TREE = "ae4823637a0c946edc3eb681807cfda087b18e70"
STRICT = "75c200a9c90f96c5b67e468afd1d8a3afeda4188"
STRICT_TREE = "407055394277264c2a804ba42c2413fc375cea87"
INTEGRATION = "a13885dbdf6660740bd3e8933ed61e7a5cbfc34d"
BASE = "d649f57310bb05a306d3d488ba019e4ab45b0b20"
BASE_TREE = "898318555883631fc1b8ffa0f2480e3360b2df9d"
SCHEMA = "RHRC_STRICT_MAIN_SOURCE_INSPECTION_V1"
POLICY_SCHEMA = "RHRC_STRICT_MAIN_SOURCE_POLICY_V1"
POLICY_SHA256 = "c3db5c050852ebedfd2498f674fd688ca1c49ae7ac1fd99fa5609d07c42d5bfe"
POLICY = combined.PREFIX + "STRICT_SCOPE.json"
VALIDATOR = combined.PREFIX + "strict_scope.py"
ADDED = {POLICY, VALIDATOR, combined.PREFIX + "test_strict_scope.py", combined.PREFIX + "strict_classification.py"}
EDITED = {combined.WORKFLOW, combined.CLI, "README.md", ".github/actions/opica4-runtime/action.yml",
          "research/RHRC/graph/FILE_CLASSES.json", "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json",
          "research/RHRC/graph/build.py"}


def check_import(previous, strict, base):
    require(previous.keys() <= base.keys() and all(base[p] == row for p, row in previous.items()),
            "Strict integration removed or changed an existing main file")
    paths = base.keys() - previous.keys()
    require(len(paths) == 952 and all(base[p] == strict.get(p) and base[p][:2] == combined.REGULAR for p in paths),
            "Strict import census or original producer blob/mode differs")
    return paths


def import_baseline(repo):
    for commit, digest in ((PREVIOUS, PREVIOUS_TREE), (STRICT, STRICT_TREE), (INTEGRATION, BASE_TREE), (BASE, BASE_TREE)):
        require(combined.value(repo, "rev-parse", commit + "^{tree}") == digest, "Unexpected tree at " + commit)
    for commit, parents in ((INTEGRATION, [STRICT, PREVIOUS]), (BASE, [PREVIOUS, INTEGRATION])):
        require(combined.value(repo, "show", "-s", "--format=%P", commit).split() == parents,
                "Unexpected parent identities at " + commit)
    previous, strict, base = (tree(repo, ref) for ref in (PREVIOUS, STRICT, BASE))
    imported = check_import(previous, strict, base)
    return base, imported


def classify(base, current, initial, active, policy):
    require(set(policy) == {"schema", "blobs", "validator_template_sha256"} and policy["schema"] == POLICY_SCHEMA
            and set(policy["blobs"]) == (EDITED | ADDED) - {POLICY, VALIDATOR}, "Invalid approved source inventory")
    require(not active.intersection(ADDED | EDITED), "Authored file also registered as a generated product")
    expected = base.keys() | ADDED
    require(current.keys() == expected and initial.keys() == expected, "Missing, added, or renamed source file")
    require(all(initial[p] == base[p] for p in base.keys() - EDITED), "Unreviewed change in source introduction")
    require(all(initial[p] != base[p] for p in EDITED), "Missing approved authored edit")
    require(all(current[p] == initial[p] and current[p][:2] == combined.REGULAR for p in ADDED | EDITED),
            "Authored source changed after its introduction")
    for p, blob in policy["blobs"].items():
        require(current[p] == (*combined.REGULAR, blob), "Different reviewed source bytes: " + p)
    changed = sorted(p for p in base if p not in EDITED and current[p] != base[p])
    require(all(p in active and current[p][:2] == base[p][:2] == combined.REGULAR for p in changed),
            "Protected source, mode, archive or frozen product changed")
    return {"added": sorted(ADDED), "edited": sorted(EDITED), "deleted": [], "generated": changed}


def validate_descendant(repo=combined.REPO, *, require_clean=False):
    repo = combined.unlinked(repo).resolve()
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Dirty strict source checkout")
    head = combined.value(repo, "rev-parse", "HEAD")
    git(repo, "merge-base", "--is-ancestor", BASE, head)
    base, imported = import_baseline(repo)
    history = git(repo, "rev-list", "--ancestry-path", "--parents", BASE + ".." + head).decode().splitlines()
    introductions = [fields[0] for row in history if (fields := row.split())[1:] == [BASE]]
    require(len(introductions) == 1 and combined.value(repo, "show", "-s", "--format=%P", introductions[0]) == BASE,
            "Expected one reviewed single-parent source introduction from integrated main")
    current = tree(repo, head)
    require(current.get(POLICY, ())[:2] == combined.REGULAR, "Missing strict integration source policy")
    raw = git(repo, "cat-file", "blob", current[POLICY][2])
    require(sha256(raw).hexdigest() == POLICY_SHA256, "Strict integration policy digest differs")
    policy = load_bytes(raw)
    archive = combined.inspect_archive(repo, combined.read_policy())
    git(repo, "merge-base", "--is-ancestor", archive["archive_commit"], BASE)
    active = set(combined.paper.policy_from_archive(repo, archive["archive_commit"])["generated"])
    frozen = set(combined.historical.round6.FROZEN_PRODUCTS)
    manifest = load_bytes(git(repo, "show", BASE + ":" + combined.MANIFEST))["generated"]
    require(len(manifest) == 81 and len(active) == 77 and len(frozen) == 4 and active.isdisjoint(frozen)
            and {r["path"] for r in manifest} == active | frozen, "Historical canonical inventory differs")
    require(all(base[p] == (*combined.REGULAR, row["git_blob"]) for p, row in archive["articles"].items()),
            "Preserved archive entries differ")
    delta = classify(base, current, tree(repo, introductions[0]), active, policy)
    template = combined.historical.round6.validator_template_hash(git(repo, "cat-file", "blob", current[VALIDATOR][2]),
                                                               POLICY_SHA256)
    require(template == policy["validator_template_sha256"], "Strict validator source template differs")
    preserve_documentation_renderer(git(repo, "cat-file", "blob", current["README.md"][2]),
                                    git(repo, "cat-file", "blob", base["README.md"][2]), path="README.md")
    combined.historical.check_worktree(repo, current)
    for p, row in current.items():
        require(bool((repo / p).stat().st_mode & 0o111) == (row[0] == "100755"), "Working-tree mode differs: " + p)
    combined.validate_workflow_migration(repo)
    protected = ("Zeta23/", "Zeta23Arithmetic/", "verification/", "research/", ".github/", "docs/examples/")
    for path in git(repo, "ls-files", "-z", "--others", "--ignored", "--exclude-standard").split(b"\0"):
        name = path.decode()
        require(not (name.startswith(protected) and name.endswith((".lean", ".lean.in", ".py", ".sh", ".yml", ".yaml"))),
                "Ignored source or executable provider: " + name)
    if require_clean:
        require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "Checkout changed during inspection")
    require(head == combined.value(repo, "rev-parse", "HEAD"), "HEAD changed during strict source inspection")
    return {"schema": SCHEMA, "status": "PASS_SOURCE_SCOPE_ONLY", "checked_commit": head,
            "checked_tree": combined.value(repo, "rev-parse", head + "^{tree}"), "base": BASE, "base_tree": BASE_TREE,
            "source_introduction": introductions[0], "source_parents": [STRICT, PREVIOUS], "strict_source": STRICT,
            "integration_commit": INTEGRATION, "imported_file_count": len(imported), "path_policy": POLICY_SHA256,
            "manifest_sha256": combined.file_hash(repo / combined.MANIFEST), "delta": delta, "paper_archive": archive,
            "canonical_product_count": len(active), "unchanged_historical_product_count": len(frozen),
            "generated_freshness": "SEPARATE_CANONICAL_CHECK_REQUIRED", "current_compiler_accepted": False,
            "full_round4_accepted": False, "proof_acceptance": False, "independent_approval": False,
            "canonical_admission": False, "RH": "OPEN", "C1": "OPEN", "Step4": "OPEN"}


def check_classification(repo=combined.REPO):
    from . import strict_classification
    validate_descendant(repo, require_clean=True)
    return strict_classification.check_classification(repo)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-classification", required=True, action="store_true")
    parser.parse_args()
    report = check_classification()
    print(json.dumps({"schema": SCHEMA, "classification": "PASS", **report}))
