"""Exact Round4 source delta; historical guards retain their original checkout.

The authority is the audited path-policy digest in this checker, not a manifest
that can authorize its own additional paths. Source receipts remain outside Git.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from .canonical import require, load_bytes, canonical_bytes, digest, validate_path_inventory
from .snapshot import unlinked, file_hash

BASE = "fe16565b2a31fb8b68bef916ae8f04d535880e7a"
BASE_TREE = "5442650eb749576e4a82e2d57460a4b97e19b5a9"
LEGACY_SCOPE_TEMPLATES = {"rhrc_opica.yml": 4, "rhrc_opica_followup.yml": 7}
LEGACY_SUITE_TEMPLATES = {"rhrc.yml": 1}
MANIFEST = "research/RHRC/integration/opica_round4/BUILD_MANIFEST.json"
AUDITED_PATH_POLICY = "15619d3e9d2e29ef877a32d3fdc1cc7870ecfd642652de4b667a360f13a48728"
REPO = Path(__file__).resolve().parents[4]
DOCUMENTATION_ADDITIONS = (
    "docs/AGENT_GUIDE.md",
    "docs/CURRENT_STATE.md",
    "docs/FRAMEWORKS.md",
    "docs/MATHEMATICAL_GLOSSARY.md",
    "docs/PROJECT_GUIDE.md",
    "docs/REPOSITORY_MAP.md",
    "research/RHRC/ffbbp/README.md",
    "research/RHRC/permansson/README.md",
)
DOCUMENTATION_EDITS = (
    "AGENTS.md",
    "AUDIT.md",
    "FORK_NOTES.md",
    "README.md",
    "research/RHRC/CURRENT_RESEARCH_PLAN.md",
    "research/RHRC/DOCUMENTATION_AUTHORITY.md",
    "research/RHRC/README.md",
    "research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md",
    "research/RHRC/graph/README.md",
    "research/RHRC/integration/README.md",
    "research/RHRC/integration/opica/README.md",
    "research/RHRC/integration/opica_followup/README.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/DOCUMENTATION_INDEX.md",
    "research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md",
    "research/RHRC/ool/README.md",
)

def documentation_migration() -> dict:
    """The reviewed documentation-only extension; no prefix can authorize paths."""
    return {"schema": "OPICA4_DOCUMENTATION_MIGRATION_V1", "id": "DOC_NAV_2026_10_28_01",
            "add": list(DOCUMENTATION_ADDITIONS), "edit": list(DOCUMENTATION_EDITS),
            "renderer_blocks": "UNCHANGED_ACCEPTED_PARENT_BYTES", "claim_cap": "DOCUMENTATION_ONLY",
            "agent_instructions": "UNCHANGED_ACCEPTED_PARENT_TAIL_FROM_LITERAL_ANCHOR",
            "RH": "OPEN", "Step4": "OPEN"}

def preserve_documentation_renderer(current: bytes, parent: bytes, *, path: str) -> None:
    begin, end = b"<!-- RHRC_CURRENT_STATE_BEGIN -->", b"<!-- RHRC_CURRENT_STATE_END -->"
    if begin not in parent and end not in parent:
        return
    def block(data: bytes) -> bytes:
        require(data.count(begin) == data.count(end) == 1,
                "historical renderer marker pair differs: " + path)
        start, stop = data.index(begin), data.index(end)
        require(start < stop, "historical renderer markers reversed: " + path)
        return data[start:stop + len(end)]
    require(block(current) == block(parent), "historical renderer bytes changed: " + path)

def preserve_agent_instructions(current: bytes, parent: bytes) -> None:
    anchor = b"Keep the original Markdown/JSON contracts"
    require(current.count(anchor) == parent.count(anchor) == 1,
            "AGENTS instruction-tail anchor differs")
    require(current[current.index(anchor):] == parent[parent.index(anchor):],
            "protected AGENTS instruction tail changed")

def git(repo: Path, *args: str) -> str:
    env = {**os.environ, "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}
    return subprocess.check_output(["git", "-C", str(repo), *args], env=env, text=True).strip()

def blob_hash(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()

def policy_body(manifest: dict) -> dict:
    require(manifest.get("schema") == "OPICA4_CLOSED_DESCENDANT_MANIFEST_V1", "unknown source contract")
    require(manifest.get("base") == BASE and manifest.get("base_tree") == BASE_TREE,
            "accepted parent reanchor absent")
    result = {k: sorted(row["path"] for row in manifest[k]) for k in ("add", "edit", "generated", "preserve")}
    for values in result.values(): require(len(values) == len(set(values)), "duplicate declared path")
    union = [x for k in result for x in result[k]]
    require(len(union) == len(set(union)), "overlapping file operations")
    validate_path_inventory(result["add"])
    require(manifest.get("documentation_migration") == documentation_migration(),
            "reviewed documentation migration differs or is absent")
    require(set(DOCUMENTATION_ADDITIONS) <= set(result["add"]) and
            set(DOCUMENTATION_EDITS) <= set(result["edit"]),
            "reviewed documentation paths missing from exact operations")
    return result

def classification_delta(base_paths, current_paths, policy: dict) -> dict:
    before, after = set(base_paths), set(current_paths)
    added, deleted = after - before, before - after
    require(not deleted, "parent source deletion forbidden")
    require(added <= set(policy["add"]), "undeclared new source or ignored provider")
    require(set(policy["add"]) <= after, "mandatory declared source missing")
    return {"added": sorted(added), "deleted": []}

def validate_workflow_migration(repo: Path) -> None:
    for name in ("rhrc_opica_round2.yml", "rhrc_opica_round3.yml", *LEGACY_SCOPE_TEMPLATES, *LEGACY_SUITE_TEMPLATES):
        text = (repo/".github/workflows"/name).read_text(encoding="utf-8")
        require("R4_PARENT_SCOPE_V1" in text and BASE in text,
                "historical selector not migrated: " + name)
        require("persist-credentials: false" in text, "persisted source credentials forbidden")
    round2 = (repo/".github/workflows/rhrc_opica_round2.yml").read_text(encoding="utf-8")
    selectors = round2.count("if [ -f research/RHRC/integration/opica_round3/DESCENDANT_EXTENSION.json ]; then")
    require(selectors > 0 and round2.count("# R4_PARENT_SCOPE_V1") == selectors,
            "not every Round2 historical selector migrated")
    for name, count in LEGACY_SCOPE_TEMPLATES.items():
        text=(repo/".github/workflows"/name).read_text(encoding="utf-8")
        require(text.count("ancestor_projection.py create")==count and
                text.count("# R4_PARENT_SCOPE_V1")==count,
                "not every original-contract ancestor selector migrated: "+name)
    for name,count in LEGACY_SUITE_TEMPLATES.items():
        text=(repo/".github/workflows"/name).read_text(encoding="utf-8")
        require(text.count("# R4_PARENT_SCOPE_V1")==count and
                text.count("run_suite.py --skip-derived-state")==count,
                "legacy full-suite dispatcher lacks its own source hop: "+name)

def validate_descendant(repo: Path = REPO, *, require_clean=False) -> dict:
    repo = unlinked(repo).resolve()
    manifest = load_bytes((repo/MANIFEST).read_bytes())
    policy = policy_body(manifest)
    require(digest(policy, domain="OPICA4_PATH_POLICY_V1") == AUDITED_PATH_POLICY,
            "audited path policy differs or not sealed")
    require(git(repo, "rev-parse", BASE + "^{tree}") == BASE_TREE, "parent tree differs")
    require(subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", BASE, "HEAD"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0,
            "child is not a descendant of accepted merge")
    raw = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", BASE])
    baseline = {}
    for line in raw.decode("utf-8").splitlines():
        left, path = line.split("\t", 1); mode, kind, sha = left.split()
        require(kind == "blob", "unsupported embedded repository in parent source")
        baseline[path] = (mode, sha)
    tracked = set(git(repo, "ls-files").splitlines())
    untracked = set(git(repo, "ls-files", "--others", "--exclude-standard").splitlines())
    # Deletions are absent on disk even when a path is still present in the index.
    current = {p for p in tracked | untracked if (repo/p).is_file()}
    delta = classification_delta(baseline, current, policy)
    mutable = set(policy["edit"]) | set(policy["generated"])
    for path, (_, old_blob) in baseline.items():
        file = unlinked(repo/path)
        require(file.is_file(), "parent path missing: " + path)
        if path not in mutable:
            require(blob_hash(file.read_bytes()) == old_blob, "protected parent bytes changed: " + path)
        if path in DOCUMENTATION_EDITS:
            parent = subprocess.check_output(["git", "-C", str(repo), "show", BASE + ":" + path])
            preserve_documentation_renderer(file.read_bytes(), parent, path=path)
            if path == "AGENTS.md":
                preserve_agent_instructions(file.read_bytes(), parent)
    for operation in ("add", "edit"):
        for row in manifest[operation]:
            path = unlinked(repo/row["path"])
            if row["path"] == MANIFEST: continue  # manifest self-hash is external, never circular
            require(type(row.get("sha256")) is str and re.fullmatch(r"[0-9a-f]{64}", row["sha256"]),
                    "missing sealed source digest")
            require(file_hash(path) == row["sha256"], "declared source changed: " + row["path"])
    ignored = git(repo, "ls-files", "--others", "--ignored", "--exclude-standard").splitlines()
    for path in ignored:
        if path.startswith(("Zeta23/", "research/", ".github/")) and path.endswith((".lean", ".lean.in", ".py", ".yml")):
            require(path in set(policy["add"]), "ignored executable/source provider: " + path)
    validate_workflow_migration(repo)
    if require_clean: require(not git(repo, "status", "--porcelain", "--untracked-files=all"), "dirty current source")
    return {"schema": "OPICA4_CURRENT_SOURCE_INSPECTION_V1", "status": "PASS_SOURCE_SCOPE_ONLY",
        "checked_commit": git(repo, "rev-parse", "HEAD"), "checked_tree": git(repo, "rev-parse", "HEAD^{tree}"),
        "base": BASE, "base_tree": BASE_TREE, "path_policy": AUDITED_PATH_POLICY,
        "manifest_sha256": file_hash(repo/MANIFEST), "delta": delta,
        "current_compiler_accepted": False, "full_round4_accepted": False, "RH": "OPEN", "Step4": "OPEN"}

def current_compatibility_scope(report: dict, requested_commit: str, requested_tree: str) -> None:
    require(report.get("scope") == "CURRENT_HOST" and report.get("checked_commit") == requested_commit and
            report.get("checked_tree") == requested_tree, "historical evidence cannot satisfy current source")

def require_acyclic_fingerprint(inputs: set[str], generated_outputs: set[str]) -> None:
    require(not inputs & generated_outputs, "generated product contributes to its own source fingerprint")

def exact_rule(identifier: str, paths: list[str], file_class: str, trust_zone: str) -> dict:
    require(paths and len(paths)==len(set(paths)), 'nonempty exact classification set required')
    return {'id':identifier,'pattern':r'\A(?:'+'|'.join(re.escape(p) for p in sorted(paths))+r')\Z',
            'file_class':file_class,'trust_zone':trust_zone}

def validate_classification_extension(current: dict, parent: dict, new_rules: list[dict]) -> None:
    require(current=={**parent,'rules':[*new_rules,*parent['rules']]},
            'classification extension or protected parent rules differ')
    for rule in new_rules:
        require(rule['pattern'].startswith(r'\A(?:') and rule['pattern'].endswith(r')\Z'),
                'broad classification prefix forbidden')
