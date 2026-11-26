#!/usr/bin/env python3
"""Extend an independently reconstructed exact R7 source stage with the strict route."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

R7 = "7b2414b97cbfefabf15e23707d31b02708c59284"
R7_TREE = "4432385398aeba99780828505faf8c40eb796849"
PERRON = "21b1663d2b2e84f4d4b2c17a9f43bf09a72127f5"
DONOR = "347c89e926a0f335caaab13d005ea738b80ee34b"
DONOR_TREE = "61c265e150ef006c786ef889dc33b4825613f092"
HERE = Path(__file__).resolve().parent
PREFIX = "verification/opica-strict-step4/"
WORKFLOW = ".github/workflows/opica-strict-step4-review.yml"
EXTRA_ASSETS = {
    PREFIX + name for name in (
        "stage.py", "run.sh", "compare.py", "Audit.lean", "README.md",
        "SOURCE_POLICY.json", "comparator/StrictChallenge/ExactRH.lean",
        "comparator/StrictSolution/ExactRH.lean", "comparator/config.json",
    )
} | {WORKFLOW}
REPAIR_PARENT = "dee12959e2c96d85bb6e8c47fa6b089a088fe8fa"
OVERLAY_TARGETS = {
    "Zeta23/OPICATerminal/Analytic/LandauTheorems/mellinGchiOfNeOne.lean",
    "Zeta23/CCM/OriginalDetectorFourHistoryLocalXBound.lean",
}
OVERLAY_PREFIX = PREFIX + "compatibility/lean-4.35.0/"
REPAIR_MODIFIED = {PREFIX + name for name in ("stage.py", "SOURCE_POLICY.json", "README.md")} | {WORKFLOW}
STAGE_ASSETS = {
    "Audit.lean": "AuditStrictReference.lean",
    "comparator/StrictChallenge/ExactRH.lean":
        "strict_comparator/StrictChallenge/ExactRH.lean",
    "comparator/StrictSolution/ExactRH.lean":
        "strict_comparator/StrictSolution/ExactRH.lean",
    "comparator/config.json": "strict_comparator/config.json",
}
LAKE_CONFIG = '''
[[lean_lib]]
name = "Zeta23StrictReference"
roots = ["Zeta23.RHReference.CompactEnergyAdapter"]
globs = ["Zeta23.RHReference.+"]

[[lean_lib]]
name = "StrictChallenge"
srcDir = "strict_comparator"
roots = ["StrictChallenge.ExactRH"]
globs = ["StrictChallenge.ExactRH"]

[[lean_lib]]
name = "StrictSolution"
srcDir = "strict_comparator"
roots = ["StrictSolution.ExactRH"]
globs = ["StrictSolution.ExactRH"]
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def git_text(repo, *args):
    return git(repo, *args).decode("utf-8").strip()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode("ascii") + data).hexdigest()


def manifest(path):
    return json.loads(path.read_bytes())


def safe(path):
    require(re.fullmatch(r"[A-Za-z0-9._/-]+", path) is not None, "unsafe path")
    normalized = PurePosixPath(path)
    require(not normalized.is_absolute() and normalized.as_posix() == path
            and not {"..", "."}.intersection(normalized.parts), "unsafe path")
    return normalized


def validate_delta(diff, paths):
    rows = diff.splitlines()
    require(len(rows) == len(paths) and
            set(rows) == {"A\t" + path for path in paths}, "strict source scope mismatch")


def exact_source(path, raw, entry):
    require(entry["path"] == path and blob(raw) == entry["git_blob"] and
            digest(raw) == entry["sha256"], "strict source hash mismatch: " + path)


def list_files(stage):
    rows = []
    for parent, dirs, files in os.walk(stage):
        dirs[:] = [name for name in dirs if name != ".lake"]
        for name in dirs:
            require(not (Path(parent) / name).is_symlink(), "symlink in staged source")
        for name in files:
            file = Path(parent) / name
            require(not file.is_symlink(), "symlink in staged source")
            require(file.suffix not in {".olean", ".ilean", ".dll", ".so", ".a"},
                    "precompiled object in source stage")
            rows.append({"path": file.relative_to(stage).as_posix(), "sha256": digest(file.read_bytes())})
    return sorted(rows, key=lambda row: row["path"])


def check_scope(repo, head, policy):
    require(git_text(repo, "rev-parse", "HEAD") == head, "candidate checkout HEAD drift")
    require(not git_text(repo, "status", "--porcelain", "--untracked-files=no"),
            "dirty candidate checkout")
    require(policy["schema"] == "STRICT_STEP4_SOURCE_V2" and
            policy["claim"] == "RH_OPEN" and policy["r7"] == R7 and
            policy["r7_tree"] == R7_TREE and policy["perron"] == PERRON and
            policy["donor"] == DONOR and policy["donor_tree"] == DONOR_TREE,
            "strict policy identity drift")
    require(git_text(repo, "rev-parse", R7 + "^{tree}") == R7_TREE, "base tree drift")
    require(git_text(repo, "rev-parse", DONOR + "^{tree}") == DONOR_TREE, "donor tree drift")
    git(repo, "merge-base", "--is-ancestor", PERRON, head)
    git(repo, "merge-base", "--is-ancestor", REPAIR_PARENT, head)
    overlays = policy["overlays"]
    require(set(overlays) == OVERLAY_TARGETS, "strict overlay target inventory differs")
    overlay_paths = {OVERLAY_PREFIX + target for target in OVERLAY_TARGETS}
    delta = git_text(repo, "diff", "--name-status", "--no-renames", REPAIR_PARENT, head).splitlines()
    require(len(delta) == len(overlay_paths) + len(REPAIR_MODIFIED) and set(delta) ==
            ({f"A\t{path}" for path in overlay_paths} | {f"M\t{path}" for path in REPAIR_MODIFIED}),
            "strict compatibility repair scope differs")
    for target, entry in overlays.items():
        overlay = OVERLAY_PREFIX + target
        exact_source(overlay, git(repo, "show", head + ":" + overlay), entry)
        original = git(repo, "show", REPAIR_PARENT + ":" + target)
        verify_preimage(target, original, entry)
        require(original == git(repo, "show", head + ":" + target), "tracked original differs")
    paths = {entry["path"] for entry in policy["modules"]}
    require(len(paths) == len(policy["modules"]), "duplicate strict source path")
    validate_delta(git_text(repo, "diff", "--name-status", "--no-renames", R7, head),
                   paths | EXTRA_ASSETS | overlay_paths)
    for entry in policy["modules"]:
        path = entry["path"]
        safe(path)
        require(path.startswith(("Zeta23/RHReference/", "Zeta23/OPICATerminal/"))
                and path.endswith(".lean"), "module outside strict source boundary")
        current = git(repo, "show", head + ":" + path)
        exact_source(path, current, entry)
        origin = entry["origin"]
        if origin == "perron":
            require(current == git(repo, "show", PERRON + ":" + path),
                    "reviewed Perron source drift")
        elif origin in {"donor", "reduced-donor"}:
            original = git(repo, "show", DONOR + ":" + path)
            require(blob(original) == entry["donor_blob"], "native donor identity drift")
            require((original == current) == (origin == "donor"), "donor provenance mismatch")
        else:
            require(origin == "reference" and path.startswith("Zeta23/RHReference/"),
                    "unexpected strict source origin")
    require(git(repo, "show", head + ":" + PREFIX + "SOURCE_POLICY.json")
            == (HERE / "SOURCE_POLICY.json").read_bytes(), "active policy bytes drift")


def verify_preimage(target, raw, entry):
    require(blob(raw) == entry["original_git_blob"] and digest(raw) == entry["original_sha256"],
            "strict overlay preimage differs: " + target)


def stage_sources(repo, baseline, stage, baseline_receipt, receipt, head):
    policy_path = HERE / "SOURCE_POLICY.json"
    policy = manifest(policy_path)
    check_scope(repo, head, policy)
    require(not stage.exists() and not receipt.exists(), "stage or receipt already exists")
    native = baseline / "verification/opica-native-terminal"
    require(git_text(baseline, "rev-parse", "HEAD") == R7, "wrong R7 checkout")
    python = [sys.executable] + (["-O"] if sys.flags.optimize else [])
    subprocess.run([*python, str(native / "epoch.py"), "--repo", str(baseline),
                    "--out", str(stage), "--receipt", str(baseline_receipt),
                    "--head", R7], check=True)
    base = manifest(baseline_receipt)
    require(base["head"] == R7 and base["tree"] == R7_TREE and
            base["toolchain"] == "leanprover/lean4:v4.35.0" and
            base["mathlib"] == "56a005855ea17e0b0958f73ec801ae140b0a1679",
            "inherited source receipt mismatch")
    for entry in policy["modules"]:
        path = entry["path"]
        target = stage / safe(path)
        require(not target.exists(), "strict source would overwrite inherited path")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git(repo, "show", head + ":" + path))
    for path, entry in policy["overlays"].items():
        target = stage / safe(path)
        require(target.is_file() and not target.is_symlink(), "strict overlay target is missing or a symlink")
        verify_preimage(path, target.read_bytes(), entry)
        patch = git(repo, "show", head + ":" + entry["path"])
        exact_source(entry["path"], patch, entry)
        target.write_bytes(patch)
    for src, dst in STAGE_ASSETS.items():
        target = stage / safe(dst)
        require(not target.exists(), "strict control would overwrite inherited path")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git(repo, "show", head + ":" + PREFIX + src))
    config = stage / "lakefile.toml"
    config.write_bytes(config.read_bytes() + LAKE_CONFIG.encode("utf-8"))
    data = {"schema": "STRICT_STEP4_STAGE_V1", "claim": "RH_OPEN", "head": head,
            "tree": git_text(repo, "rev-parse", head + "^{tree}"),
            "r7": R7, "r7_tree": R7_TREE, "perron": PERRON, "donor": DONOR,
            "toolchain": base["toolchain"], "mathlib": base["mathlib"],
            "base_receipt_sha256": digest(baseline_receipt.read_bytes()),
            "policy_sha256": digest(policy_path.read_bytes()), "files": list_files(stage)}
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    verify_stage(stage, receipt)


def verify_stage(stage, receipt):
    data = manifest(receipt)
    require(data["schema"] == "STRICT_STEP4_STAGE_V1" and data["claim"] == "RH_OPEN"
            and data["r7"] == R7 and data["r7_tree"] == R7_TREE
            and data["perron"] == PERRON and data["donor"] == DONOR
            and data["files"] == list_files(stage), "strict effective source drift")
    print("STRICT_EFFECTIVE_SOURCE_PASS", data["head"], data["tree"], len(data["files"]))


def expect_rejection(action):
    try:
        action()
    except ValueError:
        return
    raise RuntimeError("strict source negative control accepted")


def self_test():
    path = "Zeta23/RHReference/Proof.lean"
    raw = b"theorem example : True := True.intro\n"
    entry = {"path": path, "git_blob": blob(raw), "sha256": digest(raw)}
    exact_source(path, raw, entry)
    validate_delta("A\t" + path, {path})
    for invalid in ("../Proof.lean", "/Proof.lean", "A\\B.lean", "A//B.lean"):
        expect_rejection(lambda: safe(invalid))
    expect_rejection(lambda: exact_source(path, raw + b" ", entry))
    expect_rejection(lambda: validate_delta("M\t" + path, {path}))
    expect_rejection(lambda: validate_delta("", {path}))
    expect_rejection(lambda: validate_delta("A\t" + path + "\nA\tZeta23/Extra.lean", {path}))
    preimage = {"original_git_blob": blob(raw), "original_sha256": digest(raw)}
    verify_preimage(path, raw, preimage)
    expect_rejection(lambda: verify_preimage(path, raw + b" ", preimage))
    print("STRICT_SOURCE_CONTROLS_PASS", 9)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--stage", type=Path)
    parser.add_argument("--baseline-receipt", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--head")
    parser.add_argument("--verify-stage", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    options = parser.parse_args()
    if options.self_test:
        self_test()
    elif options.verify_stage:
        verify_stage(options.stage.resolve(), options.receipt.resolve())
    else:
        stage_sources(options.repo.resolve(), options.baseline.resolve(),
                      options.stage.resolve(), options.baseline_receipt.resolve(),
                      options.receipt.resolve(), options.head)
