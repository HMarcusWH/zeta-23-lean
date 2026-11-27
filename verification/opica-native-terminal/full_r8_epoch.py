"""Source lock for the full direct qualification of the published V3 mathematical tree."""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import epoch
from receipts import require

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
TRIAL_DIR = REPO / "verification/opica-native-surface-trial"
sys.path.insert(0, str(TRIAL_DIR))
import trial
import operator_audit

V3 = "0e8c9fc21693c2e250e756e550ba9ac8940ab401"
V3_TREE = "8eea24fc76e8e11ee3eaf6d94d726c6f2919186b"
R7_SOURCE_SHA256 = "e1f4c89011c93821a051ed79d49fee661c2e0c0e350bfdd6a199725535eaafbb"
FILES_SHA256 = "e5472877989c66fc02cd4fa15b1f5d39814c5d0fa17981150812972c398e9293"
POLICY = HERE / "FULL_R8_POLICY.json"
WORKFLOW = ".github/workflows/opica-native-direct-full-r8.yml"
SCOPE = {WORKFLOW} | {epoch.V + name for name in (
    "full_r8_epoch.py", "FULL_R8_POLICY.json", "admission.py", "run.sh",
    "compatibility_scan.py", "receipts.py", "full_r8_controls.py")}
SCHEMA = "NATIVE_TERMINAL_REPAIR_EPOCH_V8"


def digest_records(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def git(*args):
    return epoch.git(REPO, *map(str, args)).decode().strip()


def validate_policy(head, policy):
    require(policy["schema"] == "OPICA_DIRECT_R8_QUALIFICATION_POLICY"
            and policy["claim"] == "RH_OPEN" and policy["diagnostic_parent"] == V3
            and policy["diagnostic_tree"] == V3_TREE
            and policy["original_head"] == trial.BASE and policy["original_tree"] == trial.TREE,
            "incorrect direct qualification ancestry")
    require(policy["effective_files_sha256"] == FILES_SHA256 and policy["effective_count"] == 2117,
            "incorrect published compiler source inventory")
    require(git("show", "-s", "--format=%P", head) == V3
            and git("rev-parse", V3 + "^{tree}") == V3_TREE
            and git("rev-parse", trial.BASE + "^{tree}") == trial.TREE,
            "expected a direct child of the exact V3 diagnostic")
    subprocess.run(["git", "-C", REPO, "merge-base", "--is-ancestor", trial.BASE, V3], check=True)
    paths = set(git("diff", "--no-renames", "--name-only", V3, head).splitlines())
    protected = json.loads(git("show", f"{head}:{POLICY.relative_to(REPO)}"))
    require(paths == SCOPE and policy == protected
            and set(policy["verification_blobs"]) == SCOPE - {str(POLICY.relative_to(REPO))},
            "unexpected direct qualification files")
    for path, oid in policy["verification_blobs"].items():
        require(git("ls-tree", head, path).startswith("100644 blob " + oid + "\t")
                or git("ls-tree", head, path).startswith("100755 blob " + oid + "\t"),
                "verification source blob differs: " + path)
    require(git("rev-parse", "HEAD") == head and not git("status", "--porcelain", "--untracked-files=no"),
            "dirty verification tree or unbound HEAD")
    require(os.environ.get("GITHUB_SHA", head) == head, "runner source differs from qualification")


def expected_overlays():
    original = json.loads(git("show", f"{trial.BASE}:{epoch.OVERLAY_PATH}"))["replacements"]
    result = {r["destination"]: {"destination": r["destination"], "historical_git_blob": r["historical_git_blob"],
                                "replacement_git_blob": r["replacement_git_blob"]} for r in original}
    for row in trial.source_plan(V3):
        path = row["destination"]
        old = result.get(path, {"historical_git_blob": row["preimage"]})
        result[path] = {"destination": path, "historical_git_blob": old["historical_git_blob"],
                        "replacement_git_blob": row["postimage"]}
    require(len(result) == 24, "unexpected direct overlay inventory")
    return [result[key] for key in sorted(result)]


def fixed_receipt(head):
    policy_bytes = POLICY.read_bytes()
    policy = json.loads(policy_bytes)
    validate_policy(head, policy)
    return {"schema": SCHEMA, "head": head, "tree": git("rev-parse", head + "^{tree}"),
            "claim": "RH_OPEN", "native_base": epoch.BASE, "acquisition_commit": epoch.R0,
            "repair_baseline": trial.BASE, "diagnostic_parent": V3, "diagnostic_tree": V3_TREE,
            "supplier_attribution": "72fead102f663d5c7a407964a13dc0cf9d977207",
            "package_count": 1, "external_project_packages": 0, "mathlib": epoch.MATHLIB,
            "toolchain": epoch.TOOLCHAIN, "original_port_manifest_sha256":
                hashlib.sha256(epoch.committed(REPO, head, epoch.PORT_PATH)).hexdigest(),
            "policy_sha256": hashlib.sha256(policy_bytes).hexdigest(),
            "historical_source_receipt_sha256": R7_SOURCE_SHA256,
            "overlay": expected_overlays()}


def validate_receipt(receipt):
    rows = receipt["files"]
    require(len(rows) == 2117 and digest_records(rows) == FILES_SHA256,
            "direct effective source differs from the published V3 compiler input")
    require({k: v for k, v in receipt.items() if k != "files"} == fixed_receipt(receipt["head"]),
            "direct source receipt does not bind this candidate")


def verify_stage(work, receipt_path):
    receipt = json.loads(receipt_path.read_text())
    validate_receipt(receipt)
    require(epoch.staged_files(work) == receipt["files"], "effective staged source drift")
    for row in receipt["overlay"]:
        require(epoch.blob((work / row["destination"]).read_bytes()) == row["replacement_git_blob"],
                "effective overlay changed: " + row["destination"])
    print("NATIVE_R8_EFFECTIVE_SOURCE_PASS", receipt["head"], len(receipt["files"]), flush=True)


@contextmanager
def original_checkout():
    # The R7 stage validates its *own* checkout and every original mathematical
    # blob. A private read-only object pool and sparse working copy suffice.
    with tempfile.TemporaryDirectory() as name:
        checkout = Path(name) / "r7"
        subprocess.run(["git", "init", "--quiet", checkout], check=True)
        git_dir = checkout / ".git"
        objects = git("rev-parse", "--path-format=absolute", "--git-path", "objects")
        (git_dir / "objects/info/alternates").write_text(objects + "\n")
        shallow = Path(git("rev-parse", "--path-format=absolute", "--git-path", "shallow"))
        if shallow.is_file():
            (git_dir / "shallow").write_bytes(shallow.read_bytes())
        patterns = ["/" + p for p in (epoch.V, "Zeta23Arithmetic/", "Zeta23/OPICANativeTerminal/",
                                       ".github/workflows/opica-native-step4.yml")]
        subprocess.run(["git", "-C", checkout, "sparse-checkout", "set", "--no-cone", "--stdin"],
                       input="\n".join(patterns) + "\n", text=True, check=True)
        subprocess.run(["git", "-C", checkout, "checkout", "--quiet", "--detach", trial.BASE], check=True)
        yield checkout


def stage(work, output, head):
    receipt = fixed_receipt(head)
    with original_checkout() as base:
        original = base.parent / "r7-source.json"
        subprocess.run([sys.executable, "-B", base / epoch.V / "epoch.py", "--repo", base, "--out", work,
                        "--receipt", original, "--head", trial.BASE], check=True)
        require(hashlib.sha256(original.read_bytes()).hexdigest() == R7_SOURCE_SHA256,
                "original R7 staged source receipt drift")
    for row in trial.source_plan(V3):
        path = work / row["destination"]
        current = epoch.blob(path.read_bytes()) if path.exists() else None
        require(current == row["preimage"], "unexpected native baseline: " + str(path))
        relative = epoch.OVERLAY_DIR + row["destination"]
        require(git("rev-parse", head + ":" + relative) == row["postimage"], "candidate postimage differs")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(epoch.committed(REPO, head, relative))
    receipt["files"] = epoch.staged_files(work)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    verify_stage(work, output)


def check_public_inputs(historical, common, report_path):
    # The original comparator has already decoded, counted and hashed both
    # complete exports. Bind its counts to their raw bytes without decoding
    # a second pair of 446 MiB files into memory.
    report = json.loads(report_path.read_text())
    require(report["schema"] == "NATIVE_R7_PUBLIC_TYPE_COMPARISON" and report["claim"] == "RH_OPEN"
            and report["historical_count"] == report["common_count"] == 355
            and report["historical_sha256"] == trial.HIST_EXPORT == trial.digest(historical)
            and report["common_sha256"] == trial.digest(common),
            "public inventory count or raw historical/common source digest differs")
    print("DIRECT_R8_PUBLIC_INPUTS_BOUND", report["historical_sha256"], report["common_sha256"])


def extra_producers(work, out):
    receipt = json.loads((out / "source.json").read_text())
    verify_stage(work, out / "source.json")
    rows = {r["destination"]: r for r in trial.source_plan(V3)}
    chain = [operator_audit.PRODUCERS["tent"], "Zeta23.CCM.DictionaryTentEFExtension",
             "Zeta23.CCM.DictionaryZeroSideBridge"]
    subprocess.run(["lake", "build", *chain], cwd=work, check=True)
    with (out / "companion-bridge-kernel.log").open("w") as log:
        for module in chain:
            subprocess.run(["lake", "env", "leanchecker", "--verbose", module], cwd=work,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    for role, module in operator_audit.PRODUCERS.items():
        expected = rows[module.replace(".", "/") + ".lean"]["common_pin_inventory"]
        operator_audit.run(work, out, REPO, trial.BASE, expected, role)
    verify_stage(work, out / "source.json")
    reports = [role + "-comparison.json" for role in operator_audit.PRODUCERS]
    reports += ["mixed-historical-auxiliary.json", "companion-bridge-kernel.log"]
    result = {"schema": "DIRECT_R8_AUXILIARY_KERNEL_REPLAY", "head": receipt["head"], "tree": receipt["tree"],
              "claim": "RH_OPEN", "chain": chain,
              "reports": {name: trial.digest(out / name) for name in reports}}
    (out / "additional-producers.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--head")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--verify-pins", action="store_true")
    parser.add_argument("--verify-stage", action="store_true")
    parser.add_argument("--extra-producers", type=Path)
    parser.add_argument("--public-inputs", type=Path, nargs=3)
    args = parser.parse_args()
    if args.public_inputs:
        check_public_inputs(*args.public_inputs)
    elif args.verify_pins:
        epoch.pins(args.out.resolve())
    elif args.verify_stage:
        verify_stage(args.out.resolve(), args.receipt.resolve())
    elif args.extra_producers:
        extra_producers(args.out.resolve(), args.extra_producers.resolve())
    else:
        require(args.repo.resolve() == REPO, "candidate checkout does not match source")
        stage(args.out.resolve(), args.receipt.resolve(), args.head)
