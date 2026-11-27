"""Adversarial controls for full direct source identity and the inherited R7 stage."""
import copy
import json
from pathlib import Path
import subprocess
import sys

from full_r8_epoch import (POLICY, epoch, original_checkout, trial, validate_policy,
                           validate_receipt, verify_stage)

work, receipt_path = map(Path, sys.argv[1:])
r = json.loads(receipt_path.read_text())
verify_stage(work, receipt_path)
with original_checkout() as original:
    subprocess.run([sys.executable, "-B", original / epoch.V / "epoch.py", "--repo", original,
                    "--head", trial.BASE, "--self-test"], check=True)

def reject(function):
    try:
        function()
    except (ValueError, KeyError, RuntimeError, FileNotFoundError, subprocess.CalledProcessError):
        return
    raise RuntimeError("mutated source control accepted")

fields = {"claim": "RH_PROVED", "toolchain": "leanprover/lean4:v4.33.0-rc2", "schema":
          "NATIVE_TERMINAL_REPAIR_EPOCH_V7", "mathlib": "0" * 40, "repair_baseline": trial.FIRST_TRIAL,
          "head": trial.BASE, "tree": trial.TREE, "supplier_attribution": "0" * 40,
          "diagnostic_parent": trial.BASE, "diagnostic_tree": trial.TREE, "historical_source_receipt_sha256": "",
          "acquisition_commit": trial.BASE, "original_port_manifest_sha256": "0" * 64,
          "external_project_packages": 1, "policy_sha256": "", "package_count": 2, "native_base": trial.BASE}
for name, value in fields.items():
    reject(lambda: validate_receipt(dict(r, **{name: value})))
for key in ("files", "overlay"):
    bad = copy.deepcopy(r)
    bad[key].pop()
    reject(lambda: validate_receipt(bad))
    bad = copy.deepcopy(r)
    bad[key][0] = bad[key][1]
    reject(lambda: validate_receipt(bad))
bad = copy.deepcopy(r)
bad["overlay"][0]["replacement_git_blob"] = "0" * 40
reject(lambda: validate_receipt(bad))
negative_policy = json.loads(POLICY.read_bytes())
negative_policy["verification_blobs"].pop(next(iter(negative_policy["verification_blobs"])))
reject(lambda: validate_policy(r["head"], negative_policy))
# An extra precompiled object and a changed actual Lean source must each fail.
marker = work / "unapproved-direct-study.olean"
if marker.exists():
    raise RuntimeError("unapproved object present before mutation")
try:
    marker.write_bytes(b"forged object")
    reject(lambda: verify_stage(work, receipt_path))
finally:
    marker.unlink()
source = work / epoch.TERMINAL
original_bytes = source.read_bytes()
try:
    source.write_bytes(original_bytes + b"\n-- direct source mutation\n")
    reject(lambda: verify_stage(work, receipt_path))
finally:
    source.write_bytes(original_bytes)
verify_stage(work, receipt_path)
print("NATIVE_R8_SOURCE_AND_STAGE_CONTROLS_PASS", len(fields) + 8)
