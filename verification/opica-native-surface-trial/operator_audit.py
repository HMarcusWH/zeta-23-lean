"""Compare the additional operator producer on its R7 and trial common-pin sources."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

MODULE = "Zeta23.CCM.NativeDampedCompletionOperator"
DESTINATION = MODULE.replace(".", "/") + ".lean"


def inventory(path):
    records = json.loads(path.read_text())
    declarations = {r["name"]: (r["kind"], r["type_expr"]) for r in records}
    if not records or len(declarations) != len(records) or {r["module"] for r in records} != {MODULE}:
        raise RuntimeError("invalid operator compiler inventory")
    return declarations


def inventory_digest(declarations):
    rows = [[name, kind, hashlib.sha256(expr.encode()).hexdigest()]
            for name, (kind, expr) in sorted(declarations.items())]
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()


def export_program(source):
    original = source.read_text()
    first = original.index("open Lean Elab Command\n")
    start = original.index("  let modules := [", first)
    end = original.index("  let mut rows : Array Json := #[]", start)
    return (f"import {MODULE}\nimport Lean\n" + original[first:start]
            + f'  let modules := ["{MODULE}"]\n' + original[end:])


def run(work, out, checkout, base, expected):
    scratch = out.parent / "operator-comparison"
    scratch.mkdir()
    baseline = scratch / "baseline"
    normal = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=work, text=True).strip()
    object_path = Path(DESTINATION).with_suffix(".olean")
    roots = [(work / item).resolve() for item in normal.split(os.pathsep) if item]
    origin = next((root for root in roots if (root / object_path).is_file()), None)
    if origin is None:
        raise RuntimeError("compiled candidate operator missing")
    # Lean picks a search root by namespace. Mirror the candidate's built project
    # dependencies so the temporary baseline can resolve siblings in Zeta23.CCM.
    def omit_target(directory, names):
        return [name for name in names if Path(directory) == origin / object_path.parent
                and name.startswith(object_path.stem + ".")]
    shutil.copytree(origin / "Zeta23", baseline / "Zeta23", copy_function=os.symlink, ignore=omit_target)
    source = baseline / DESTINATION
    with source.open("wb") as stream:
        subprocess.run(["git", "-C", checkout, "show", f"{base}:{DESTINATION}"], stdout=stream, check=True)
    olean = source.with_suffix(".olean")
    subprocess.run(["lake", "env", "lean", "-R", baseline, "-o", olean, source], cwd=work, check=True)
    exporter = scratch / "OperatorSurface.lean"
    exporter.write_text(export_program(work / "TypeSurface.lean"))
    results = []
    for label, search in (("baseline", str(baseline) + os.pathsep + normal), ("candidate", normal)):
        path = out / f"operator-{label}.json"
        env = ["lake", "env", "env", "LEAN_PATH=" + search]
        subprocess.run([*env, "OPICA_NATIVE_TYPE_SURFACE=" + str(path), "lean", exporter], cwd=work, check=True)
        with (out / f"operator-{label}-kernel.log").open("w") as log:
            subprocess.run([*env, "leanchecker", "--verbose", MODULE], cwd=work, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        results.append(inventory(path))
    left, right = results
    missing = sorted(left.keys() - right.keys())
    extra = sorted(right.keys() - left.keys())
    changed = sorted(n for n in left.keys() & right.keys() if left[n] != right[n])
    hashes = {"baseline_inventory_sha256": inventory_digest(left), "candidate_inventory_sha256": inventory_digest(right)}
    receipt = {"schema": "R8_ADDITIONAL_COMMON_PIN_OPERATOR_INVENTORY", "module": MODULE,
               "baseline": base, "baseline_count": len(left), "candidate_count": len(right),
               "missing": missing, "extra": extra, "changed": changed,
               "expected_changes": expected["changed"], "expected_count": expected["count"],
               "stock_kernel": ["baseline", "candidate"], **hashes, "claim": "RH_OPEN"}
    (out / "operator-comparison.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if (missing or extra or len(right) != expected["count"] or changed != expected["changed"]
            or any(digest != expected[key] for key, digest in hashes.items())):
        raise RuntimeError("unexpected public producer declaration changes")
