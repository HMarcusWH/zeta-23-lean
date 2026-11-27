"""Compare each newly overlaid producer on its R7 and trial common-pin sources."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

PRODUCERS = {"operator": "Zeta23.CCM.NativeDampedCompletionOperator",
             "tent": "Zeta23.CCM.DictionaryTentArchLimit",
             "mixed": "Zeta23.CCM.MixedSourceDerivativeTransport"}


GENERATED_MIXED_EQUATION = """import Zeta23.CCM.MixedSourceDerivativeTransport
import Lean

open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let via := ``Zeta23.CCM.sourceAtomPairing
  let some names ← liftTermElabM (Lean.Meta.getEqnsFor? via)
    | throwError "No generated equations for {via}"
  let expected := `Zeta23.CCM.sourceAtomPairing.eq_1
  unless names == #[expected] do throwError "Unexpected generated equation names {names}"
  let env := (← getEnv).setExporting false
  let some info := env.find? expected | throwError "Missing compiler-generated equation {expected}"
  let .thmInfo _ := info | throwError "Expected a theorem at {expected}"
  let some output ← IO.getEnv "COORDINATE_EQUATION_REPR" | throwError "Output path required"
  liftIO <| IO.FS.writeFile output (reprStr info.type)
"""


def inventory(path, module):
    records = json.loads(path.read_text())
    declarations = {r["name"]: (r["kind"], r["type_expr"]) for r in records}
    if not records or len(declarations) != len(records) or {r["module"] for r in records} != {module}:
        raise RuntimeError("invalid compiler inventory for " + module)
    return declarations


def inventory_digest(declarations):
    rows = [[name, kind, hashlib.sha256(expr.encode()).hexdigest()]
            for name, (kind, expr) in sorted(declarations.items())]
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()


def export_program(source, module):
    original = source.read_text()
    first = original.index("open Lean Elab Command\n")
    start = original.index("  let modules := [", first)
    end = original.index("  let mut rows : Array Json := #[]", start)
    return (f"import {module}\nimport Lean\n" + original[first:start]
            + f'  let modules := ["{module}"]\n' + original[end:])


def run(work, out, checkout, base, expected, role):
    module = PRODUCERS[role]
    destination = module.replace(".", "/") + ".lean"
    scratch = out.parent / (role + "-comparison")
    scratch.mkdir()
    baseline = scratch / "baseline"
    normal = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=work, text=True).strip()
    object_path = Path(destination).with_suffix(".olean")
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
    source = baseline / destination
    with source.open("wb") as stream:
        subprocess.run(["git", "-C", checkout, "show", f"{base}:{destination}"], stdout=stream, check=True)
    olean = source.with_suffix(".olean")
    subprocess.run(["lake", "env", "lean", "-R", baseline, "-o", olean, source], cwd=work, check=True)
    exporter = scratch / "OperatorSurface.lean"
    exporter.write_text(export_program(work / "TypeSurface.lean", module))
    equation_exporter = scratch / "GeneratedEquation.lean"
    if role == "mixed":
        equation_exporter.write_text(GENERATED_MIXED_EQUATION)
    results = []
    for label, search in (("baseline", str(baseline) + os.pathsep + normal), ("candidate", normal)):
        path = out / f"{role}-{label}.json"
        env = ["lake", "env", "env", "LEAN_PATH=" + search]
        subprocess.run([*env, "OPICA_NATIVE_TYPE_SURFACE=" + str(path), "lean", exporter], cwd=work, check=True)
        with (out / f"{role}-{label}-kernel.log").open("w") as log:
            subprocess.run([*env, "leanchecker", "--verbose", module], cwd=work, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        if role == "mixed":
            raw = out / f"mixed-{label}-generated-equation.txt"
            subprocess.run([*env, "COORDINATE_EQUATION_REPR=" + str(raw), "lean", equation_exporter],
                           cwd=work, check=True)
            if hashlib.sha256(raw.read_bytes()).hexdigest() != expected[label + "_equation_sha256"]:
                raise RuntimeError("generated equation differs from the independently compiled " + label)
        results.append(inventory(path, module))
    left, right = results
    missing = sorted(left.keys() - right.keys())
    extra = sorted(right.keys() - left.keys())
    changed = sorted(n for n in left.keys() & right.keys() if left[n] != right[n])
    hashes = {"baseline_inventory_sha256": inventory_digest(left), "candidate_inventory_sha256": inventory_digest(right)}
    receipt = {"schema": "R8_ADDITIONAL_COMMON_PIN_INVENTORY", "module": module,
               "baseline": base, "baseline_count": len(left), "candidate_count": len(right),
               "missing": missing, "extra": extra, "changed": changed,
               "expected_changes": expected["changed"], "expected_count": expected["count"],
               "stock_kernel": ["baseline", "candidate"], **hashes, "claim": "RH_OPEN"}
    (out / f"{role}-comparison.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if (missing or extra or len(right) != expected["count"] or changed != expected["changed"]
            or any(digest != expected[key] for key, digest in hashes.items())):
        raise RuntimeError("unexpected public producer declaration changes in " + module)
