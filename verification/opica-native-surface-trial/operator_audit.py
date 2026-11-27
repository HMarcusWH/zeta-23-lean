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


def check_historical_mixed(expected, baseline, candidate, out):
    import base64
    import hashlib
    import json
    import zlib

    snapshots = expected["historical_auxiliary"]
    frozen = {
        "Zeta23.CCM.sourcePairingCoefficientSum.eq_1": (
            493888, "492a5e810c5cd6d932b17afff5446298d0bb75074e3a372f7a43e2deeeda068f",
            "3b45b80f292d5ecbc494318ab6ce5aba7ef44f22689f7bd0ad54d1a8f669e1bc"),
        "Zeta23.CCM.sourcePairingRightDefect.eq_1": (
            538535, "bad8131f2d8ab54edb3cd1dae9ca4a6b3e57727ebad96c5f6315ba79b75e9d1a",
            "8ff1ab86653e060d493d8992c6e583006cdff34ed86386c6634ff70977d6878b"),
    }
    archive = {
        "archive_id": 15182125482,
        "archive_sha256": "3fdeb147e4ba3fdec49cbe7d4c1aabd8f3f5b55b072674f0faf12b2459b888f1",
        "git_commit": "e7b940fece806876a9f4ff6de05aca3cee3f06f0",
        "source_git_oid": "03d393b3ea72e16850bf628cb759910fb78ec4ff",
        "olean_sha256": "cdeab7275e9a3cd3e4392b2d57a0ed6121fb239d107bcd06361f117c671b7165",
        "lean_sha256": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
        "encoding": "gzip+base64",
    }
    if (any(snapshots.get(key) != value for key, value in archive.items())
            or set(snapshots["rows"]) != set(frozen) or expected["changed"] != sorted(frozen)):
        raise RuntimeError("wrong historical auxiliary compiler snapshot or changed scope")
    old_binder = "`x.«_@».Mathlib.Data.FunLike.Basic"
    current_binder = "`x.«_@».Mathlib.Basic.FunLike.Basic"
    rows = {}
    for name, (size, historical_digest, baseline_digest) in frozen.items():
        packed = base64.b64decode(snapshots["rows"][name], validate=True)
        decoder = zlib.decompressobj(zlib.MAX_WBITS | 16)
        raw = decoder.decompress(packed, size + 1)
        if (len(raw) != size or not decoder.eof or decoder.unused_data or decoder.unconsumed_tail
                or hashlib.sha256(raw).hexdigest() != historical_digest):
            raise RuntimeError("incorrect preserved old compiler bytes for " + name)
        original = raw.decode("utf-8")
        left_kind, left = baseline[name]
        right_kind, right = candidate[name]
        if (original.count(old_binder) != 1 or original.count(current_binder) != 0
                or left_kind != right_kind or left_kind != "theorem"
                or hashlib.sha256(left.encode()).hexdigest() != baseline_digest):
            raise RuntimeError("unexpected parent type or historical binder for " + name)
        if (original == right or right.count(current_binder) != 1
                or original.replace(old_binder, current_binder) != right):
            raise RuntimeError("unexpected auxiliary historical type difference for " + name)
        rows[name] = {
            "historical_raw_sha256": historical_digest,
            "baseline_raw_sha256": baseline_digest,
            "candidate_raw_sha256": hashlib.sha256(right.encode()).hexdigest(),
            "literal_historical_match": False,
            "remaining_binder_differences": 1,
        }
    report = {"schema": "MIXED_PRODUCER_HISTORICAL_RAW_DELTA", **archive, "rows": rows,
              "historical_status": "REVIEW_REQUIRED", "claim": "RH_OPEN"}
    (out / "mixed-historical-auxiliary.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


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
    if role == "mixed":
        check_historical_mixed(expected, left, right, out)
