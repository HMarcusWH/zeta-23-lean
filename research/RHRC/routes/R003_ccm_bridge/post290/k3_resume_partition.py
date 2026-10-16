#!/usr/bin/env python3
"""Freeze the source-bound, exact SECOND continuation; no positivity is inferred."""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "post287"
sys.path[:0] = [str(OLD), str(HERE.parent)]
from certificate_integrity import LAYERS, rational, record_path, validate_layer, source_input_digests, source_commit

HISTORICAL_COMMIT = "31512dbb698dd59b90cfa32549f0e9273a5163f9"
HISTORICAL_RUN = 38332529352
EXPECTED_UNRESOLVED = {(9, "even"): 7, (13, "even"): 7, (14, "even"): 11, (15, "even"): 10}
RESOURCES = {
    "method": "SECOND", "first": {"precision_bits": 256, "max_depth": 40, "max_nodes": 4096, "seconds": 1800},
    "second": {"precision_bits": 512, "max_depth": 48, "max_nodes": 8192, "seconds": 1800},
    "first_component_parts": 8, "second_leaf_parts": 4, "second_child_cap": 256,
    "max_concurrency": 8, "checker_precision_bits": 768,
    "checker_seconds_per_layer": 1800, "checker_max_concurrency": 8,
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pair(value):
    return [value.numerator, value.denominator]


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def own_source():
    return {str(p.relative_to(HERE)): digest(p) for p in sorted(HERE.glob("k3_*.py"))}


def seam_source_bindings():
    """Exact source lineage for the endpoint identities; compiler audit is separate."""
    root=HERE.parents[4]
    bindings={
        "Zeta23.CCM.qBasis_aperture_eq_zero":"Zeta23/CCM/KernelAnalysis.lean",
        "Zeta23.CCM.primeSourceCoordinate_log_add":"Zeta23/CCM/CanonicalPrimeSeamTaylor.lean",
        "Zeta23.CCM.sourceMatrix_zero":"Zeta23/CCM/SourceMatrix.lean",
    }
    return {"entering_source_coordinate":"omega=0","bindings":{name:{"path":path,"sha256":digest(root/path)} for name,path in bindings.items()},"authority":"SOURCE_BINDINGS_ONLY_COMPILER_RECEIPT_SEPARATELY_REQUIRED"}


def current_identity():
    root = HERE.parents[4]
    return {"commit": source_commit(), "tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=root, text=True).strip(),
            "source_digests": source_input_digests(), "continuation_source_digests": own_source(),
            "seam_source_bindings":seam_source_bindings(),
            "python": platform.python_version(), "python_executable": sys.executable}


def require_current(manifest):
    identity = current_identity()
    if identity != manifest["current_source"]:
        raise ValueError("source tree, continuation code or toolchain changed after preregistration")


def split(lo, hi, count):
    if not lo < hi or count <= 0:
        raise ValueError("unordered rational endpoints or invalid subdivision")
    return [(lo + (hi-lo)*i/count, lo + (hi-lo)*(i+1)/count) for i in range(count)]


def coalesce(unresolved):
    components = []
    previous = None
    for index, tile in sorted(enumerate(unresolved), key=lambda x: rational(x[1]["left"])):
        lo, hi = rational(tile["left"]), rational(tile["right"])
        if not lo < hi or previous is not None and lo < previous:
            raise ValueError("unresolved intervals overlap or have unordered endpoints")
        if components and lo == components[-1]["right"]:
            components[-1]["right"] = hi
            components[-1]["parents"].append(index)
        else:
            components.append({"left": lo, "right": hi, "parents": [index]})
        previous = hi
    return components


def intake(directory):
    directory = Path(directory)
    manifest = json.loads((directory / "manifest.json").read_text())
    if manifest.get("source_commit") != HISTORICAL_COMMIT or manifest.get("method") != "SECOND" or manifest.get("terminal_claim") != "RH_OPEN":
        raise ValueError("wrong historical source/method/claim")
    seen, complete, inherited, hashes = set(), 0, [], {"manifest.json": digest(directory / "manifest.json")}
    for spec in manifest["records"]:
        layer = (spec["cell"], spec["parity"])
        if layer in seen or layer not in LAYERS:
            raise ValueError("duplicated or illegal historical layer")
        seen.add(layer)
        path = record_path(directory, spec["file"])
        if digest(path) != spec["sha256"]:
            raise ValueError("historical layer bytes changed")
        data = json.loads(path.read_text())
        complete += int(validate_layer(spec, data, "SECOND"))
        if len(data["unresolved"]) != EXPECTED_UNRESOLVED.get(layer, 0):
            raise ValueError("historical unresolved count disagrees with actual intervals")
        hashes[spec["file"]] = digest(path)
        inherited.append((spec, data))
    if seen != LAYERS or complete != 26:
        raise ValueError("INPUT_MISSING: require all 30 layers, exactly 26 complete")
    return manifest, inherited, hashes


def freeze(directory):
    historical, layers, hashes = intake(directory)
    components, jobs = [], []
    for spec, data in sorted(layers, key=lambda x: (x[0]["cell"], x[0]["parity"])):
        for i, component in enumerate(coalesce(data["unresolved"])):
            q, parity = spec["cell"], spec["parity"]
            ancestors = [{"file": spec["file"], "sha256": spec["sha256"], "unresolved_index": n,
                          "left": data["unresolved"][n]["left"], "right": data["unresolved"][n]["right"]} for n in component["parents"]]
            components.append({"Q": q, "parity": parity, "component": i, "left": pair(component["left"]), "right": pair(component["right"]), "ancestors": ancestors})
            for n, (lo, hi) in enumerate(split(component["left"], component["right"], 8)):
                jobs.append({"id": f"Q{q:02d}_{parity}_C{i:02d}_P{n:02d}", "Q": q, "parity": parity, "component": i, "left": pair(lo), "right": pair(hi), "pass": 1, "ancestors": ancestors})
    return {"schema": "post290.k3-resource-partition.v1", "protocol": "SECOND_RESOURCE_PARTITION_2026_10_13_v1", "terminal_claim": "RH_OPEN", "not_a_lean_proof": True,
            "resources": RESOURCES, "historical_source": {"commit": HISTORICAL_COMMIT, "run": HISTORICAL_RUN, "directory": str(Path(directory).resolve()), "hashes": hashes, "source_digests": historical["source_digests"]},
            "current_source": current_identity(), "components": components, "jobs": jobs, "historical_layers": 30, "historical_complete_layers": 26, "historical_unresolved_leaves": 35}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError("refuse to overwrite preregistered partition")
    result = freeze(args.archive)
    write(args.out, result)
    print(json.dumps({"partition_sha256": digest(args.out), "components": len(result["components"]), "jobs": len(result["jobs"]), "terminal_claim": "RH_OPEN"}))


if __name__ == "__main__":
    main()
