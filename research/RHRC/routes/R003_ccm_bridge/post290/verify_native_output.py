#!/usr/bin/env python3
"""Fresh 1024-bit independent-point reconstruction of native panel observations.

The checker shares the canonical analytic backend but invokes separate source
constructions and its own scalar loops. It verifies recorded enclosures;
unresolved seams or source terms stay unresolved.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from evaluate_native_output import APERTURES, CARRIERS, CUTOFFS, HERE, REPO, aperture, source_identity


def fresh_pair(name, K):
    """Scalar-loop checker independent of evaluator matrix-product residuals."""
    sys.path.insert(0, str(HERE.parent))
    import canonical_source_arb as C
    from flint import arb
    from residual_channels import native_geometry, exact_ball, zero_consistency, seed_algebra
    C.set_precision(1024)
    L, Q = aperture(name)
    if Q is None:
        from native_seam_points import direct_at_log_seam, signed_at_log_seam
        Q = int(name[3:])
        L, M = direct_at_log_seam(Q, K)
        channels = signed_at_log_seam(Q, K)
    else:
        M = C.canonical_source_matrix(L, K, Q)
        channels = C.signed_channel_matrices(L, K, Q)
    seed_algebra()
    G = native_geometry(K, L)
    size = 2*K+1
    vec = lambda matrix: [matrix[i, 0] for i in range(size)]
    dot = lambda x, y: sum((a*b for a, b in zip(x, y)), arb(0))
    mv = lambda matrix, vector: [sum((matrix[i, j]*vector[j] for j in range(size)), arb(0)) for i in range(size)]
    subtract_level = lambda x, p, lam: [x[i]-lam*p[i] for i in range(size)]
    reconstruction = [[zero_consistency(M[i, j]-sum((matrix[i, j] for matrix in channels.values()), arb(0)))
                       for j in range(size)] for i in range(size)]
    rows = []
    for carrier in CARRIERS:
        even = carrier.endswith("even")
        Q0 = G[("Qe" if even else "Qo") if carrier.startswith("pole_neutral") else ("E" if even else "O")]
        p = vec(G["pe" if even else "po"])
        apply = lambda x: mv(Q0, mv(M, mv(Q0, x)))
        lam = dot(p, mv(M, p))
        residual = subtract_level(apply(p), p, lam)
        levels = {key: dot(p, mv(matrix, p)) for key, matrix in channels.items()}
        parts = {key: subtract_level(mv(Q0, mv(matrix, p)), p, levels[key]) for key, matrix in channels.items()}
        names = list(parts)
        gram = [[dot(parts[i], parts[j]) for j in names] for i in names]
        residual_sq = dot(residual, residual)
        variance = dot(p, apply(apply(p))) - lam*lam
        sum_parts = [sum((parts[key][i] for key in names), arb(0)) for i in range(size)]
        consistency = {"unit_norm": zero_consistency(dot(p, p)-1),
                       "carrier_projection": [zero_consistency(x-y) for x, y in zip(mv(Q0, p), p)],
                       "channel_residual_sum": [zero_consistency(x-y) for x, y in zip(sum_parts, residual)],
                       "residual_variance": zero_consistency(residual_sq-variance),
                       "full_gram_sum": zero_consistency(residual_sq-sum((v for row in gram for v in row), arb(0)))}
        source = {"status": "NOT_APPLICABLE"}
        if even:
            n2, ve, h = (vec(G[k]) for k in ("N2", "ve", "h"))
            S = dot(n2, mv(M, p))/dot(n2, n2)
            b = dot(h, n2)/dot(n2, n2)
            alpha = dot(ve, mv(G["E"], mv(M, p)))/dot(ve, ve)
            S0 = S-b*alpha
            source = {"status": "EVALUATED", "S": exact_ball(S), "b": exact_ball(b),
                      "alpha": exact_ball(alpha), "S0": exact_ball(S0), "correction": exact_ball(S0-S)}
        rows.append({"carrier": carrier, "rayleigh": exact_ball(lam),
                     "residual_norm_sq": exact_ball(residual_sq), "spectral_variance": exact_ball(variance),
                     "M4": exact_ball(sum((t**4*p[i] for i, t in enumerate(G["n"])), arb(0))),
                     "channel_names": names, "channel_rayleigh": {k: exact_ball(v) for k, v in levels.items()},
                     "residual_gram_real": [[exact_ball(v) for v in row] for row in gram],
                     "native_source": source, "consistency": consistency})
    return {"status": "EVALUATED_NATIVE_PROBE", "rows": rows, "matrix_reconstruction": reconstruction}


def bounded_fresh_pair(name, K, seconds):
    env = os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"})
    scratch = REPO.parent/"native-workers"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verify-", dir=scratch) as tmp:
        out = Path(tmp)/"fresh.json"
        try:
            run = subprocess.run([sys.executable, str(__file__), "--worker", name, str(K), "--out", str(out)],
                                 env=env, capture_output=True, text=True, timeout=seconds)
            if run.returncode or not out.exists():
                return {"status": "UNRESOLVED", "reason": "FRESH_POINT_ERROR: " + (run.stderr[-2000:] or run.stdout[-2000:])}
            return json.loads(out.read_text())
        except subprocess.TimeoutExpired:
            return {"status": "UNRESOLVED", "reason": "FRESH_POINT_HARD_WALL_LIMIT"}


def rational(value):
    if not isinstance(value, list) or len(value) != 2 or any(type(x) is not int for x in value) or value[1] <= 0:
        raise ValueError("expected exact integer endpoint pair")
    return Fraction(*value)


def bounds(record):
    if record.get("finite") is not True:
        raise ValueError("nonfinite or missing enclosure")
    lo, hi = rational(record["lower"]), rational(record["upper"])
    if lo > hi:
        raise ValueError("reversed enclosure")
    return lo, hi


def overlap(old, fresh):
    x, y = bounds(old), bounds(fresh)
    if max(x[0], y[0]) > min(x[1], y[1]):
        raise ValueError("fresh point enclosure contradicts recorded enclosure")


def validate_consistency(item):
    if isinstance(item, list):
        for x in item:
            validate_consistency(x)
    elif isinstance(item, dict) and "enclosure" in item:
        lo, hi = bounds(item["enclosure"])
        if item.get("contains_zero") is not True or not lo <= 0 <= hi:
            raise ValueError("failed or falsely relabelled scalar identity consistency")
    elif isinstance(item, dict):
        for x in item.values():
            if isinstance(x, (dict, list)):
                validate_consistency(x)


def verify(path, seconds):
    panel = json.loads(path.read_text())
    if panel.get("schema") != "post290.native-observation-panel.v1" or panel.get("terminal_claim") != "RH_OPEN":
        raise ValueError("wrong panel schema/claim")
    if panel.get("runner_version") != "symbolic-log-endpoint-v1":
        raise ValueError("wrong native point runner/source convention")
    initial_identity = source_identity()
    initial_source = initial_identity["source_sha256"]
    if panel["source_identity"].get("source_hash_mode") != initial_identity["source_hash_mode"]:
        raise ValueError("unregistered source newline/hash convention")
    if panel["source_identity"]["source_sha256"] != initial_source:
        raise ValueError("panel source changed")
    pairs = panel["pairs"]
    keys = [(r["aperture"], r["K"]) for r in pairs]
    if len(set(keys)) != len(keys) or panel["pair_count"] != len(pairs) or panel["row_count"] != 4*len(pairs):
        raise ValueError("missing/duplicate/miscounted pairs")
    if panel.get("frozen_panel_complete") is True and set(keys) != {(a, k) for a in APERTURES for k in CUTOFFS}:
        raise ValueError("partial panel relabelled complete")
    all_rows = [row for pair in pairs for row in pair["rows"]]
    if panel.get("evaluated_rows") != sum(r["status"] == "EVALUATED_NATIVE_PROBE" for r in all_rows) or panel.get("unresolved_rows") != sum(r["status"] == "UNRESOLVED" for r in all_rows):
        raise ValueError("panel numerical disposition counts disagree")
    receipts = []
    for pair in pairs:
        name, K = pair["aperture"], pair["K"]
        rows = pair["rows"]
        if [r["carrier"] for r in rows] != list(CARRIERS):
            raise ValueError("missing/duplicated/native carrier rows")
        if any(r.get("is_hypothetical_zero_generated_detector") is not False for r in rows):
            raise ValueError("native sample relabelled hypothetical-zero-generated")
        if pair["status"] == "UNRESOLVED":
            if any(r["status"] != "UNRESOLVED" for r in rows):
                raise ValueError("unresolved pair relabelled evaluated")
            receipts.append({"aperture": name, "K": K, "status": "UNRESOLVED_INPUT"})
            continue
        if pair["status"] != "EVALUATED_NATIVE_PROBE" or any(r["status"] != "EVALUATED_NATIVE_PROBE" for r in rows):
            raise ValueError("invalid evaluated pair/row disposition")
        if name.startswith("log") and "-" not in name and "+" not in name:
            from native_seam_points import seam_receipt
            if pair.get("symbolic_seam_receipt") != seam_receipt(int(name[3:])):
                raise ValueError("exact seam source identity omitted or whole-ball scope invented")
        elif pair.get("symbolic_seam_receipt") is not None:
            raise ValueError("ordinary cell point relabelled symbolic seam")
        for row in rows:
            expected_source = "EVALUATED" if row["carrier"].endswith("even") else "NOT_APPLICABLE"
            if row["native_source"]["status"] != expected_source:
                raise ValueError("actual canonical source scalar skipped or wrong parity domain")
            if expected_source == "EVALUATED" and row["native_source"].get("source_binding") != "Zeta23.CCM.evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment":
                raise ValueError("actual source identification binding removed or changed")
        fresh = bounded_fresh_pair(name, K, seconds)
        if fresh["status"] == "UNRESOLVED":
            receipts.append({"aperture": name, "K": K, "status": "UNRESOLVED_FRESH_CHECK", "reason": fresh["reason"]})
            continue
        for old, new in zip(rows, fresh["rows"]):
            for field in ("rayleigh", "residual_norm_sq", "spectral_variance", "M4"):
                overlap(old[field], new[field])
            if old["channel_names"] != new["channel_names"]:
                raise ValueError("signed channel provenance changed")
            for channel in old["channel_names"]:
                overlap(old["channel_rayleigh"][channel], new["channel_rayleigh"][channel])
            if len(old["residual_gram_real"]) != 4:
                raise ValueError("missing residual Gram row")
            for oldrow, newrow in zip(old["residual_gram_real"], new["residual_gram_real"]):
                if len(oldrow) != 4 or len(newrow) != 4:
                    raise ValueError("missing complex Gram cross term")
                for x, y in zip(oldrow, newrow):
                    overlap(x, y)
            if old["native_source"]["status"] == "EVALUATED":
                for field in ("S", "b", "alpha", "S0", "correction"):
                    overlap(old["native_source"][field], new["native_source"][field])
            validate_consistency(old["consistency"])
            validate_consistency(new["consistency"])
        validate_consistency(pair["matrix_reconstruction"])
        validate_consistency(fresh["matrix_reconstruction"])
        receipts.append({"aperture": name, "K": K, "status": "FRESH_1024BIT_CONSISTENT", "rows": 4})
    if source_identity()["source_raw_sha256"] != initial_identity["source_raw_sha256"]:
        raise ValueError("source changed during native fresh checking")
    from evaluate_native_output import digest
    return {"schema": "post290.native-observation-checker.v1", "status": "CHECKED_WITH_OPEN_UNIVERSAL_SCOPE",
            "panel_sha256": digest(path), "source_sha256": initial_source,
            "source_hash_mode": initial_identity["source_hash_mode"],
            "checker_source_raw_sha256": initial_identity["source_raw_sha256"],
            "precision_bits": 1024, "verified_pairs": sum(r["status"] == "FRESH_1024BIT_CONSISTENT" for r in receipts),
            "unresolved_pairs": sum(r["status"] != "FRESH_1024BIT_CONSISTENT" for r in receipts),
            "shared_analytic_backend": True, "independence": "separate process, independent scalar-loop residual/Gram/variance arithmetic, fresh direct/channel matrices and increased precision",
            "universal_theorem_authority": False, "terminal_claim": "RH_OPEN", "receipts": receipts}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("panel", type=Path, nargs="?")
    parser.add_argument("--worker", nargs=2, metavar=("APERTURE", "K"))
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=int, default=180)
    args = parser.parse_args()
    if not 0 < args.seconds <= 180:
        raise ValueError("fresh checker hard cap is 180 seconds per pair")
    result = fresh_pair(args.worker[0], int(args.worker[1])) if args.worker else verify(args.panel, args.seconds)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(json.dumps({k: v for k, v in result.items() if k != "receipts"}))
