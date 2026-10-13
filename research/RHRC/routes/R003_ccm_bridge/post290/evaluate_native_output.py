#!/usr/bin/env python3
"""Evaluate the frozen low-K native panel with isolated bounded point workers.

Registered logarithmic seams consume the exact entering-atom zero theorem
through a symbolic-point wrapper. No numerical nudging or whole-ball cutoff
claim is made. Missing, nonfinite or timed-out quantities remain unresolved.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
CARRIERS = ("legal_even", "legal_odd", "pole_neutral_even", "pole_neutral_odd")
CUTOFFS = (3, 4, 6, 8)
APERTURES = ("1/512", "1/400", "1/4", "1/2", "log2-1/1024", "log2", "log2+1/1024", "log3", "log4", "log8", "log16")
SOURCE_PATHS = (HERE.parent / "canonical_source_arb.py", HERE / "residual_channels.py", HERE / "evaluate_native_output.py", HERE / "verify_native_output.py",
                HERE / "native_seam_points.py", REPO / "research/RHRC/integration/post290/NATIVE_SEAM_POINT_PROTOCOL.json",
                REPO / "Zeta23/CCM/KernelAnalysis.lean", REPO / "Zeta23/CCM/CanonicalPrimeSeamTaylor.lean",
                REPO / "Zeta23/CCM/SourceMatrix.lean", REPO / "Zeta23/CCM/Step123PrimeSeam.lean")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_identity():
    return {"commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
            "tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=REPO, text=True).strip(),
            "working_tree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=REPO, text=True).strip()),
            "source_hash_mode": "CRLF_TO_LF_ONLY_WITH_RAW_BYTES_RECORDED_SEPARATELY",
            "source_sha256": {p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest() for p in SOURCE_PATHS},
            "source_raw_sha256": {p.relative_to(REPO).as_posix(): digest(p) for p in SOURCE_PATHS}}


def aperture(name):
    from flint import arb
    if name not in APERTURES:
        raise ValueError("unregistered aperture")
    if name.startswith("log"):
        text = name[3:]
        integer = int(text.split("-")[0].split("+")[0])
        value = arb(integer).log()
        if "+" in text:
            return value + arb(1)/1024, integer
        if "-" in text:
            return value - arb(1)/1024, integer-1
        return value, None
    num, den = name.split("/")
    return arb(int(num))/int(den), 1


def unresolved_rows(name, K, reason):
    return [{"aperture": name, "K": K, "carrier": c, "status": "UNRESOLVED", "reason": reason,
             "is_hypothetical_zero_generated_detector": False, "authority": "NONE", "terminal_claim": "RH_OPEN"} for c in CARRIERS]


def compute_pair(name, K, bits):
    sys.path.insert(0, str(HERE.parent))
    import canonical_source_arb as C
    from residual_channels import exact_ball, zero_consistency, seed_algebra, native_geometry, evaluate_row
    C.set_precision(bits)
    if K not in CUTOFFS:
        raise ValueError("unregistered cutoff")
    L, Q = aperture(name)
    seam = None
    if Q is None:
        from native_seam_points import direct_at_log_seam, signed_at_log_seam, seam_receipt
        Q = int(name[3:])
        L, M = direct_at_log_seam(Q, K)
        channels = signed_at_log_seam(Q, K)
        seam = seam_receipt(Q)
    elif not C.fixed_cell_membership(Q, L)["certified"]:
        raise ValueError("aperture not inside the exact registered cutoff cell")
    else:
        # Separately evaluate direct and legacy+repair source formulas.
        M = C.canonical_source_matrix(L, K, Q)
        channels = C.signed_channel_matrices(L, K, Q)
    symbolic = seed_algebra()
    G = native_geometry(K, L)
    rebuilt = sum(channels.values())
    difference = M-rebuilt
    reconstruction = [[zero_consistency(difference[i, j]) for j in range(M.ncols())] for i in range(M.nrows())]
    rows = []
    for carrier in CARRIERS:
        row = evaluate_row(carrier, G, M, channels)
        row.update({"aperture": name, "K": K, "Q": Q, "precision_bits": bits, "terminal_claim": "RH_OPEN"})
        rows.append(row)
    return {"aperture": name, "K": K, "Q": Q, "precision_bits": bits,
            "L": exact_ball(L), "a": exact_ball(G["a"]), "symbolic_seed_checks": symbolic,
            "pole_normal_even_norm_sq": exact_ball(G["even_normal_sq"]),
            "pole_normal_odd_norm_sq": exact_ball(G["odd_normal_sq"]),
            "matrix_reconstruction": reconstruction, "rows": rows, "status": "EVALUATED_NATIVE_PROBE",
            "symbolic_seam_receipt": seam}


def bounded_pair(name, K, bits, seconds):
    env = os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"})
    started = time.monotonic()
    scratch = REPO.parent / "native-workers"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="point-", dir=scratch) as tmp:
        target = Path(tmp)/"pair.json"
        try:
            result = subprocess.run([sys.executable, str(__file__), "--worker", name, str(K), "--bits", str(bits), "--out", str(target)],
                                    env=env, capture_output=True, text=True, timeout=seconds)
            if result.returncode or not target.exists():
                reason = "POINT_EVALUATION_ERROR: " + (result.stderr[-2000:] or result.stdout[-2000:])
                return {"aperture": name, "K": K, "rows": unresolved_rows(name, K, reason), "status": "UNRESOLVED", "elapsed_seconds": time.monotonic()-started}
            record = json.loads(target.read_text())
        except subprocess.TimeoutExpired:
            return {"aperture": name, "K": K, "rows": unresolved_rows(name, K, "POINT_WORKER_HARD_WALL_LIMIT"), "status": "UNRESOLVED", "elapsed_seconds": time.monotonic()-started}
    record["elapsed_seconds"] = time.monotonic()-started
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--worker", nargs=2, metavar=("APERTURE", "K"))
    parser.add_argument("--bits", type=int, default=192, choices=(192, 384, 768, 1024))
    parser.add_argument("--seconds", type=int, default=120)
    parser.add_argument("--apertures", nargs="+", choices=APERTURES, default=APERTURES)
    parser.add_argument("--cutoffs", nargs="+", type=int, choices=CUTOFFS, default=CUTOFFS)
    args = parser.parse_args()
    if args.worker:
        record = compute_pair(args.worker[0], int(args.worker[1]), args.bits)
    else:
        if not 0 < args.seconds <= 120:
            raise ValueError("discovery worker hard cap is 120 seconds per pair")
        initial = source_identity()
        pairs = []
        for name in args.apertures:
            for K in args.cutoffs:
                pair = bounded_pair(name, K, args.bits, args.seconds)
                pairs.append(pair)
                print(json.dumps({"aperture": name, "K": K, "status": pair["status"]}), flush=True)
        if source_identity()["source_raw_sha256"] != initial["source_raw_sha256"]:
            raise ValueError("native source bytes changed during evaluation")
        rows = [row for pair in pairs for row in pair["rows"]]
        record = {"schema": "post290.native-observation-panel.v1", "runner_version": "symbolic-log-endpoint-v1", "source_identity": initial,
                  "status": "COMPLETE_OBSERVATION_WITH_OPEN_QUANTITIES", "pairs": pairs,
                  "pair_count": len(pairs), "row_count": len(rows),
                  "evaluated_rows": sum(row["status"] == "EVALUATED_NATIVE_PROBE" for row in rows),
                  "unresolved_rows": sum(row["status"] == "UNRESOLVED" for row in rows),
                  "frozen_panel_complete": set(args.apertures) == set(APERTURES) and set(args.cutoffs) == set(CUTOFFS),
                  "not_a_Lean_proof": True, "not_a_universal_detector_evaluation": True,
                  "source_matrix": "UNCHANGED_CANONICAL", "terminal_claim": "RH_OPEN"}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
