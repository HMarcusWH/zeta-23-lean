#!/usr/bin/env python3
"""Pointwise Arb replay for post-#171 threshold-barrier candidates.

This certifier deliberately avoids whole-cell interval evaluation.  Each replay
point uses the actual physical integer cutoff Q=floor(exp L), then removes the
current q atom at matrix level to recover the q-removed background.  A negative
full Schur pivot with certified predecessor positivity is a successful research
discovery, not a CI failure.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, canonical_source_matrix, set_precision
from certify_post169_fb05_threshold_pivot_scope import (
    _entrywise_overlap,
    _restricted,
    _schur_record,
    _sign_class,
    _step_basis,
)
from post166_fb05_cell_interval import fixed_q_canonical_source_matrix_arb
from post167_fb05_threshold_jet import canonical_entering_atom_arb
from post171_fb05_schur_barrier import arithmetic_cell

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post171_fb05_threshold_barrier_v1.json"


def _target_key(target: dict) -> tuple[int, int, str]:
    return int(target["q"]), int(target["predecessor_N"]), target["selected_parity"]


def _find_discovery_case(discovery: dict, target: dict) -> dict:
    key = _target_key(target)
    for rec in discovery["cases"]:
        t = rec["target"]
        if (int(t["q"]), int(t["N"]), t["parity"]) == key:
            return rec
    raise KeyError(f"discovery output missing target {key}")


def _quantize_omega(q: int, omega_float: float, bits: int) -> tuple[int, int]:
    cell = arithmetic_cell(q)
    den = 1 << bits
    num = int(round(float(omega_float) * den))
    num = max(1, num)
    while num / den >= cell.omega_end:
        num -= 1
    if num <= 0:
        raise ValueError("failed to quantize interior source coordinate")
    return num, den


def _threshold_record(q: int, N: int, parity: str) -> dict:
    L = arb(q).log()
    _W, _c, B, c2 = _step_basis(N, parity)
    # Continuous left-cell extension.  The q atom is exactly zero at entry.
    M = fixed_q_canonical_source_matrix_arb(L, N + 1, q - 1)
    rec = _schur_record(_restricted(M, B))
    pivot = rec["pivot"]
    if not rec["predecessor_pd"]["certified"]:
        cls = "H1_SCOPE_LOST"
    else:
        cls = _sign_class(pivot)
    return {
        "L": ball_record(L),
        "physical_continuation_Q": q - 1,
        "H1_predecessor_positive_certified": bool(rec["predecessor_pd"]["certified"]),
        "raw_pivot": None if pivot is None else ball_record(pivot),
        "unit_pivot": None if pivot is None else ball_record(pivot / c2),
        "classification": cls,
    }


def _point_record(q: int, N: int, parity: str, omega_num: int, omega_den: int, label: str) -> dict:
    omega = arb(omega_num) / omega_den
    L = arb(q).log() / (1 - omega)
    omega_float = omega_num / omega_den
    L_float = math.log(float(q)) / (1.0 - omega_float)
    physical_Q = int(math.floor(math.exp(L_float)))

    _W, _c, B, c2 = _step_basis(N, parity)
    full = canonical_source_matrix(L, N + 1, physical_Q)
    atom = canonical_entering_atom_arb(q, N + 1, omega)
    background = full - atom
    if not _entrywise_overlap(full, background + atom):
        raise AssertionError("Arb full/background/current-q reconstruction failed")

    full_rec = _schur_record(_restricted(full, B))
    bg_rec = _schur_record(_restricted(background, B))
    full_pivot = full_rec["pivot"]
    bg_pivot = bg_rec["pivot"]
    lift = None if full_pivot is None or bg_pivot is None else full_pivot - bg_pivot

    if not full_rec["predecessor_pd"]["certified"]:
        classification = "H1_SCOPE_LOST"
    elif full_pivot is None:
        classification = "UNRESOLVED"
    elif _sign_class(full_pivot) == "NEGATIVE_CERTIFIED":
        classification = "BAD_SUCCESSOR_CERTIFIED"
    elif _sign_class(full_pivot) == "POSITIVE_CERTIFIED":
        classification = "POSITIVE_CERTIFIED"
    else:
        classification = "UNRESOLVED"

    return {
        "label": label,
        "omega_num": omega_num,
        "omega_den": omega_den,
        "omega": ball_record(omega),
        "L": ball_record(L),
        "physical_integer_cutoff_Q": physical_Q,
        "full_equals_background_plus_current_q_atom": True,
        "H1_full_certified": bool(full_rec["predecessor_pd"]["certified"]),
        "H1_background_certified": bool(bg_rec["predecessor_pd"]["certified"]),
        "full_unit_pivot": None if full_pivot is None else ball_record(full_pivot / c2),
        "background_unit_pivot": None if bg_pivot is None else ball_record(bg_pivot / c2),
        "entry_lift_unit": None if lift is None else ball_record(lift / c2),
        "entry_lift_sign": _sign_class(lift),
        "classification": classification,
        "claim_cap": "RIGOROUS_FINITE_POINT_AUDIT_ONLY",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--discovery", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST171_FB05_THRESHOLD_BARRIER_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=None)
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    discovery = json.loads(args.discovery.read_text(encoding="utf-8"))
    precision = int(args.precision_bits or fixture.get("arb_precision_bits", 256))
    bits = int(fixture.get("source_quantization_bits", 40))
    near_end_fraction = float(fixture.get("near_end_fraction", 0.995))
    set_precision(precision)

    results = []
    bad_certified = []
    for target in fixture["arb_targets"]:
        q, N, parity = _target_key(target)
        disc = _find_discovery_case(discovery, target)
        threshold = _threshold_record(q, N, parity)
        cell = arithmetic_cell(q)

        best = disc["physical_minimum"].get("best")
        candidate_omega = float(best["omega"]) if best is not None else 0.5 * cell.omega_end
        cand_num, cand_den = _quantize_omega(q, candidate_omega, bits)
        end_num, end_den = _quantize_omega(q, near_end_fraction * cell.omega_end, bits)

        points = [
            _point_record(q, N, parity, cand_num, cand_den, "floating_minimum_candidate"),
            _point_record(q, N, parity, end_num, end_den, "near_end_candidate"),
        ]
        for p in points:
            if p["classification"] == "BAD_SUCCESSOR_CERTIFIED":
                bad_certified.append({"target": target, "point": p})

        results.append({
            "target": target,
            "threshold": threshold,
            "points": points,
            "discovery_classification": disc["classification"],
        })

    out = {
        "schema_version": "POST171_FB05_THRESHOLD_BARRIER_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_POINT_BARRIER_REPLAY_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "precision_bits": precision,
        "results": results,
        "bad_successor_certified_count": len(bad_certified),
        "bad_successor_certificates": bad_certified,
        "nonclaims": [
            "Pointwise Arb replay does not certify a whole arithmetic interval.",
            "The floating minimum candidate is not claimed to be the exact minimum.",
            "Positive replay points do not imply whole-cell positivity.",
            "A BAD_SUCCESSOR_CERTIFIED result is finite canonical evidence, not an RH conclusion.",
            "RH remains OPEN."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "precision_bits": precision,
        "bad_successor_certified_count": len(bad_certified),
        "results": results,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
