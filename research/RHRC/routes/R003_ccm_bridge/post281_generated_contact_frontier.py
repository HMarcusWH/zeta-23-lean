#!/usr/bin/env python3
"""Broad post-#281 generated-contact discovery.

This is deterministic floating discovery, not a proof or interval certificate.
Unlike the historical near-seam panel, it scans every physical integer cutoff
cell Q=1..64, K=2..6, both parity sectors, and all frozen interior fractions.
Candidate selection never uses rho_sat or a preferred Delta sign.

Claim cap: EXPERIMENTAL_SIGNAL_ONLY.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

from canonical_source_numeric import canonical_source_matrix_L
import post280_saturation_frontier as saturation
from post280_saturation_frontier import boundary_flat_parity_basis, planted_increment_float
from run_commutator_gauntlet_v2 import q_basis, von_mangoldt

SCHEMA = "POST281_GENERATED_CONTACT_DISCOVERY_v1"
CLAIM_CAP = "EXPERIMENTAL_SIGNAL_ONLY"


def _frac(pair):
    return float(pair[0]) / float(pair[1])


def validate_protocol(p: dict) -> None:
    if p.get("schema_version") != "POST281_GENERATED_CONTACT_FRONTIER_PROTOCOL_v1":
        raise ValueError("protocol schema drift")
    if p.get("claim_cap") != CLAIM_CAP:
        raise ValueError("claim-cap drift")
    d = p["discovery"]
    if (d["Q_min"], d["Q_max"]) != (1, 64):
        raise ValueError("full-cell discovery scope drift")
    if d["K"] != [2, 3, 4, 5, 6]:
        raise ValueError("K schedule drift")
    if d["interior_fractions"]["denominator"] != 16:
        raise ValueError("interior grid drift")
    if d["interior_fractions"]["numerators"] != list(range(1, 16)):
        raise ValueError("interior numerators drift")
    if "rho_distance_to_one" not in d["forbidden_selection_features"]:
        raise ValueError("selection firewall missing")
    if "preferred_delta_sign" not in d["forbidden_selection_features"]:
        raise ValueError("selection firewall missing")


def cell_bounds(Q: int) -> tuple[float, float]:
    if Q < 1:
        raise ValueError("require Q>=1")
    lo = math.log(float(Q))
    hi = math.log(float(Q + 1))
    if Q == 1:
        lo = 1.0 / 512.0
    return lo, hi


def matrix_for_model(L: float, K: int, model: str, gamma: float, delta: float) -> np.ndarray:
    M = canonical_source_matrix_L(float(L), int(K))
    if model == "canonical":
        return M
    if model == "planted_on_line":
        return M - planted_increment_float(L, K, gamma, 0.0)
    if model == "planted_off_line":
        return M - planted_increment_float(L, K, gamma, delta)
    raise ValueError(f"unknown model {model}")


def parity_spectrum(M: np.ndarray, K: int, parity: str) -> dict:
    U = boundary_flat_parity_basis(K, parity)
    H = (U.T @ M @ U)
    H = (H + H.T) / 2.0
    vals = np.linalg.eigvalsh(H)
    return {
        "bottom": float(vals[0]),
        "second": float(vals[1]) if len(vals) > 1 else None,
        "sector_gap": float(vals[1] - vals[0]) if len(vals) > 1 else None,
        "dimension": int(len(vals)),
    }


def evaluate(L: float, Q: int, K: int, model: str, gamma: float, delta: float) -> dict:
    M = matrix_for_model(L, K, model, gamma, delta)
    even = parity_spectrum(M, K, "even")
    odd = parity_spectrum(M, K, "odd")
    if even["bottom"] < odd["bottom"]:
        selected = "even"
        ground = even["bottom"]
        sector_gap = even["sector_gap"]
    elif odd["bottom"] < even["bottom"]:
        selected = "odd"
        ground = odd["bottom"]
        sector_gap = odd["sector_gap"]
    else:
        selected = "tie_float"
        ground = even["bottom"]
        sector_gap = min(
            x for x in (even["sector_gap"], odd["sector_gap"]) if x is not None
        ) if any(x is not None for x in (even["sector_gap"], odd["sector_gap"])) else None
    return {
        "Q": Q, "K": K, "L": float(L), "model": model,
        "cell_left_symbolic": ("1/512" if Q == 1 else f"log({Q})"),
        "cell_right_symbolic": f"log({Q + 1})",
        "selected_parity_float": selected,
        "global_bottom": float(ground),
        "parity_separation": abs(float(even["bottom"] - odd["bottom"])),
        "selected_sector_gap": sector_gap,
        "even": even, "odd": odd,
        "contact_status": "ORDINARY_STATE",
        "claim_cap": CLAIM_CAP,
    }



def _ground_state(M: np.ndarray, K: int) -> dict:
    data = {}
    for parity in ("even", "odd"):
        U = boundary_flat_parity_basis(K, parity)
        H = (U.T @ M @ U)
        H = (H + H.T) / 2.0
        vals, vecs = np.linalg.eigh(H)
        data[parity] = {
            "bottom": float(vals[0]),
            "vector": U @ vecs[:, 0],
        }
    selected = "even" if data["even"]["bottom"] <= data["odd"]["bottom"] else "odd"
    z = data[selected]["vector"]
    z = z / np.linalg.norm(z)
    return {
        "selected_parity": selected,
        "global_bottom": data[selected]["bottom"],
        "z": z,
        "even_bottom": data["even"]["bottom"],
        "odd_bottom": data["odd"]["bottom"],
    }


def current_prime_atom_matrix(L: float, Q: int, K: int) -> np.ndarray:
    """Unsigned current-Q prime atom; the canonical matrix contains its negative."""
    weight = float(von_mangoldt(int(Q)))
    dim = 2 * K + 1
    if Q < 2 or weight == 0.0:
        return np.zeros((dim, dim), dtype=float)
    y = math.log(float(Q))
    idx = list(range(-K, K + 1))
    atom = np.empty((dim, dim), dtype=float)
    scale = weight / math.sqrt(float(Q))
    for r, n in enumerate(idx):
        for c, m in enumerate(idx):
            atom[r, c] = scale * float(q_basis(n, m, y, L))
    return (atom + atom.T) / 2.0


def current_prime_interventions(L: float, Q: int, K: int) -> dict:
    """Frozen-state and reoptimized removal of the current Q atom.

    This is floating research evidence only.  Removing the atom changes the
    canonical matrix by +atom because the production prime channel is subtracted.
    """
    M = canonical_source_matrix_L(float(L), int(K))
    atom = current_prime_atom_matrix(float(L), int(Q), int(K))
    ablated = M + atom
    base = _ground_state(M, K)
    after = _ground_state(ablated, K)
    z = base["z"]
    frozen_before = float(z @ M @ z)
    frozen_after = float(z @ ablated @ z)
    return {
        "Q": int(Q),
        "K": int(K),
        "von_mangoldt_weight": float(von_mangoldt(int(Q))),
        "atom_fro_norm": float(np.linalg.norm(atom, "fro")),
        "frozen_state": {
            "selected_parity": base["selected_parity"],
            "energy_before": frozen_before,
            "energy_after_removal": frozen_after,
            "energy_shift": frozen_after - frozen_before,
        },
        "reoptimized": {
            "global_bottom_before": base["global_bottom"],
            "global_bottom_after_removal": after["global_bottom"],
            "global_bottom_shift": after["global_bottom"] - base["global_bottom"],
            "selected_parity_before": base["selected_parity"],
            "selected_parity_after": after["selected_parity"],
        },
        "authority": "EXPERIMENTAL_FLOATING_ABLATION_ONLY",
    }


def generic_contact_controls() -> list[dict]:
    """Small generic crossing/touch controls that must not inherit zeta authority."""
    eps = 2.0 ** -8
    controls = [
        ("TRANSVERSE_CROSSING", lambda t: t, lambda t: 1.0),
        ("STATIONARY_CUBIC_CROSSING", lambda t: t ** 3, lambda t: 1.0),
        ("POSITIVE_QUARTIC_TOUCH", lambda t: t ** 4, lambda t: 1.0),
        ("PARITY_TIE", lambda t: t, lambda t: -t),
        ("ODD_SELECTED_REFLECTION", lambda t: 1.0, lambda t: -t),
        ("SMALLEST_COMPLEMENT", lambda t: t, lambda t: 2.0),
    ]
    out = []
    for name, even_f, odd_f in controls:
        samples = []
        for t in (-eps, 0.0, eps):
            e, o = float(even_f(t)), float(odd_f(t))
            samples.append({
                "t": t,
                "even_bottom": e,
                "odd_bottom": o,
                "global_bottom": min(e, o),
            })
        out.append({
            "model": "GENERIC_SYNTHETIC",
            "control_name": name,
            "samples": samples,
            "canonical_arithmetic_authority": False,
            "claim_cap": CLAIM_CAP,
        })
    return out


def candidate_frontier_proxy(cand: dict) -> dict:
    """Attach the inherited #281 floating Q/remainder/Delta diagnostic."""
    L = cand.get("L")
    if L is None:
        L = (float(cand["L_left"]) + float(cand["L_right"])) / 2.0
    Q = int(cand["Q"])
    K = int(cand["K"])
    row = saturation.evaluate(float(L), K)
    keep = {
        "L": float(L),
        "Q": Q,
        "K": K,
        "classification": row["classification"],
        "lambda_even": row["lambda_even"],
        "lambda_odd": row["lambda_odd"],
        "lambda_prime_fd": row["lambda_prime_fd"],
        "fixed_vector_second_fd": row["fixed_vector_second_fd"],
        "kappa_fd": row["kappa_fd"],
        "M4": row["M4"],
        "source_moment_S": row["source_moment_S"],
        "Q_arithmetic": row["Q_arithmetic"],
        "Q_spectral_reduced": row["Q_spectral_reduced"],
        "Q_representation_status": row["Q_representation_status"],
        "production_arithmetic_remainder": row["production_arithmetic_remainder"],
        "production_remainder_integral_error_estimate": row["production_remainder_integral_error_estimate"],
        "delta_sat_proxy": row["delta_sat_proxy"],
        "delta_minus_kappa_fd": row["delta_minus_kappa_fd"],
        "contact_status": "NEAR_CONTACT_PROXY",
        "authority": "EXPERIMENTAL_FLOATING_PROXY_ONLY",
    }
    keep["current_prime_interventions"] = current_prime_interventions(float(L), Q, K)
    return keep


def discover(protocol: dict) -> dict:
    validate_protocol(protocol)
    d = protocol["discovery"]
    gamma = _frac(d["planted_gamma"])
    off_delta = _frac(d["planted_off_line_delta"])
    denom = d["interior_fractions"]["denominator"]
    nums = d["interior_fractions"]["numerators"]
    rows = []
    canonical_by_qk = {}
    for Q in range(d["Q_min"], d["Q_max"] + 1):
        lo, hi = cell_bounds(Q)
        for K in d["K"]:
            key = (Q, K)
            canonical_by_qk[key] = []
            for j in nums:
                L = lo + (hi - lo) * (j / denom)
                for model in d["models"]:
                    row = evaluate(L, Q, K, model, gamma, off_delta)
                    row["cell_fraction"] = [j, denom]
                    rows.append(row)
                    if model == "canonical":
                        canonical_by_qk[key].append(row)

    sign_brackets = []
    for (Q, K), group in canonical_by_qk.items():
        for a, b in zip(group, group[1:]):
            ga, gb = a["global_bottom"], b["global_bottom"]
            if ga == 0.0 or gb == 0.0 or (ga < 0.0 < gb) or (gb < 0.0 < ga):
                sign_brackets.append({
                    "reason": "sign_bracket", "Q": Q, "K": K,
                    "L_left": a["L"], "L_right": b["L"],
                    "fraction_left": a["cell_fraction"],
                    "fraction_right": b["cell_fraction"],
                    "cell_left_symbolic": (
                        "1/512" if Q == 1 else f"log({Q})"
                    ),
                    "cell_right_symbolic": f"log({Q + 1})",
                    "g_left": ga, "g_right": gb,
                })

    canonical = [r for r in rows if r["model"] == "canonical"]
    cap = int(d["additional_neighborhood_cap"])
    quota = d.get("selection_quota", {
        "sign_bracket": 4,
        "ground_magnitude": 3,
        "parity_separation": 2,
        "sector_gap": 2,
        "dimension_diversity": 1,
    })
    if sum(int(v) for v in quota.values()) != cap:
        raise ValueError("selection quotas must sum to additional_neighborhood_cap")

    selected = []
    used = set()

    def rec_key(rec):
        return (rec["Q"], rec["K"], rec.get("L", rec.get("L_left")))

    def add(rec):
        key = rec_key(rec)
        if key not in used and len(selected) < cap:
            used.add(key)
            selected.append(rec)
            return True
        return False

    def stratified_take(records, limit, sort_key):
        by_k = {K: [] for K in d["K"]}
        for rec in records:
            by_k.setdefault(rec["K"], []).append(rec)
        for K in by_k:
            by_k[K].sort(key=sort_key)
        taken = 0
        while taken < limit:
            progressed = False
            for K in d["K"]:
                while by_k.get(K):
                    rec = by_k[K].pop(0)
                    if add(rec):
                        taken += 1
                        progressed = True
                        break
                if taken >= limit:
                    break
            if not progressed:
                break

    bracket_records = [dict(b) for b in sign_brackets]
    stratified_take(
        bracket_records,
        int(quota["sign_bracket"]),
        lambda x: (x["Q"], x["L_left"]),
    )

    criteria = [
        ("ground_magnitude", lambda r: abs(r["global_bottom"])),
        ("parity_separation", lambda r: r["parity_separation"]),
        ("sector_gap", lambda r: float("inf") if r["selected_sector_gap"] is None
            else abs(r["selected_sector_gap"])),
    ]
    for reason, keyfun in criteria:
        records = [{
            "reason": reason, "Q": r["Q"], "K": r["K"], "L": r["L"],
            "cell_fraction": r["cell_fraction"],
            "cell_left_symbolic": ("1/512" if r["Q"] == 1 else f"log({r['Q']})"),
            "cell_right_symbolic": f"log({r['Q'] + 1})",
            "global_bottom": r["global_bottom"],
            "parity_separation": r["parity_separation"],
            "selected_sector_gap": r["selected_sector_gap"],
        } for r in canonical]
        stratified_take(
            records,
            int(quota[reason]),
            lambda x, _kf=keyfun: (
                _kf(next(r for r in canonical
                    if r["Q"] == x["Q"] and r["K"] == x["K"] and r["L"] == x["L"])),
                x["Q"], x["L"],
            ),
        )

    represented = {r["K"] for r in selected}
    diversity_records = []
    for K in d["K"]:
        if K in represented:
            continue
        candidates = [r for r in canonical if r["K"] == K]
        if candidates:
            r = min(candidates, key=lambda x:(abs(x["global_bottom"]),x["Q"],x["L"]))
            diversity_records.append({
                "reason":"dimension_diversity","Q":r["Q"],"K":r["K"],"L":r["L"],
                "cell_fraction":r["cell_fraction"],
                "cell_left_symbolic":("1/512" if r["Q"]==1 else f"log({r['Q']})"),
                "cell_right_symbolic":f"log({r['Q']+1})",
                "global_bottom":r["global_bottom"],
                "parity_separation":r["parity_separation"],
                "selected_sector_gap":r["selected_sector_gap"],
            })
    stratified_take(
        diversity_records,
        int(quota["dimension_diversity"]),
        lambda x:(abs(x["global_bottom"]),x["Q"],x["L"]),
    )

    selected_diagnostics = [
        {
            "candidate": rec,
            "frontier_proxy": candidate_frontier_proxy(rec),
        }
        for rec in selected
    ]

    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "protocol": protocol,
        "measurements": rows,
        "sign_brackets": sign_brackets,
        "selected_neighborhoods": selected,
        "selected_diagnostics": selected_diagnostics,
        "generic_controls": generic_contact_controls(),
        "summary": {
            "measurement_count": len(rows),
            "canonical_count": len(canonical),
            "planted_count": len(rows) - len(canonical),
            "sign_bracket_count": len(sign_brackets),
            "selected_count": len(selected),
            "selected_diagnostic_count": len(selected_diagnostics),
            "generic_control_count": len(generic_contact_controls()),
            "contact_claimed": False,
            "terminal_claim": "RH_OPEN",
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    protocol = json.loads(Path(args.input).read_text(encoding="utf-8"))
    out = discover(protocol)
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    print(json.dumps(out["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
