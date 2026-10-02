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
from post280_saturation_frontier import boundary_flat_parity_basis, planted_increment_float

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
        "selected_parity_float": selected,
        "global_bottom": float(ground),
        "parity_separation": abs(float(even["bottom"] - odd["bottom"])),
        "selected_sector_gap": sector_gap,
        "even": even, "odd": odd,
        "contact_status": "ORDINARY_STATE",
        "claim_cap": CLAIM_CAP,
    }


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
                    "g_left": ga, "g_right": gb,
                })

    canonical = [r for r in rows if r["model"] == "canonical"]
    cap = int(d["additional_neighborhood_cap"])
    selected = []
    used = set()

    def add(rec):
        key = (rec["Q"], rec["K"], rec.get("L", rec.get("L_left")))
        if key not in used and len(selected) < cap:
            used.add(key)
            selected.append(rec)

    for b in sorted(sign_brackets, key=lambda x:(x["Q"],x["K"],x["L_left"])):
        add(dict(b))

    criteria = [
        ("ground_magnitude", lambda r: abs(r["global_bottom"])),
        ("parity_separation", lambda r: r["parity_separation"]),
        ("sector_gap", lambda r: float("inf") if r["selected_sector_gap"] is None else abs(r["selected_sector_gap"])),
    ]
    for reason, keyfun in criteria:
        for r in sorted(canonical, key=lambda x:(keyfun(x), x["K"], x["Q"], x["L"])):
            add({
                "reason": reason, "Q": r["Q"], "K": r["K"], "L": r["L"],
                "global_bottom": r["global_bottom"],
                "parity_separation": r["parity_separation"],
                "selected_sector_gap": r["selected_sector_gap"],
            })
            if len(selected) >= cap:
                break
        if len(selected) >= cap:
            break

    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "protocol": protocol,
        "measurements": rows,
        "sign_brackets": sign_brackets,
        "selected_neighborhoods": selected,
        "summary": {
            "measurement_count": len(rows),
            "canonical_count": len(canonical),
            "planted_count": len(rows) - len(canonical),
            "sign_bracket_count": len(sign_brackets),
            "selected_count": len(selected),
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
