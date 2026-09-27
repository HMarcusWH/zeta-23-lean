from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys

import numpy as np

SPECIALIZATION_L = 3.7
SPECIALIZATION_CASES = (
    (0, 0, 0.23),
    (1, 0, 0.31),
    (1, 1, 0.19),
    (2, -1, 0.41),
    (-2, 1, 0.67),
)
TAPER_WIDTH_FRACTIONS = (0.08, 0.17, 0.25)

MASKING_LOG_HEIGHT = 12.0
MASKING_LAMBDAS = (0.5, 1.0, 2.0)
MASKING_DELTAS = (0.01, 0.03, 0.06, 0.1, 0.2, 0.4)
PRODUCTION_LAMBDA_MAX = 1.0
SYNTHETIC_SEED = 0
HALFWIDTH_GRID_UNITS = 25


def same_witness_budget(full_hat: np.ndarray, bulk_hat: np.ndarray) -> dict:
    evals, evecs = np.linalg.eigh(full_hat)
    i = int(np.argmin(evals))
    w = evecs[:, i]
    pair_hat = full_hat - bulk_hat
    bulk_q = float(w @ bulk_hat @ w)
    pair_q = float(w @ pair_hat @ w)
    total_q = float(w @ full_hat @ w)
    pair_min = float(np.linalg.eigvalsh(pair_hat).min())
    return {
        "lambda_min_full": float(evals[i]),
        "same_witness_bulk": bulk_q,
        "same_witness_pair": pair_q,
        "same_witness_total": total_q,
        "reconstruction_error": total_q - (bulk_q + pair_q),
        "pair_lambda_min": pair_min,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    repo = Path(args.repo).resolve()
    r002 = repo / "research" / "RHRC" / "routes" / "R002_multi_probe"
    sys.path.insert(0, str(r002))
    from compare_r002_ccm_probe_families import (
        q_basis,
        hard_character_correlation_closed,
        shifted_correlation_numeric,
    )
    from run_negindex_masking import build_gram

    specialization_rows = []
    max_hard = 0.0
    max_smooth = 0.0
    for n, m, y_frac in SPECIALIZATION_CASES:
        y = y_frac * SPECIALIZATION_L
        q = q_basis(n, m, y, SPECIALIZATION_L)
        hard = hard_character_correlation_closed(n, m, y, SPECIALIZATION_L)
        hard_residual = abs(q - hard)
        max_hard = max(max_hard, hard_residual)
        smooth = []
        for frac in TAPER_WIDTH_FRACTIONS:
            value = shifted_correlation_numeric(
                n, m, y, SPECIALIZATION_L,
                taper_width=frac * SPECIALIZATION_L,
                steps=12000,
            )
            residual = abs(q - value)
            max_smooth = max(max_smooth, residual)
            smooth.append({
                "taper_width_fraction": frac,
                "value": value,
                "qBasis_residual": residual,
            })
        specialization_rows.append({
            "n": n,
            "m": m,
            "y_over_L": y_frac,
            "qBasis": q,
            "hard_closed": hard,
            "hard_residual": hard_residual,
            "smooth": smooth,
        })

    if max_hard > 5e-13:
        raise SystemExit(f"hard-window identity regression failed: {max_hard}")

    T = math.exp(MASKING_LOG_HEIGHT) * 2 * math.pi
    masking_rows = []
    for lam in MASKING_LAMBDAS:
        L = lam * MASKING_LOG_HEIGHT
        halfwidth = HALFWIDTH_GRID_UNITS * 2 * math.pi / L
        bulk, _tau, d = build_gram(
            L, MASKING_LOG_HEIGHT, T, halfwidth,
            delta=0.0, gamma_off=T, seed=SYNTHETIC_SEED,
        )
        bulk_hat = bulk / (L ** 2)
        for delta in MASKING_DELTAS:
            full, _tau2, d2 = build_gram(
                L, MASKING_LOG_HEIGHT, T, halfwidth,
                delta=delta, gamma_off=T, seed=SYNTHETIC_SEED,
            )
            if d2 != d:
                raise AssertionError("same-scope masking dimension drift")
            full_hat = full / (L ** 2)
            budget = same_witness_budget(full_hat, bulk_hat)
            masking_rows.append({
                "lambda": lam,
                "L": L,
                "delta": delta,
                "delta_times_L": delta * L,
                "dimension": int(d),
                "production_valid": bool(lam <= PRODUCTION_LAMBDA_MAX),
                "nominal_oversampled_regime": bool(lam > 1.0),
                **budget,
            })

    production_rows = [r for r in masking_rows if r["production_valid"]]
    production_visible = [
        r for r in production_rows if r["lambda_min_full"] < -1e-9
    ]
    specialization_class = (
        "SMOOTH_TAPER_SPECIALIZATION_BARRIER_CONFIRMED"
        if max_smooth > 1e-3
        else "SMOOTH_TAPER_DISTINCTION_UNRESOLVED"
    )
    masking_class = (
        "SYNTHETIC_PRODUCTION_VISIBILITY_OBSERVED_ON_FROZEN_SCOPE"
        if production_visible
        else "SYNTHETIC_PRODUCTION_MASKING_BARRIER_PERSISTS"
    )

    out = {
        "schema_version": "RHRC-CLOSURE-R002-VISIBILITY-AUDIT-2.0",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "adaptive_search": False,
        "scope": {
            "specialization_L": SPECIALIZATION_L,
            "taper_width_fractions": list(TAPER_WIDTH_FRACTIONS),
            "masking_log_height": MASKING_LOG_HEIGHT,
            "masking_lambdas": list(MASKING_LAMBDAS),
            "masking_deltas": list(MASKING_DELTAS),
            "production_lambda_max": PRODUCTION_LAMBDA_MAX,
            "synthetic_seed": SYNTHETIC_SEED,
        },
        "specialization_rows": specialization_rows,
        "masking_rows": masking_rows,
        "max_hard_residual": max_hard,
        "max_smooth_residual": max_smooth,
        "specialization_classification": specialization_class,
        "masking_classification": masking_class,
        "classification": specialization_class + "__" + masking_class,
        "production_visibility_status": "OPEN_THEOREM_SYNTHETIC_SAME_WITNESS_BUDGET_ONLY",
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "The generic smooth R002 family is not identified with the hard-window CCM qBasis.",
            "Synthetic same-witness visibility is not evidence about actual zeta zeros.",
            "lambda>1 rows are explicit out-of-production controls.",
            "No finite masking computation proves R002_WINDOWED_VISIBILITY.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
