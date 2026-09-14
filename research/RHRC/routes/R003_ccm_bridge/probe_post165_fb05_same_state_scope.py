#!/usr/bin/env python3
"""Broad floating scout for post-#165 FB-05 same-state arithmetic restrictions.

The scout deliberately ranks adversarial shifted states: simultaneous parity
badness, large source-channel cancellation, sourceMoment/M4 scale separation,
and small endpoint scalars.  When no bad successor is found it also retains the
H1 states whose successor eigenvalue is closest to zero, so a negative result
still tells us whether the sampled finite regime is near the first-bad boundary.

This is a discovery engine only.  Any actual shifted candidate worth keeping
must be replayed with Arb by ``certify_post165_fb05_same_state_scope.py``.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from canonical_source_numeric import dyadic_inside_fixed_cell
from post165_fb05_shifted_state import evaluate_shifted_state


def _safe_log10_ratio(a: float, b: float) -> float:
    aa = max(abs(float(a)), 1e-300)
    bb = max(abs(float(b)), 1e-300)
    return math.log10(aa / bb)


def _candidate_score(rec: dict) -> tuple[float, dict]:
    score = 0.0
    tags: list[str] = []
    if rec["post150_scope"]["H3_all_smaller_sizes_both_parities_good_same_aperture"]:
        score += 100.0
        tags.append("H3_SIGNAL")
    elif rec["post150_scope"]["H2_selected_successor_bad"]:
        score += 35.0
        tags.append("H2_SIGNAL")

    opposite = rec["opposite_parity"]["classification"]
    if opposite == "BAD_SIGNAL":
        score += 60.0
        tags.append("SIMULTANEOUS_PARITY_BAD_SIGNAL")
    elif opposite == "NEAR_ZERO":
        score += 25.0
        tags.append("OPPOSITE_PARITY_NEAR_ZERO")

    s8 = abs(float(rec["endpoint_scalar"]["S8"]))
    if s8 > 0:
        small_s8 = max(0.0, -math.log10(s8))
        score += min(20.0, 2.0 * small_s8)
        if small_s8 >= 3:
            tags.append("SMALL_S8_SIGNAL")

    diagnostics = {
        "opposite_parity": opposite,
        "abs_S8": s8,
    }

    if rec["parity"] == "even":
        src = rec["explicit_source_moment"]
        m4n = float(src["normalized_abs_m4"])
        smn = float(src["normalized_abs_source_moment"])
        channels = src["signed_channels"]
        numerator = sum(
            abs(float(channels[name]))
            for name in ("pole", "arch_signed", "prime_signed", "scalar_shift")
        )
        cancellation = numerator / max(abs(float(src["direct"])), 1e-300)
        separation = abs(_safe_log10_ratio(m4n, smn))
        score += min(30.0, 3.0 * max(0.0, math.log10(max(cancellation, 1.0))))
        score += min(30.0, 4.0 * separation)
        if cancellation >= 1e3:
            tags.append("SOURCE_CHANNEL_CANCELLATION_SIGNAL")
        if separation >= 3:
            tags.append("SOURCE_MOMENT_M4_SCALE_SEPARATION_SIGNAL")
        diagnostics.update(
            {
                "normalized_abs_M4": m4n,
                "normalized_abs_source_moment": smn,
                "source_channel_cancellation_ratio": cancellation,
                "log10_M4_source_separation": separation,
            }
        )
    else:
        tags.append("ODD_SELECTED_STRESS_STATE")

    return score, {"tags": tags, **diagnostics}


def _compact_candidate(rec: dict, L_num: int, L_den: int) -> dict:
    score, diagnostics = _candidate_score(rec)
    return {
        "score": score,
        "Q": int(rec["Q"]),
        "L_num": int(L_num),
        "L_den": int(L_den),
        "L": float(rec["L"]),
        "N": int(rec["N"]),
        "Kstar": int(rec["Kstar"]),
        "parity": rec["parity"],
        "lambda": float(rec["secular"]["lambda"]),
        "selected_bad_witness_coeffs_in_exact_successor_basis": rec[
            "selected_bad_witness_coeffs_in_exact_successor_basis"
        ],
        "opposite_bad_witness_coeffs_in_exact_successor_basis": rec["opposite_parity"].get(
            "bad_witness_coeffs_in_exact_successor_basis"
        ),
        "scope": rec["post150_scope"],
        "diagnostics": diagnostics,
        "trial": rec["trial"],
        "explicit_source_moment": rec["explicit_source_moment"],
        "opposite_parity": rec["opposite_parity"],
        "endpoint_scalar": rec["endpoint_scalar"],
    }


def _compact_margin(rec: dict, L_num: int, L_den: int) -> dict | None:
    """Keep H1 states near the successor sign boundary even without a bad root."""
    if not rec["post150_scope"]["H1_predecessor_positive"]:
        return None
    eig = rec["selected_successor"].get("min_form_eigenvalue")
    if eig is None or not math.isfinite(float(eig)):
        return None
    return {
        "Q": int(rec["Q"]),
        "L_num": int(L_num),
        "L_den": int(L_den),
        "L": float(rec["L"]),
        "N": int(rec["N"]),
        "Kstar": int(rec["Kstar"]),
        "parity": rec["parity"],
        "successor_min_form_eigenvalue": float(eig),
        "absolute_margin_to_zero": abs(float(eig)),
        "zero_shift_schur_energy": float(
            rec["zero_shift_selected_residual"]["schur_energy"]
        ),
        "zero_shift_direct_trial_energy": float(
            rec["zero_shift_selected_residual"]["direct_trial_energy"]
        ),
        "scope_highest": rec["post150_scope"]["highest"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q-min", type=int, default=2)
    ap.add_argument("--q-max", type=int, default=12)
    ap.add_argument("--n-min", type=int, default=2)
    ap.add_argument("--n-max", type=int, default=5)
    ap.add_argument("--samples", type=int, default=3)
    ap.add_argument("--top", type=int, default=20)
    ap.add_argument("--dyadic-bits", type=int, default=40)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST165_FB05_SAME_STATE_DISCOVERY.json"),
    )
    args = ap.parse_args()

    if args.q_min < 1 or args.q_max < args.q_min:
        raise ValueError("invalid Q range")
    if args.n_min < 1 or args.n_max < args.n_min:
        raise ValueError("invalid N range")
    if args.samples < 1:
        raise ValueError("samples must be positive")

    candidates = []
    margins = []
    attempted = 0
    unavailable = 0
    for Q in range(args.q_min, args.q_max + 1):
        for j in range(args.samples):
            pos = (j + 1) / (args.samples + 1)
            num, den = dyadic_inside_fixed_cell(Q, pos, bits=args.dyadic_bits)
            L = num / den
            for N in range(args.n_min, args.n_max + 1):
                for parity in ("even", "odd"):
                    attempted += 1
                    rec = evaluate_shifted_state(Q, L, N, parity)
                    margin = _compact_margin(rec, num, den)
                    if margin is not None:
                        margins.append(margin)
                    if not rec["available"]:
                        unavailable += 1
                        continue
                    candidates.append(_compact_candidate(rec, num, den))

    candidates.sort(key=lambda x: (-float(x["score"]), x["Q"], x["N"], x["parity"]))
    top = candidates[: args.top]
    margins.sort(
        key=lambda x: (
            float(x["absolute_margin_to_zero"]),
            x["Q"],
            x["N"],
            x["parity"],
        )
    )
    closest = margins[: args.top]
    minimum_sampled = min(
        margins,
        key=lambda x: (
            float(x["successor_min_form_eigenvalue"]),
            x["Q"],
            x["N"],
            x["parity"],
        ),
        default=None,
    )

    payload = {
        "schema_version": "POST165_FB05_SAME_STATE_DISCOVERY_v1",
        "status": "PASS",
        "phase": "FLOATING_FALSIFICATION_SCOUT",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "search": {
            "q_min": args.q_min,
            "q_max": args.q_max,
            "n_min": args.n_min,
            "n_max": args.n_max,
            "samples_per_cell": args.samples,
            "dyadic_bits": args.dyadic_bits,
            "attempted_states": attempted,
            "unavailable_states": unavailable,
            "h1_margin_states": len(margins),
            "shifted_states": len(candidates),
        },
        "minimum_sampled_successor_eigenvalue": minimum_sampled,
        "closest_to_zero_successor_margins": closest,
        "top_candidates": top,
        "nonclaims": [
            "Candidate and margin ranking is exploratory and not theorem authority.",
            "A positive sampled successor margin is not a whole-cell positivity certificate.",
            "A floating sign is not a certificate.",
            "No sourceMoment/M4 implication is promoted by this scout.",
            "No endpoint-scalar global sign theorem is promoted by this scout.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    print(
        json.dumps(
            {
                "status": payload["status"],
                "attempted_states": attempted,
                "h1_margin_states": len(margins),
                "shifted_states": len(candidates),
                "minimum_sampled_successor_eigenvalue": minimum_sampled,
                "closest_to_zero_successor_margins": closest,
                "top_candidates": [
                    {
                        "score": c["score"],
                        "Q": c["Q"],
                        "L_num": c["L_num"],
                        "L_den": c["L_den"],
                        "N": c["N"],
                        "parity": c["parity"],
                        "lambda": c["lambda"],
                        "tags": c["diagnostics"]["tags"],
                        "selected_bad_witness": c[
                            "selected_bad_witness_coeffs_in_exact_successor_basis"
                        ],
                        "opposite_bad_witness": c[
                            "opposite_bad_witness_coeffs_in_exact_successor_basis"
                        ],
                    }
                    for c in top
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
