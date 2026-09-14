#!/usr/bin/env python3
"""Deterministic plumbing checks for the post-#165 FB-05 shifted-state tool.

This script checks implementation identities only.  It deliberately does not
require a favorable arithmetic sign or a new theorem-like pattern.
"""
from __future__ import annotations

import json
import math

import mpmath as mp

from canonical_riesz_endpoint_scalar import canonical_riesz_eight_endpoint_scalar_mp
from canonical_source_numeric import dyadic_inside_fixed_cell
from post150_selected_residual import exact_geometry_self_check
from post165_fb05_shifted_state import evaluate_shifted_state


def _assert_small(x: float, scale: float, label: str, rel: float = 2e-7) -> None:
    if abs(float(x)) > rel * max(float(scale), 1.0):
        raise AssertionError(f"{label} too large: {x} at scale {scale}")


def _check_state(rec: dict) -> None:
    if not rec["available"]:
        raise AssertionError("attempted to check unavailable shifted state")
    sec = rec["secular"]
    if not sec["lambda"] < 0:
        raise AssertionError("shifted secular root is not negative")
    eig_scale = max(abs(sec["lambda"]), abs(sec["selected_successor_min_eigenvalue"]), 1.0)
    _assert_small(sec["root_eigenvalue_error"], eig_scale, "root/eigenvalue agreement")
    _assert_small(sec["predecessor_residual_norm"], rec["trial"]["norm"], "predecessor residual")
    _assert_small(
        sec["shell_residual_identity_error"],
        max(abs(sec["shell_residual"]), abs(sec["lambda"]), 1.0),
        "shell residual identity",
        rel=2e-8,
    )
    if rec["zero_shift_crosscheck"]["ray_error"] > 2e-10:
        raise AssertionError("lambda=0 integer-basis and orthonormal Schur rays disagree")

    mp.mp.dps = 70
    s8 = float(
        canonical_riesz_eight_endpoint_scalar_mp(
            int(rec["Q"]), mp.mpf(str(rec["L"]))
        )
    )
    _assert_small(s8 - rec["endpoint_scalar"]["S8"], abs(s8), "S8 reuse", rel=1e-12)

    if rec["parity"] == "even":
        source = rec["explicit_source_moment"]
        _assert_small(
            source["reconstruction_error"],
            max(abs(source["direct"]), abs(source["sum"]), 1.0),
            "source-moment channel reconstruction",
            rel=2e-8,
        )
        _assert_small(
            source["arch_split_error"],
            max(abs(source["signed_channels"]["arch_signed"]), 1.0),
            "arch source-moment split",
            rel=2e-8,
        )
        # n2 is orthogonal to every even boundary-flat trial, so an identity
        # scalar shift must vanish in this mixed pairing.
        _assert_small(
            source["signed_channels"]["scalar_shift"],
            max(abs(source["direct"]), 1.0),
            "scalar-shift mixed moment",
            rel=2e-8,
        )
        if not math.isfinite(rec["trial"]["mixed_seventh_jet"]):
            raise AssertionError("even shifted state produced nonfinite seventh jet")
    else:
        if rec["explicit_source_moment"] is not None:
            raise AssertionError("odd-selected state incorrectly received even source-moment theorem data")
        if rec["trial"]["mixed_seventh_jet"] is not None:
            raise AssertionError("odd-selected state incorrectly received even seventh-jet theorem data")


def _search_available_even_state() -> dict:
    # Start with the historical smoke point, then broaden deterministically.
    seeds = [(2, 3, 4, 2, "even")]
    for Q in range(2, 7):
        for pos in (0.3, 0.5, 0.7):
            num, den = dyadic_inside_fixed_cell(Q, pos, bits=34)
            for N in range(2, 6):
                seeds.append((Q, num, den, N, "even"))
    seen = set()
    for Q, num, den, N, parity in seeds:
        key = (Q, num, den, N, parity)
        if key in seen:
            continue
        seen.add(key)
        rec = evaluate_shifted_state(Q, num / den, N, parity)
        if rec["available"]:
            return rec
    raise AssertionError("no even shifted secular state found in deterministic plumbing search")


def main() -> int:
    geometry = exact_geometry_self_check(max_N=6)
    if geometry["status"] != "PASS":
        raise AssertionError("exact parity/shell geometry self-check failed")

    even = _search_available_even_state()
    _check_state(even)

    # Exercise the odd firewall at the same aperture/size when a shifted odd
    # state exists.  Absence is not a mathematical failure.
    odd = evaluate_shifted_state(even["Q"], even["L"], even["N"], "odd")
    if odd["available"]:
        _check_state(odd)

    payload = {
        "status": "PASS",
        "checked_even_state": {
            "Q": even["Q"],
            "L": even["L"],
            "N": even["N"],
            "lambda": even["secular"]["lambda"],
            "opposite_parity": even["opposite_parity"]["classification"],
        },
        "checked_odd_state": bool(odd["available"]),
        "claim_firewall": {
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
        },
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
