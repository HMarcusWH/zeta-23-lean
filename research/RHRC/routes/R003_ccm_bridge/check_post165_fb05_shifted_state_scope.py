#!/usr/bin/env python3
"""Deterministic plumbing checks for the post-#165 FB-05 shifted-state tool.

This script checks implementation identities only.  In particular, it does not
assume that a production bad successor exists in a small numerical scan.  The
shifted resolvent is tested at a safe negative parameter on historical smoke
points; actual negative secular-root discovery remains optional experimental
output of the scout.
"""
from __future__ import annotations

import json
import math

import mpmath as mp

from canonical_riesz_endpoint_scalar import canonical_riesz_eight_endpoint_scalar_mp
from canonical_source_numeric import canonical_source_matrix_L
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_geometry_self_check,
    exact_shell_generator,
)
from post165_fb05_shifted_state import (
    centered_moment,
    evaluate_shifted_state,
    mixed_seventh_jet_from_m4,
    source_moment_channel_record,
    shifted_trial_vector,
    zero_shift_ray_agreement,
)


def _assert_small(x: float, scale: float, label: str, rel: float = 2e-7) -> None:
    if abs(float(x)) > rel * max(float(scale), 1.0):
        raise AssertionError(f"{label} too large: {x} at scale {scale}")


def _check_safe_shift(Q: int, L: float, N: int, parity: str, lam: float = -1.0) -> dict:
    K = N + 1
    M = canonical_source_matrix_L(L, K)
    W = centered_predecessor_basis(N, parity)
    c = exact_shell_generator(N, parity)
    u, algebra = shifted_trial_vector(lam, M, W, c)
    unorm = float((u @ u) ** 0.5)

    _assert_small(algebra["predecessor_residual_norm"], unorm, "predecessor residual")
    _assert_small(
        algebra["shell_residual_identity_error"],
        max(abs(algebra["shell_residual"]), abs(algebra["secular_scalar"]), 1.0),
        "shell residual identity",
        rel=2e-8,
    )
    zero_shift = zero_shift_ray_agreement(M, W, c)
    if zero_shift["ray_error"] > 2e-10:
        raise AssertionError("lambda=0 integer-basis and orthonormal Schur rays disagree")

    mp.mp.dps = 70
    s8 = float(canonical_riesz_eight_endpoint_scalar_mp(Q, mp.mpf(str(L))))
    source = None
    h7 = None
    if parity == "even":
        source = source_moment_channel_record(L, K, u)
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
        _assert_small(
            source["signed_channels"]["scalar_shift"],
            max(abs(source["direct"]), 1.0),
            "scalar-shift mixed moment",
            rel=2e-8,
        )
        m4 = centered_moment(u, K, 4)
        h7 = mixed_seventh_jet_from_m4(m4)
        if not math.isfinite(h7):
            raise AssertionError("even safe shift produced nonfinite seventh jet")

    return {
        "Q": Q,
        "L": L,
        "N": N,
        "Kstar": K,
        "parity": parity,
        "lambda": lam,
        "predecessor_residual_norm": algebra["predecessor_residual_norm"],
        "shell_residual_identity_error": algebra["shell_residual_identity_error"],
        "zero_shift_ray_error": zero_shift["ray_error"],
        "source_moment_checked": source is not None,
        "mixed_seventh_jet_checked": h7 is not None,
        "S8": s8,
    }


def main() -> int:
    geometry = exact_geometry_self_check(max_N=6)
    if geometry["status"] != "PASS":
        raise AssertionError("exact parity/shell geometry self-check failed")

    even = _check_safe_shift(2, 3 / 4, 2, "even", lam=-1.0)
    odd = _check_safe_shift(3, 5 / 4, 2, "odd", lam=-1.0)

    # Root existence is intentionally not a plumbing requirement.  Record the
    # historical smoke-point discovery state so CI makes the distinction clear.
    even_root = evaluate_shifted_state(2, 3 / 4, 2, "even")
    odd_root = evaluate_shifted_state(3, 5 / 4, 2, "odd")

    payload = {
        "status": "PASS",
        "safe_shift_checks": [even, odd],
        "historical_smoke_root_discovery": {
            "even_available": bool(even_root["available"]),
            "even_failure": even_root.get("failure"),
            "odd_available": bool(odd_root["available"]),
            "odd_failure": odd_root.get("failure"),
            "interpretation": (
                "Absence of a production bad root at these finite smoke points is not "
                "a plumbing failure and is not a positivity theorem."
            ),
        },
        "claim_firewall": {
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
        },
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
