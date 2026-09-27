from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from flint import arb, arb_mat, ctx


# Physical cutoff cells used by the theorem-aligned fixed-Q continuation.
# Q=12 supplies the left side of the q=13 threshold; 14,15,18 are deliberately
# retained zero-von-Mangoldt controls rather than mislabeled arithmetic
# thresholds.
PHYSICAL_Q = (12, 13, 14, 15, 16, 17, 18, 19)
TRUE_VM_THRESHOLDS = (13, 16, 17, 19)
ZERO_WEIGHT_CONTROLS = (14, 15, 18)
SUCCESSOR_K = (3, 4, 6)
PARITIES = ("even", "odd")
DEN = 4
PREC = 256


def _leading_block(H: arb_mat, k: int) -> arb_mat:
    return arb_mat([[H[r, c] for c in range(k)] for r in range(k)])


def _leading_minors(H: arb_mat) -> list[arb]:
    return [_leading_block(H, k).det() for k in range(1, H.nrows() + 1)]


def _all_exact_zero(xs: list[arb]) -> bool:
    return all(x.is_zero() for x in xs)


def _schur_form(H: arb_mat) -> tuple[arb, list[arb], arb_mat]:
    """Return q_c, coupling b, and q_c*A - b*b^T.

    In the exact [W|c] coordinates used by Lean's
    canonicalOneStepDomination, nonnegativity of the returned predecessor form
    for every w is exactly the denominator-free determinant condition.
    """
    n = H.nrows()
    if n != H.ncols() or n < 1:
        raise ValueError("expected nonempty square one-step restriction")
    d = H[n - 1, n - 1]
    if n == 1:
        return d, [], arb_mat(0, 0)
    b = [H[i, n - 1] for i in range(n - 1)]
    S = arb_mat(n - 1, n - 1)
    for i in range(n - 1):
        for j in range(n - 1):
            S[i, j] = d * H[i, j] - b[i] * b[j]
    return d, b, S


def _classify(d: arb, b: list[arb], S: arb_mat, definitely_positive, definitely_negative) -> tuple[str, str]:
    # Failure certificates first: negative shell, or an explicit coordinate
    # predecessor with negative determinant form.
    if definitely_negative(d):
        return "CERTIFIED_CANONICAL_DOMINATION_FAILURE", "NEGATIVE_SHELL_ENERGY"
    for i in range(S.nrows()):
        if definitely_negative(S[i, i]):
            return "CERTIFIED_CANONICAL_DOMINATION_FAILURE", f"NEGATIVE_COORDINATE_DETERMINANT_{i}"

    # Exact singular compatibility is a real certificate: q_c=0 and b=0 makes
    # the determinant form identically zero, regardless of predecessor A.
    if d.is_zero():
        if _all_exact_zero(b):
            return "SINGULAR_COMPATIBLE", "EXACT_ZERO_SHELL_AND_COUPLING"
        if any(not z.contains(0) for z in b):
            return "SINGULAR_BAD_COUPLING", "EXACT_ZERO_SHELL_NONZERO_COUPLING"
        return "UNRESOLVED", "SINGULAR_COUPLING_INTERVAL_CONTAINS_ZERO"

    # Strict positivity of all leading minors is a sufficient, rigorous
    # positive-definite certificate for the determinant form.  We intentionally
    # do not call nonnegative leading minors a PSD certificate.
    if definitely_positive(d):
        minors = _leading_minors(S)
        if all(definitely_positive(x) for x in minors):
            return "CERTIFIED_CANONICAL_DOMINATION", "STRICT_SCHUR_FORM_POSITIVE"

    return "UNRESOLVED", "INTERVAL_SIGN_NOT_DECIDED"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    repo = Path(args.repo).resolve()
    r003 = repo / "research" / "RHRC" / "routes" / "R003_ccm_bridge"
    sys.path.insert(0, str(r003))

    from canonical_source_arb import ball_record, definitely_negative, definitely_positive, von_mangoldt
    from post166_fb05_cell_interval import (
        _arb_matrix_from_sympy,
        arb_unit_interval,
        cell_coordinate_L_arb,
    )
    from post169_fb05_schur_visibility import one_step_geometry
    from post175_fb05_q13_fixed_unit_enclosure import (
        fixed_unit_fixed_q_canonical_source_matrix_arb,
    )

    ctx.prec = PREC
    rows: list[dict] = []

    for Q in PHYSICAL_Q:
        for K in SUCCESSOR_K:
            N = K - 1
            for parity in PARITIES:
                geom = one_step_geometry(N, parity)
                B = _arb_matrix_from_sympy(geom.step_basis_exact)
                for lo in range(DEN):
                    t = arb_unit_interval(lo, lo + 1, DEN)
                    L = cell_coordinate_L_arb(Q, t)
                    M = fixed_unit_fixed_q_canonical_source_matrix_arb(L, K, Q)
                    H = B.transpose() * M * B
                    d, b, S = _schur_form(H)
                    classification, reason = _classify(
                        d, b, S, definitely_positive, definitely_negative
                    )
                    minors = _leading_minors(S) if S.nrows() else []
                    vm = von_mangoldt(Q)
                    rows.append({
                        "Q": Q,
                        "N": N,
                        "Kstar": K,
                        "parity": parity,
                        "segment": {"lo": lo, "hi": lo + 1, "den": DEN},
                        "t_ball": ball_record(t),
                        "L_ball": ball_record(L),
                        "von_mangoldt_Q": ball_record(vm),
                        "Q_role": (
                            "TRUE_VM_THRESHOLD" if Q in TRUE_VM_THRESHOLDS
                            else "ZERO_WEIGHT_CONTROL" if Q in ZERO_WEIGHT_CONTROLS
                            else "PHYSICAL_CELL_CONTEXT"
                        ),
                        "shell_energy": ball_record(d),
                        "coupling": [ball_record(x) for x in b],
                        "schur_form_leading_minors": [ball_record(x) for x in minors],
                        "classification": classification,
                        "reason": reason,
                    })

    counts = Counter(r["classification"] for r in rows)
    bad = counts["CERTIFIED_CANONICAL_DOMINATION_FAILURE"] + counts["SINGULAR_BAD_COUPLING"]
    good = counts["CERTIFIED_CANONICAL_DOMINATION"] + counts["SINGULAR_COMPATIBLE"]

    out = {
        "schema_version": "RHRC-CLOSURE-CANONICAL-SCHUR-ARB-2.0",
        "claim_cap": "RIGOROUS_BOUNDED_ARB_RESEARCH",
        "adaptive_search": False,
        "precision_bits": PREC,
        "backend": "FIXED_UNIT_CANONICAL_ARB",
        "scope": {
            "physical_Q": list(PHYSICAL_Q),
            "true_von_mangoldt_thresholds": list(TRUE_VM_THRESHOLDS),
            "zero_weight_controls": list(ZERO_WEIGHT_CONTROLS),
            "successor_K": list(SUCCESSOR_K),
            "predecessor_N": [k - 1 for k in SUCCESSOR_K],
            "parities": list(PARITIES),
            "segments_per_cell": DEN,
        },
        "rows": rows,
        "classification_counts": dict(counts),
        # Compatibility keys consumed by the existing integration/replay layer.
        "selected_classification_counts": dict(counts),
        "scope_classification_counts": dict(counts),
        "certified_bad_interval_count": int(bad),
        "certified_domination_interval_count": int(good),
        "classification": (
            "CANONICAL_DOMINATION_FAILURE_CERTIFIED_ON_FROZEN_SCOPE"
            if bad else
            "CANONICAL_DOMINATION_CERTIFIED_ON_SOME_FROZEN_INTERVALS"
            if good else
            "CANONICAL_SCHUR_SCOPE_UNRESOLVED"
        ),
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "Finite interval certificates do not prove all-parameter CanonicalUniformDomination.",
            "UNRESOLVED is not evidence for domination.",
            "Q=14,15,18 are physical-cell zero-weight controls, not arithmetic threshold starts.",
            "Only rigorous Arb sign separation creates a frozen-scope disposition.",
            "The fixed-unit evaluator is the theorem-aligned production representation selected by the historical enclosure audits.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
