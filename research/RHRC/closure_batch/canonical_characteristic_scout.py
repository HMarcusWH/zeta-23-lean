from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

from flint import acb, acb_mat, arb, arb_mat, ctx, fmpq

FROZEN_L = (2, 3, 4)
FROZEN_Q = (7, 20, 54)
FROZEN_K = (3, 4, 6, 8)
FROZEN_Z = (
    ("0", "1/4"),
    ("0", "1/2"),
    ("1/2", "1/4"),
    ("1", "1/2"),
    ("-1/2", "3/4"),
)
PREC = 192


def arb_from_fraction_text(value: str) -> arb:
    q = Fraction(value)
    return arb(fmpq(q.numerator, q.denominator))


def z_from_spec(spec: tuple[str, str]) -> acb:
    return acb(arb_from_fraction_text(spec[0]), arb_from_fraction_text(spec[1]))


def z_scope_records() -> list[dict[str, str]]:
    return [{"re": re, "im": im} for re, im in FROZEN_Z]


def acb_contains_zero(z: acb) -> bool:
    return bool(z.real.contains(0) and z.imag.contains(0))


def abs_ball(z: acb) -> arb:
    return (z.real * z.real + z.imag * z.imag).sqrt()


def arb_record(x: arb) -> dict:
    return {
        "ball": x.str(45, more=True),
        "lower": x.lower().str(55, radius=False),
        "upper": x.upper().str(55, radius=False),
        "contains_zero": bool(x.contains(0)),
        "rel_accuracy_bits": int(x.rel_accuracy_bits()),
    }


def acb_record(z: acb) -> dict:
    return {"re": arb_record(z.real), "im": arb_record(z.imag)}


def centered_submatrix(M: arb_mat, max_k: int, k: int) -> arb_mat:
    lo = max_k - k
    hi = max_k + k
    idx = list(range(lo, hi + 1))
    return arb_mat([[M[i, j] for j in idx] for i in idx])


def to_acb_mat(M: arb_mat) -> acb_mat:
    return acb_mat([[acb(M[i, j]) for j in range(M.ncols())] for i in range(M.nrows())])


def shifted(M: acb_mat, z: acb) -> acb_mat:
    n = M.nrows()
    return acb_mat([
        [M[i, j] - z if i == j else M[i, j] for j in range(n)]
        for i in range(n)
    ])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    repo = Path(args.repo).resolve()
    r003 = repo / "research" / "RHRC" / "routes" / "R003_ccm_bridge"
    sys.path.insert(0, str(r003))
    from canonical_source_arb import canonical_source_matrix

    ctx.prec = PREC
    max_k = max(FROZEN_K)
    normalized: dict[tuple[int, int, int], acb] = {}
    rows = []
    normalizer_failures = []

    for L, Q in zip(FROZEN_L, FROZEN_Q):
        full_real = canonical_source_matrix(arb(L), max_k, Q)
        for K in FROZEN_K:
            M = to_acb_mat(centered_submatrix(full_real, max_k, K))
            normalizer = M.det()
            if acb_contains_zero(normalizer):
                normalizer_failures.append({
                    "L": L,
                    "Q": Q,
                    "K": K,
                    "normalizer": acb_record(normalizer),
                })
                continue

            values = []
            for z_index, spec in enumerate(FROZEN_Z):
                z = z_from_spec(spec)
                raw = shifted(M, z).det()
                norm = raw / normalizer
                normalized[(L, K, z_index)] = norm
                values.append({
                    "z_index": z_index,
                    "z": {"re": spec[0], "im": spec[1]},
                    "raw": acb_record(raw),
                    "normalized": acb_record(norm),
                })
            rows.append({
                "L": L,
                "Q": Q,
                "K": K,
                "normalizer": acb_record(normalizer),
                "normalizer_abs": arb_record(abs_ball(normalizer)),
                "values": values,
            })

    k_deltas = []
    for L in FROZEN_L:
        for ka, kb in zip(FROZEN_K, FROZEN_K[1:]):
            for z_index, spec in enumerate(FROZEN_Z):
                a = normalized.get((L, ka, z_index))
                b = normalized.get((L, kb, z_index))
                if a is None or b is None:
                    continue
                k_deltas.append({
                    "L": L,
                    "K_from": ka,
                    "K_to": kb,
                    "z_index": z_index,
                    "z": {"re": spec[0], "im": spec[1]},
                    "abs_delta": arb_record(abs_ball(b - a)),
                })

    l_deltas = []
    for la, lb in zip(FROZEN_L, FROZEN_L[1:]):
        for K in FROZEN_K:
            for z_index, spec in enumerate(FROZEN_Z):
                a = normalized.get((la, K, z_index))
                b = normalized.get((lb, K, z_index))
                if a is None or b is None:
                    continue
                l_deltas.append({
                    "L_from": la,
                    "L_to": lb,
                    "K": K,
                    "z_index": z_index,
                    "z": {"re": spec[0], "im": spec[1]},
                    "abs_delta": arb_record(abs_ball(b - a)),
                })

    out = {
        "schema_version": "RHRC-CLOSURE-CANONICAL-CHARACTERISTIC-SCOUT-2.0",
        "claim_cap": "RIGOROUS_BOUNDED_ACB_RESEARCH",
        "adaptive_search": False,
        "precision_bits": PREC,
        "scope": {
            "L": list(FROZEN_L),
            "physical_Q": list(FROZEN_Q),
            "K": list(FROZEN_K),
            "z": z_scope_records(),
        },
        "normalizer_failures": normalizer_failures,
        "rows": rows,
        "successive_K_deltas": k_deltas,
        "successive_L_deltas": l_deltas,
        "classification": (
            "NORMALIZER_ZERO_CONTAINMENT_ON_FROZEN_SCOPE"
            if normalizer_failures
            else "FINITE_COMPLEX_BALL_CHARACTERISTIC_SCOUT_NO_LIMIT_THEOREM"
        ),
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "Finite complex-ball enclosures are not local-uniform convergence.",
            "No limiting function is identified with Xi.",
            "No decrease of successive differences is promoted to an asymptotic or theorem.",
            "Bounded Acb research evidence is not Lean theorem authority.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
