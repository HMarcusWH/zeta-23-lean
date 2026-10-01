from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def add(*ps):
    out = {}
    for p in ps:
        for k, v in p.items():
            out[k] = out.get(k, F(0)) + v
    return {k: v for k, v in out.items() if v}


def scale(c, p):
    return {k: c * v for k, v in p.items() if c * v}


def mul(p, q):
    out = {}
    for (i, j), v in p.items():
        for (k, l), w in q.items():
            key = (i + k, j + l)
            out[key] = out.get(key, F(0)) + v * w
    return {k: v for k, v in out.items() if v}


def diff(p):
    return {(i - 1, j): i * v for (i, j), v in p.items() if i}


def cut(p, n):
    return {k: v for k, v in p.items() if k[0] <= n}


def coeff(p, i, j):
    return p.get((i, j), F(0))


def run_checks() -> dict:
    K = 3
    ns = list(range(-K, K + 1))
    z = list(map(F, [0, 1, -4, 6, -4, 1, 0]))
    u = list(map(F, [1, 0, -9, 16, -9, 0, 1]))
    dot = lambda x, y: sum(a * b for a, b in zip(x, y))
    w = [a - F(12, 5) * b for a, b in zip(u, z)]
    mean = F(sum(n * n for n in ns), len(ns))
    N = [F(n * n) - mean for n in ns]
    nu = dot(N, N)
    m = sum(n**4 * v for n, v in zip(ns, z))
    mw = sum(n**4 * v for n, v in zip(ns, w))
    y = [n * v for n, v in zip(ns, z)]
    h = [n * n * v - m * nn / nu for n, v, nn in zip(ns, z, N)]

    A = [[{
        (2 * j + 1, 2 * j):
            F(2 * (-1) ** j, factorial(2 * j + 1)) *
            sum(n ** (2 * j - r) * p ** r for r in range(2 * j + 1))
        for j in range(8)
    } for p in ns] for n in ns]

    def energy(x, v):
        return add(*(
            scale(x[i] * v[j], A[i][j])
            for i in range(len(ns))
            for j in range(len(ns))
        ))

    ez, ey, ehz, ezw = energy(z, z), energy(y, y), energy(h, z), energy(z, w)
    H = scale(1 / nu, energy(N, z))
    a2 = {(0, 2): F(1)}
    one = {(0, 0): F(1)}
    one_sub = {(0, 0): F(1), (1, 0): F(-1)}
    one_sub_sq = mul(one_sub, one_sub)

    checks = {
        "z_legal": sum(z) == 0 and sum(n * n * v for n, v in zip(ns, z)) == 0,
        "w_legal": sum(w) == 0 and sum(n * n * v for n, v in zip(ns, w)) == 0,
        "w_perpendicular": dot(z, w) == 0,
        "h_legal": sum(h) == 0 and sum(n * n * v for n, v in zip(ns, h)) == 0,
        "normal_norm_squared": nu == 84,
        "moment_nonzero": m == 24,
        "source_decomposition_all_retained_coefficients":
            ey == add(ehz, scale(m, H)),
        "derivative_transport_through_order_13":
            cut(diff(diff(ez)), 13) == cut(scale(-1, mul(a2, ey)), 13),
        "even_source_flat_through_8": not cut(ez, 8),
        "even_source_ninth_coefficient":
            coeff(ez, 9, 8) == F(2, factorial(9)) * m * m,
        "odd_source_flat_through_6": not cut(ey, 6),
        "odd_source_seventh_coefficient":
            coeff(ey, 7, 6) == -F(2, factorial(7)) * m * m,
        "normal_source_seventh_coefficient":
            coeff(H, 7, 6) == -F(2, factorial(7)) * m,
    }

    for L in (F(3, 2), F(5)):
        phi = add(
            scale(1 / L**2, mul(one_sub_sq, diff(diff(ez)))),
            scale(2 / L, mul(one_sub, diff(ezw))),
        )
        remainder = add(
            scale(
                m / L**2,
                mul(mul(a2, add(one, scale(-1, one_sub_sq))), H),
            ),
            scale(-1 / L**2, mul(mul(a2, one_sub_sq), ehz)),
            scale(2 / L, mul(one_sub, diff(ezw))),
        )
        checks[f"L={L}:exact_remainder_identity_through_order_13"] = (
            cut(remainder, 13) ==
            cut(add(phi, scale(m / L**2, mul(a2, H))), 13)
        )
        checks[f"L={L}:phi_flat_through_6"] = not cut(phi, 6)
        checks[f"L={L}:phi_seventh_coefficient"] = (
            coeff(phi, 7, 8) == F(2, factorial(7)) * m * m / L**2
        )
        checks[f"L={L}:remainder_flat_through_7"] = not cut(remainder, 7)
        checks[f"L={L}:remainder_eighth_coefficient"] = (
            coeff(remainder, 8, 8) ==
            F(4, factorial(8)) * (L * m * mw - 8 * m * m) / L**2
        )
        c = 8 / L - mw / m
        wg = [a + c * b for a, b in zip(w, z)]
        phig = add(
            scale(1 / L**2, mul(one_sub_sq, diff(diff(ez)))),
            scale(2 / L, mul(one_sub, diff(energy(z, wg)))),
        )
        rg = add(phig, scale(m / L**2, mul(a2, H)))
        checks[f"L={L}:gauge_remainder_flat_through_8"] = not cut(rg, 8)
        checks[f"L={L}:gauge_preserves_phi_seventh_coefficient"] = (
            coeff(phig, 7, 8) == coeff(phi, 7, 8)
        )

    failed = {k: v for k, v in checks.items() if not v}
    if failed:
        raise AssertionError(failed)

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-SOURCE-REMAINDER-1.0",
        "status": "PASS",
        "passed": sum(checks.values()),
        "total": len(checks),
        "method": "Exact rational coefficients with formal independent omega and a=2*pi",
        "scope": (
            "Pointwise source identities and endpoint jets in the actual K=3 "
            "source geometry; no canonical contact is asserted"
        ),
        "source_series_max_order": 15,
        "identities_checked_through_order": 13,
        "M4_z": str(m),
        "M4_w": str(mw),
        "checks": checks,
        "equality_rigidity_proved": False,
        "unconditional_RH_proved": False,
        "terminal_claim": "RH_OPEN",
        "limitations": [
            "Finite exact coefficient checks corroborate the general algebraic derivation.",
            "No arithmetic-functional sign or universal contact-exclusion theorem is supplied.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    receipt = run_checks()
    payload = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
