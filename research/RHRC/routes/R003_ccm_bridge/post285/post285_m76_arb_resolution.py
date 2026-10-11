"""POST285 M76 Arb resolution: certified secular margins on the M76 grid (LEAD 3).

The float probe post285_m76_secular_margin.py (K = 2..5, L = 1/4, 1/2, ..., 6)
cannot read a sign at the 50 grid points where lambda_min is below 1e-10 of the
matrix scale.  This script recomputes all 96 grid points in Arb (python-flint,
256 bits):

  * S_L = canonical_source_arb.canonical_source_matrix at the exact rational
    aperture L = k/4, with the cutoff Q = floor(e^L) certified inside its cell;
  * A_L, B_L = the even and odd legal compressions on the exact integer
    boundary-flat carriers (boundary_flat_parity_basis), orthonormalized by the
    inverse Cholesky factor of their exact Gram matrices;
  * certified enclosures of lambda_min(A_L) and lambda_min(B_L) (Arb eig);
  * the secular margin 1 - T(L) = det A_L / det B_L (M74), and T(L) = H_L(x_L)
    with x_L = D^-1 B^-1 g and H_L read off from the rank-one relation
    B D - D A = g H, as a cross-check of the determinant ratio;
  * the channel split of T (pole, signed arch, signed prime, scalar shift; the
    signed_channel_matrices of canonical_source_arb); each channel satisfies the
    rank-one relation B_c D - D A_c = g H_c on its own (residual below 1e-68);
  * the float probe's values at the same point, with its resolved flag.  Where
    float64 resolves the point its margin agrees with Arb to 1.9e-3 relative (the
    error grows with the pole/T cancellation, 6.8e9 at the worst such point); at
    the unresolved points float64 even reports negative bottoms (9 even, 4 odd),
    all of which Arb certifies positive.

Result (CERTIFIED_DISCOVERY_REPLAY): A_L > 0, B_L > 0 and 1 - T(L) > 0 are
certified at all 96 points.  The margin falls to 2.2e-9 (K = 5, L = 6) and
lambda_min(A_L) to 9.7e-25; the pole channel of T cancels against the prime and
arch channels at up to 2e16 times T.  Along L, every grid minimum of
lambda_min(A_L) for K = 2 is the grid point nearest to some 2 pi k/gamma_1
(k = 4, 5, 8, 9, 10, 12, 13), and K = 3 and K = 4 have their deepest dip at
L = 4, where L gamma_1/(2 pi) = 8.998: the M51 near-contacts, seen on the grid.
At every point the even bottom is certified below the odd bottom (ratio 0.49
down to 1.1e-3), so on this grid the approach toward a contact is even-first.

Negative controls (each must FAIL as predicted), at the grid point of smallest
margin for each K:
  C1  every von Mangoldt weight times 1 + 1e-6: lambda_min(A_L) < 0 (certified);
  C2  every von Mangoldt weight times 1 - 1e-6: lambda_min(A_L) < 0 or
      lambda_min(B_L) < 0 (certified);
  so positivity at those points depends on the exact prime weights to one part
  in a million, in both directions;
  C3  canonicalArchScalarCorrection added twice (S_L + 2 c(L) I): both bottoms
      move up by exactly 2 c(L) (about 0.87 at these points), which would hide
      every near-contact.

Pointwise evidence at 96 rational apertures only: nothing between grid points,
nothing for K >= 6, no contact excluded, and not RH evidence.
M76_ARITHMETIC_COMPOSITION stays OPEN.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

from flint import arb, arb_mat, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

import canonical_source_arb as C  # noqa: E402
from canonical_source_numeric import canonical_source_matrix_L  # noqa: E402
from post247_remainder_budget_ratio_scout import (  # noqa: E402
    _eigs,
    _sym,
    boundary_flat_parity_basis,
    certified_cutoff,
    orthonormalizer,
)
from post285_m76_secular_margin import carriers, secular  # noqa: E402

PREC = 256
GAMMA_1 = 14.134725141734693790


def orthonormal_carrier(K: int, parity: str) -> arb_mat:
    V = boundary_flat_parity_basis(K, parity)
    return V * orthonormalizer(V).transpose()


def compress(M: arb_mat, W: arb_mat) -> arb_mat:
    return _sym(W.transpose() * M * W)


def max_abs_upper(M: arb_mat) -> float:
    return max(float(abs(M[i, j]).upper()) for i in range(M.nrows()) for j in range(M.ncols()))


def enclosure(x: arb) -> dict:
    return {"mid": float(x.mid()), "lower": float(x.lower()), "upper": float(x.upper()),
            "positive": bool(x > 0), "negative": bool(x < 0)}


class Grid:
    """Exact carriers, D and g for one K (orthonormal Arb bases)."""

    def __init__(self, K: int):
        self.K = K
        self.WE = orthonormal_carrier(K, "even")
        self.WO = orthonormal_carrier(K, "odd")
        dim = 2 * K + 1
        n = [arb(j) for j in range(-K, K + 1)]
        N = arb_mat([[n[i] if i == j else arb(0) for j in range(dim)] for i in range(dim)])
        self.D = self.WO.transpose() * N * self.WE
        self.g = self.WO.transpose() * arb_mat([[x ** 3] for x in n])
        self.gg = (self.g.transpose() * self.g)[0, 0]
        # N maps the even carrier into the odd one (moments 0, 1, 2 of n v vanish)
        self.D_leak = max_abs_upper(N * self.WE - self.WO * self.D)

    def functional(self, A: arb_mat, B: arb_mat) -> tuple[arb_mat, float]:
        R = B * self.D - self.D * A
        h = R.transpose() * self.g * (1 / self.gg)
        return h, max_abs_upper(R - self.g * h.transpose())


def arb_row(grid: Grid, k: int) -> dict:
    K = grid.K
    L = arb(fmpq(k, 4))
    Q = certified_cutoff(L)
    S = C.canonical_source_matrix(L, K, Q)
    channels = C.signed_channel_matrices(L, K, Q)
    A, B = compress(S, grid.WE), compress(S, grid.WO)
    lam_A, lam_B = _eigs(A)[0], _eigs(B)[0]
    margin = A.det() / B.det()
    h, rank_one = grid.functional(A, B)
    x = grid.D.solve(B.solve(grid.g))
    T = (h.transpose() * x)[0, 0]
    split, split_rank_one, total = {}, {}, arb(0)
    for name, M in channels.items():
        hc, rc = grid.functional(compress(M, grid.WE), compress(M, grid.WO))
        Tc = (hc.transpose() * x)[0, 0]
        split[name] = float(Tc.mid())
        split_rank_one[name] = rc
        total += Tc
    return {
        "K": K, "L": k / 4, "L_exact": f"{k}/4", "Q": Q,
        "L_gamma1_over_2pi": k / 4 * GAMMA_1 / (2 * math.pi),
        "matrix_scale": max_abs_upper(S),
        "lambda_min_A": enclosure(lam_A), "lambda_min_B": enclosure(lam_B),
        "margin": enclosure(margin),
        "margin_rel_radius": float(margin.rad() / abs(margin.mid())),
        "T": float(T.mid()),
        "T_vs_det_ratio": float(abs(1 - T - margin).upper()),
        "rank_one_residual": rank_one,
        "T_channels": split,
        "channel_rank_one_residual_max": max(split_rank_one.values()),
        "channel_sum_residual": float(abs(total - T).upper()),
        "pole_over_T": abs(split["pole"]) / abs(float(T.mid())),
        "_S": S, "_channels": channels, "_L": L, "_Q": Q,
    }


def float_compare(row: dict, fl: tuple) -> None:
    n, E, O = fl
    K, L = row["K"], row["L"]
    out = secular(K, L, canonical_source_matrix_L(L, K), n, E, O)
    row["float"] = {"resolved": out["float_resolved"],
                    "lambda_min_A": out["lambda_min_A"], "lambda_min_B": out["lambda_min_B"],
                    "margin": out.get("margin")}
    if out["float_resolved"] and out.get("margin") is not None:
        row["float"]["margin_rel_diff"] = abs(out["margin"] - row["margin"]["mid"]) / row["margin"]["mid"]


def controls(grid: Grid, row: dict) -> dict:
    S, ch = row["_S"], row["_channels"]
    eps = arb(fmpq(1, 10 ** 6))
    out = {"K": row["K"], "L": row["L"], "margin": row["margin"]["mid"]}
    for label, sign in (("C1_prime_weights_times_1_plus_1e-6", 1), ("C2_prime_weights_times_1_minus_1e-6", -1)):
        # prime_signed = -(prime part); heavier primes add eps * prime_signed
        Sp = S + ch["prime_signed"] * (sign * eps)
        A, B = compress(Sp, grid.WE), compress(Sp, grid.WO)
        lam_A, lam_B = _eigs(A)[0], _eigs(B)[0]
        out[label] = {"lambda_min_A": enclosure(lam_A), "lambda_min_B": enclosure(lam_B),
                      "positivity_lost": bool(lam_A < 0) or bool(lam_B < 0),
                      "even_bottom_negative": bool(lam_A < 0)}
    Sd = S + ch["scalar_shift"]
    A, B = compress(Sd, grid.WE), compress(Sd, grid.WO)
    shift = 2 * C.c_correction(row["_L"])
    lam_A, lam_B = _eigs(A)[0], _eigs(B)[0]
    lam_A0, lam_B0 = _eigs(compress(S, grid.WE))[0], _eigs(compress(S, grid.WO))[0]
    out["C3_scalar_correction_added_twice"] = {
        "two_c_L": float(shift.mid()),
        "lambda_min_A": float(lam_A.mid()), "lambda_min_B": float(lam_B.mid()),
        "shift_is_two_c": bool((lam_A - lam_A0 - shift).contains(0)) and bool((lam_B - lam_B0 - shift).contains(0)),
        "hides_near_contact": bool(lam_A > arb(fmpq(1, 2)) * shift),
    }
    return out


def grid_minima(rows: list[dict]) -> list[dict]:
    out = []
    for K in sorted({r["K"] for r in rows}):
        rs = [r for r in rows if r["K"] == K]
        for i in range(1, len(rs) - 1):
            a, b, c = (rs[j]["lambda_min_A"]["mid"] for j in (i - 1, i, i + 1))
            if b < a and b < c:
                out.append({"K": K, "L": rs[i]["L"], "lambda_min_A": b,
                            "L_gamma1_over_2pi": rs[i]["L_gamma1_over_2pi"]})
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=5)
    ap.add_argument("--kmax-quarter-steps", type=int, default=24, help="L = k/4 for k = 1..this")
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    C.set_precision(PREC)
    t0 = time.time()
    rows, grids = [], {}
    for K in range(2, args.kmax + 1):
        grid = grids[K] = Grid(K)
        fl = carriers(K)
        for k in range(1, args.kmax_quarter_steps + 1):
            row = arb_row(grid, k)
            float_compare(row, fl)
            rows.append(row)
    resolved = [r for r in rows if r["float"]["resolved"]]
    worst_by_K = {}
    for r in rows:
        if r["K"] not in worst_by_K or r["margin"]["mid"] < worst_by_K[r["K"]]["margin"]["mid"]:
            worst_by_K[r["K"]] = r
    ctrl = [controls(grids[K], r) for K, r in sorted(worst_by_K.items())]
    worst = min(rows, key=lambda r: r["margin"]["mid"])
    deepest = min(rows, key=lambda r: r["lambda_min_A"]["mid"])
    summary = {
        "grid_points": len(rows),
        "certified_A_positive": sum(r["lambda_min_A"]["positive"] for r in rows),
        "certified_B_positive": sum(r["lambda_min_B"]["positive"] for r in rows),
        "certified_margin_positive": sum(r["margin"]["positive"] for r in rows),
        "min_margin": {"K": worst["K"], "L": worst["L"], "value": worst["margin"]["mid"]},
        "min_lambda_min_A": {"K": deepest["K"], "L": deepest["L"], "value": deepest["lambda_min_A"]["mid"]},
        "certified_even_bottom_below_odd": sum(
            r["lambda_min_A"]["upper"] < r["lambda_min_B"]["lower"] for r in rows),
        "even_over_odd_bottom_range": [min(r["lambda_min_A"]["mid"] / r["lambda_min_B"]["mid"] for r in rows),
                                       max(r["lambda_min_A"]["mid"] / r["lambda_min_B"]["mid"] for r in rows)],
        "max_margin_rel_radius": max(r["margin_rel_radius"] for r in rows),
        "max_T_vs_det_ratio": max(r["T_vs_det_ratio"] for r in rows),
        "max_rank_one_residual": max(r["rank_one_residual"] for r in rows),
        "max_channel_rank_one_residual": max(r["channel_rank_one_residual_max"] for r in rows),
        "max_channel_sum_residual": max(r["channel_sum_residual"] for r in rows),
        "max_D_leak": max(g.D_leak for g in grids.values()),
        "pole_over_T_max": max(r["pole_over_T"] for r in rows),
        "float_resolved_points": len(resolved),
        "float_unresolved_points_now_certified": sum(
            1 for r in rows if not r["float"]["resolved"] and r["margin"]["positive"]
            and r["lambda_min_A"]["positive"] and r["lambda_min_B"]["positive"]),
        "float_max_margin_rel_diff_on_resolved": max(r["float"]["margin_rel_diff"] for r in resolved),
        "float_negative_even_bottom_at_unresolved": sum(
            1 for r in rows if not r["float"]["resolved"] and r["float"]["lambda_min_A"] <= 0),
        "float_negative_odd_bottom_at_unresolved": sum(
            1 for r in rows if not r["float"]["resolved"] and r["float"]["lambda_min_B"] <= 0),
        "grid_minima_of_lambda_min_A": grid_minima(rows),
        "seconds": round(time.time() - t0, 1),
    }
    all_certified = all(r["lambda_min_A"]["positive"] and r["lambda_min_B"]["positive"]
                        and r["margin"]["positive"] for r in rows)
    consistent = (summary["max_T_vs_det_ratio"] <= 1e-30 and summary["max_rank_one_residual"] <= 1e-40
                  and summary["max_channel_sum_residual"] <= 1e-20 and summary["max_D_leak"] <= 1e-40
                  and summary["float_max_margin_rel_diff_on_resolved"] <= 1e-2)
    controls_fail = all(c["C1_prime_weights_times_1_plus_1e-6"]["even_bottom_negative"]
                        and c["C2_prime_weights_times_1_minus_1e-6"]["positivity_lost"]
                        and c["C3_scalar_correction_added_twice"]["shift_is_two_c"]
                        and c["C3_scalar_correction_added_twice"]["hides_near_contact"] for c in ctrl)
    passed = all_certified and consistent and controls_fail
    for r in rows:
        for key in ("_S", "_channels", "_L", "_Q"):
            r.pop(key)
    report = {"terminal_claim": "RH_OPEN", "authority": "ARB_POINTWISE_RESEARCH_EVIDENCE",
              "package": "M76_ARB_RESOLUTION", "verdict": "PASS" if passed else "FAIL",
              "precision_bits": PREC,
              "statement": "A_L > 0, B_L > 0 and 1 - T(L) = det A_L / det B_L > 0 at each grid point "
                           "(K, L = k/4); pointwise, nothing between grid points",
              "summary": summary, "controls": ctrl, "rows": rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
