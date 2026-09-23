#!/usr/bin/env python3
"""Runtime QA for the post-#247 remainder/budget ratio scout.

Implementation checks only.  Synthetic Arb matrices exercise the ratio and
ordering logic; real canonical checks verify channel identities against the
independent Arb and float builders; planted controls verify the predicted
structure; and a few frozen fixture points are recomputed and compared.
Nothing here is theorem authority.
"""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpq

import canonical_source_arb as ca
import post247_remainder_budget_ratio_scout as scout

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post247_remainder_budget_ratio_v1.json"


def _diag(vals: list) -> arb_mat:
    n = len(vals)
    return arb_mat([[vals[i] if i == j else arb(0) for j in range(n)] for i in range(n)])


def _close(a: float, b: float, rel: float = 1e-12) -> bool:
    return abs(a - b) <= rel * max(abs(a), abs(b))


def check_synthetic_ratio_controls() -> None:
    ctx.prec = 256
    good = scout.ratio_block(_diag([arb(2), arb(4)]), _diag([arb(1), arb(3)]))
    assert good["lambda_min"]["certified_positive"]
    assert _close(float(good["slack_1_minus_ratio"]["mid"]), 0.25)
    assert _close(float(good["ratio_B_over_A_max"]["mid"]), 0.75)
    assert _close(float(good["slack_ratio_minus_1"]["mid"]), 1 / 3)
    bad = scout.ratio_block(_diag([arb(2), arb(4)]), _diag([arb(3), arb(1)]))
    assert bad["lambda_min"]["certified_negative"]
    assert bad["E_inertia"] == {"positive": 1, "negative": 1, "uncertified": 0}
    assert _close(float(bad["slack_1_minus_ratio"]["mid"]), -0.5)


def check_exact_eigen_ordering() -> None:
    """Regression: float sort keys once collapsed eigenvalues within 1e-16 of 1."""
    ctx.prec = 512
    tiny30 = arb(fmpq(1, 10 ** 30))
    tiny20 = arb(fmpq(1, 10 ** 20))
    vals = scout._eigs(_diag([1 - tiny30, arb(1), 1 - tiny20]))
    assert vals[0].overlaps(1 - tiny20)
    assert vals[1].overlaps(1 - tiny30)
    assert vals[2].overlaps(arb(1))


def check_boundary_flat_carriers() -> None:
    ctx.prec = 256
    for K in (2, 5, 9):
        for parity, sign in (("even", 1), ("odd", -1)):
            V = scout.boundary_flat_parity_basis(K, parity)
            assert V.nrows() == 2 * K + 1 and V.ncols() == K - 1
            for c in range(V.ncols()):
                col = [int(round(float(V[r, c].mid()))) for r in range(V.nrows())]
                assert col == [sign * x for x in reversed(col)]


def check_channel_identities() -> None:
    ctx.prec = 256
    for (num, den) in ((1, 2), (2, 1), (5, 1)):
        L = arb(fmpq(num, den))
        K = 6
        ch = scout.channels(L, K)
        assert float(scout._matmax(ch["Pole"] - (ch["G"] - ch["T"])).upper()) < 1e-60
        direct = ca.canonical_source_matrix(L, K, ch["Q"])
        diff = (ch["A"] - ch["B"]) - direct
        for i in range(2 * K + 1):
            for j in range(2 * K + 1):
                assert diff[i, j].contains(0), (num, den, i, j)
    assert scout.float_crosscheck()["max_relative_entry_difference"] < 1e-12


def check_planted_structure() -> None:
    row0 = scout.planted_point(2, 1, 6, (5, 1), (0, 1))
    assert not row0["planted_state_certified_bad"]
    for p in ("even", "odd"):
        inc = row0[p]["increment_inertia"]
        assert inc == {"positive": 1, "negative": 0, "uncertified": row0[p]["dim"] - 1}
    row1 = scout.planted_point(2, 1, 6, (5, 1), (1, 100))
    row2 = scout.planted_point(2, 1, 6, (5, 1), (1, 1000))
    assert row1["planted_state_certified_bad"] and row2["planted_state_certified_bad"]
    for p in ("even", "odd"):
        assert row1[p]["increment_inertia"]["positive"] == 1
        assert row1[p]["increment_inertia"]["negative"] == 1
        ratio = float(row2[p]["increment_eig_min"]["mid"]) / float(row1[p]["increment_eig_min"]["mid"])
        # Near-zero leading-order quadratic response only:
        # delta shrinks by 10, so a delta^2 term shrinks by about 100.
        # This is not an exact global scaling law in delta.
        assert 0.0099 < ratio < 0.0101, ratio


def check_explicit_formula_sign() -> None:
    ef = scout.explicit_formula_check(40)
    assert ef["mean_abs_error_planted_sign_convention"] * 3 < ef["mean_abs_error_flipped_sign"], ef


def check_fixture_replay() -> None:
    d = json.loads(FIXTURE.read_text(encoding="utf-8"))
    real = {(r["L"], r["K"]): r for r in d["real"]}
    for (num, den, K) in ((1, 2, 4), (2, 1, 6), (8, 1, 3)):
        got = scout.real_point(num, den, K)
        want = real[(f"{num}/{den}", K)]
        assert got["prec_bits"] == want["prec_bits"]
        for p in ("even", "odd"):
            for key in ("lambda_min", "slack_1_minus_ratio", "A_eig_min", "B_eig_min"):
                assert _close(float(got[p][key]["mid"]), float(want[p][key]["mid"])), (num, den, K, p, key)
    planted = {(r["L"], r["K"], r["gamma"], r["delta"]): r for r in d["planted"]}
    got = scout.planted_point(2, 1, 6, (5, 1), (1, 1000))
    want = planted[("2/1", 6, "5/1", "1/1000")]
    for p in ("even", "odd"):
        assert _close(float(got[p]["lambda_min"]["mid"]), float(want[p]["lambda_min"]["mid"]))
    thr = {(t["L"], t["K"], t["gamma"]): t for t in d["detection_thresholds"]}
    got_t = scout.detection_threshold(2, 1, 6, (5, 1))
    want_t = thr[("2/1", 6, "5/1")]
    assert _close(got_t["delta_certified_bad"], want_t["delta_certified_bad"], 1e-9)


def main() -> int:
    check_synthetic_ratio_controls()
    check_exact_eigen_ordering()
    check_boundary_flat_carriers()
    check_channel_identities()
    check_planted_structure()
    check_explicit_formula_sign()
    check_fixture_replay()
    print("POST247 REMAINDER/BUDGET RATIO SCOUT RESULTS: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
