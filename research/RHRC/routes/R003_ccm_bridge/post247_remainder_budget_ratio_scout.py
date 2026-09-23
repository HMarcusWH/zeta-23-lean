#!/usr/bin/env python3
"""Post-#247 prime-remainder / prime-free-budget ratio scout (R003 discovery).

Research/falsification tooling only.  Claim cap: EXPERIMENTAL_SIGNAL_ONLY.

PR #246 proved, for every ``L > 0``, ``K`` and every Euclidean vector ``x``,

    canonicalSourceChannelEnergy L K x
        = -canonicalPrimeRemainderEnergy L K x - canonicalPrimeFreeBudget L K x

and that nonnegativity on every boundary-flat carrier at every ``(L, K)`` is
equivalent to Mathlib's ``RiemannHypothesis``.  Write

    A := -E_R      (minus the energy of R(x) = sum_{n<=x} Lambda(n)/sqrt(n) - 2 sqrt(x))
    B := B_free    (pole tail + reduced archimedean channels + scalar)
    E := A - B     (the canonical energy).

RH is equivalent to ``B(x) <= A(x)`` on every boundary-flat carrier.  This scout
measures that ratio, in Arb ball arithmetic, on

1. the real canonical data, and
2. a synthetic zero-side perturbation control: the real canonical prime data
   remain fixed while ``R(x)`` receives the local explicit-formula contribution
   ``-sum x^(rho-1/2)/(rho-1/2)`` of an extra zero quadruplet
   ``1/2 +- delta +- i*gamma``.  ``delta = 0`` plants an on-line double pair and
   must add a positive semidefinite form; ``delta > 0`` plants an off-line pair.

The planted object is not a globally self-consistent alternate zeta function:
no modified Euler product or von Mangoldt sequence is constructed to generate
the extra zeros.  It is a route-level falsifier for the local zero-side response.

Matrix conventions follow ``Zeta23/CCM/CanonicalPrimeRemainder.lean``:

    S(w)   : diag 2 w cos(2 pi n w), off (sin(2 pi n w) - sin(2 pi m w)) / (pi (n - m))
    E_R    = int_0^1 R(e^{L(1-w)}) S'(w) dw = P - G
    P      = sum_{2<=q<=e^L} Lambda(q)/sqrt(q) S(1 - log q / L)    (prime channel)
    G      = int_0^1 2 e^{L(1-w)/2} S'(w) dw                        (PNT main term)
    T      = int_0^1 2 e^{-L(1-w)/2} S'(w) dw                       (pole tail)
    B_free = T + canonical archimedean channel

The pole channel is checked independently: ``pole == G - T`` (closed form of
``pole_component`` against the exact integrals).

Every matrix entry is an Arb enclosure.  Eigenvalues are Arb enclosures from
``arb_mat.eig``; a sign is reported as certified only when the enclosure
excludes zero.  Nothing here is Lean theorem authority.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

from flint import acb, arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import canonical_source_arb as ca  # noqa: E402

I = acb(0, 1)
SCHEMA = "POST247_REMAINDER_BUDGET_RATIO_SCOUT_v1"
CLAIM_CAP = "EXPERIMENTAL_SIGNAL_ONLY"

# Apertures are exact rationals chosen strictly inside a prime-power cell.
REAL_GRID_L = (
    (1, 2), (3, 4), (1, 1), (3, 2), (2, 1), (5, 2), (3, 1), (4, 1), (5, 1), (6, 1),
    (7, 1), (8, 1),
)
REAL_GRID_K = (3, 4, 6, 8, 10, 12, 16, 20)

PLANT_GRID_L = ((2, 1), (3, 1), (4, 1))
PLANT_GRID_K = (6, 12)
PLANT_GAMMAS = ((5, 1), (10, 1), (20, 1))
PLANT_DELTAS = ((0, 1), (1, 1000), (1, 100), (1, 20), (1, 10), (1, 4))

PREC_START = 256
PREC_MAX = 4096


# ---------------------------------------------------------------------------
# small Arb helpers


def _q(num: int, den: int = 1) -> arb:
    return arb(fmpq(num, den))


def _as_float(x: arb) -> float:
    return float(x.mid())


def _rec(x: arb) -> dict:
    return {
        "mid": x.mid().str(20, radius=False),
        "rad": x.rad().str(3, radius=False),
        "certified_positive": bool(x > 0),
        "certified_negative": bool(x < 0),
    }


def _sym(M: arb_mat) -> arb_mat:
    return (M + M.transpose()) * _q(1, 2)


def _matmax(M: arb_mat) -> arb:
    best = arb(0)
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            v = abs(M[i, j])
            if v.mid() > best.mid():
                best = v
    return best


def _max_upper(M: arb_mat) -> float:
    """Largest certified upper bound of |M_ij| (float, for reporting)."""
    out = 0.0
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            out = max(out, float(abs(M[i, j]).upper()))
    return out


def _cholesky(M: arb_mat) -> arb_mat:
    """Arb Cholesky factor; raises if a pivot is not certified positive."""
    n = M.nrows()
    Lc = [[arb(0) for _ in range(n)] for _ in range(n)]
    for j in range(n):
        s = M[j, j]
        for k in range(j):
            s -= Lc[j][k] * Lc[j][k]
        if not s > 0:
            raise ArithmeticError("Cholesky pivot not certified positive")
        Lc[j][j] = s.sqrt()
        for i in range(j + 1, n):
            t = M[i, j]
            for k in range(j):
                t -= Lc[i][k] * Lc[j][k]
            Lc[i][j] = t / Lc[j][j]
    return arb_mat(Lc)


def _eigs(M: arb_mat) -> list[arb]:
    """Certified eigenvalue enclosures of a real symmetric Arb matrix.

    Simple isolation is tried first; low-rank increments have a multiple zero
    eigenvalue, for which Arb returns one shared enclosure per cluster.
    """
    try:
        vals = M.eig()
    except ValueError:
        vals = M.eig(multiple=True)
    out = []
    for v in vals:
        if not v.imag.contains(0):
            raise ArithmeticError("symmetric eigenvalue acquired a non-real enclosure")
        out.append(v.real)
    # Sort by exact ball midpoints: float keys collapse eigenvalues that
    # differ below double precision (e.g. ratios within 1e-18 of 1).
    out.sort(key=lambda a: a.mid())
    return out


def _congruence(M: arb_mat, Linv: arb_mat) -> arb_mat:
    return _sym(Linv * M * Linv.transpose())


# ---------------------------------------------------------------------------
# canonical channels at exact rational aperture


def certified_cutoff(L: arb) -> int:
    Q = int(math.floor(math.exp(float(L.mid()))))
    if Q >= 1 and not ca.fixed_cell_membership(Q, L)["certified"]:
        raise ValueError("aperture is not certified inside a prime-power cell")
    if Q < 1:
        raise ValueError("require L > 0")
    return Q


def centered(K: int) -> list[int]:
    return list(range(-K, K + 1))


def exp_weight_sprime(c: acb, w: acb, K: int) -> arb_mat:
    """Matrix of int_0^1 Re[w e^{c(1-omega)}] S'(omega) d omega, in closed form.

    With k = 2 pi n and s = i k - c:
        J0 = int_0^1 e^{c(1-w)} e^{ikw} dw = (1 - e^c)/s
        J1 = int_0^1 w e^{c(1-w)} e^{ikw} dw = ((s - 1) + e^c)/s^2
    """
    pi = arb.pi()
    ec = c.exp()
    a: dict[int, arb] = {}
    b: dict[int, arb] = {}
    for n in range(0, K + 1):
        k = 2 * pi * n

        def j0(kk: arb) -> acb:
            s = I * kk - c
            return (1 - ec) / s

        def j1(kk: arb) -> acb:
            s = I * kk - c
            return ((s - 1) + ec) / (s * s)

        an = (w * (j0(k) + j0(-k)) / 2).real
        bn = (w * (j1(k) - j1(-k)) / (2 * I)).real
        a[n], a[-n] = an, an
        b[n], b[-n] = bn, -bn
    idx = centered(K)
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for cc, m in enumerate(idx):
            if n == m:
                rows[r][cc] = 2 * a[n] - 4 * pi * n * b[n]
            else:
                rows[r][cc] = 2 * (n * a[n] - m * a[m]) / (n - m)
    return arb_mat(rows)


def prime_matrix(L: arb, K: int, Q: int) -> arb_mat:
    pi = arb.pi()
    s = {n: arb(0) for n in range(0, K + 1)}
    d = {n: arb(0) for n in range(0, K + 1)}
    for q in range(2, Q + 1):
        vm = ca.von_mangoldt(q)
        if vm.is_zero():
            continue
        wq = vm / arb(q).sqrt()
        y = arb(q).log()
        for n in range(0, K + 1):
            ph = 2 * pi * n * y / L
            s[n] += wq * ph.sin()
            d[n] += wq * 2 * (1 - y / L) * ph.cos()
    for n in range(1, K + 1):
        s[-n] = -s[n]
        d[-n] = d[n]
    idx = centered(K)
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c, m in enumerate(idx):
            rows[r][c] = d[n] if n == m else (s[n] - s[m]) / (pi * (m - n))
    return arb_mat(rows)


def arch_matrix(L: arb, K: int) -> arb_mat:
    alpha, beta, gamma = {}, {}, {}
    for n in range(0, K + 1):
        alpha[n] = ca.alpha_L(n, L)
        beta[n] = ca.beta_L(n, L)
        gamma[n] = ca.source_eq44_gamma_L(n, L)
        alpha[-n], beta[-n], gamma[-n] = -alpha[n], beta[n], gamma[n]
    idx = centered(K)
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c, m in enumerate(idx):
            rows[r][c] = (
                2 * gamma[n] - 2 * beta[n]
                if n == m
                else (alpha[m] - alpha[n]) / (n - m)
            )
    return arb_mat(rows)


def pole_matrix(L: arb, K: int) -> arb_mat:
    idx = centered(K)
    return arb_mat([[ca.pole_component(n, m, L) for m in idx] for n in idx])


def channels(L: arb, K: int) -> dict[str, arb_mat]:
    Q = certified_cutoff(L)
    P = prime_matrix(L, K, Q) if Q >= 2 else arb_mat(2 * K + 1, 2 * K + 1)
    G = exp_weight_sprime(acb(L / 2), acb(2), K)
    T = exp_weight_sprime(acb(-L / 2), acb(2), K)
    Arch = arch_matrix(L, K)
    Pole = pole_matrix(L, K)
    A = G - P  # = -E_R
    B = T + Arch  # = B_free
    return {"Q": Q, "P": P, "G": G, "T": T, "Arch": Arch, "Pole": Pole, "A": A, "B": B}


def planted_increment(L: arb, K: int, gamma: arb, delta: arb) -> arb_mat:
    """Energy of the planted quadruplet's contribution to R (i.e. E_Delta).

    Delta(e^t) = sum_{s in {delta+i gamma, -delta+i gamma}} Re[(-2/s) e^{s t}],
    E_R(planted) = E_R + E_Delta, so A(planted) = A - E_Delta.
    """
    out = arb_mat(2 * K + 1, 2 * K + 1)
    for sgn in (1, -1):
        s = acb(sgn * delta, gamma)
        out += exp_weight_sprime(s * L, -2 / s, K)
    return out


# ---------------------------------------------------------------------------
# boundary-flat parity carriers (exact integer bases)


def boundary_flat_parity_basis(K: int, parity: str) -> arb_mat:
    """Columns span the even/odd boundary-flat carrier (moments 0,1,2 vanish).

    v_j = e_j - l_{-1}(j) e_{-1} - l_0(j) e_0 - l_1(j) e_1 with the Lagrange
    weights of the nodes -1, 0, 1; even/odd columns are v_j +- v_{-j}, j >= 2.
    """
    if K < 2:
        raise ValueError("boundary-flat parity carriers need K >= 2")
    dim = 2 * K + 1
    pos = {n: n + K for n in centered(K)}

    def v(j: int) -> list[int]:
        col = [0] * dim
        col[pos[j]] += 1
        col[pos[-1]] -= j * (j - 1) // 2
        col[pos[0]] -= 1 - j * j
        col[pos[1]] -= j * (j + 1) // 2
        return col

    cols = []
    for j in range(2, K + 1):
        vp, vm = v(j), v(-j)
        cols.append([x + y for x, y in zip(vp, vm)] if parity == "even" else [x - y for x, y in zip(vp, vm)])
    for col in cols:
        for p in range(3):
            if sum(c * (n ** p) for c, n in zip(col, centered(K))) != 0:
                raise AssertionError("basis vector is not boundary-flat")
    return arb_mat([[arb(cols[c][r]) for c in range(len(cols))] for r in range(dim)])


def orthonormalizer(V: arb_mat) -> arb_mat:
    """Inverse Cholesky factor of the exact Gram matrix V^T V."""
    return _cholesky(V.transpose() * V).inv()


def restrict(M: arb_mat, V: arb_mat, Linv: arb_mat) -> arb_mat:
    return _congruence(V.transpose() * M * V, Linv)


# ---------------------------------------------------------------------------
# block analysis


def ratio_block(A: arb_mat, B: arb_mat) -> dict:
    """Inertia of A, B, eigenvalues of E = A - B and the B/A ratio."""
    E = _sym(A - B)
    eE, eA, eB = _eigs(E), _eigs(A), _eigs(B)
    out: dict = {
        "dim": E.nrows(),
        "lambda_min": _rec(eE[0]),
        "lambda_2": _rec(eE[1]) if len(eE) > 1 else None,
        "lambda_max": _rec(eE[-1]),
        "A_eig_min": _rec(eA[0]),
        "A_eig_max": _rec(eA[-1]),
        "B_eig_min": _rec(eB[0]),
        "B_eig_max": _rec(eB[-1]),
        "A_inertia": _inertia(eA),
        "B_inertia": _inertia(eB),
        "E_inertia": _inertia(eE),
    }
    # Slack is computed directly as the bottom of E in the A- (or B-) metric,
    # min_x E(x)/A(x) = 1 - max_x B(x)/A(x), which avoids cancellation near 1.
    if all(x > 0 for x in eA):
        La_inv = _cholesky(A).inv()
        sA = _eigs(_congruence(E, La_inv))[0]
        out["slack_1_minus_ratio"] = _rec(sA)
        out["ratio_B_over_A_max"] = _rec(1 - sA)
    if all(x > 0 for x in eB):
        Lb_inv = _cholesky(B).inv()
        sB = _eigs(_congruence(E, Lb_inv))[0]
        out["slack_ratio_minus_1"] = _rec(sB)
        out["ratio_A_over_B_min"] = _rec(1 + sB)
    return out


def _inertia(eigs: list[arb]) -> dict:
    return {
        "positive": sum(1 for x in eigs if x > 0),
        "negative": sum(1 for x in eigs if x < 0),
        "uncertified": sum(1 for x in eigs if x.contains(0)),
    }


def _all_certified(block: dict) -> bool:
    lam = block["lambda_min"]
    return lam["certified_positive"] or lam["certified_negative"]


# ---------------------------------------------------------------------------
# scout runs


def real_point(Lnum: int, Lden: int, K: int) -> dict:
    prec = PREC_START
    while True:
        ctx.prec = prec
        t0 = time.time()
        L = _q(Lnum, Lden)
        ch = channels(L, K)
        pole_check = _matmax(ch["Pole"] - (ch["G"] - ch["T"]))
        rev = {}
        blocks = {}
        ok = True
        try:
            for parity in ("even", "odd"):
                V = boundary_flat_parity_basis(K, parity)
                Linv = orthonormalizer(V)
                A = restrict(ch["A"], V, Linv)
                B = restrict(ch["B"], V, Linv)
                blocks[parity] = ratio_block(A, B)
                ok = ok and _all_certified(blocks[parity])
            Ve = boundary_flat_parity_basis(K, "even")
            Vo = boundary_flat_parity_basis(K, "odd")
            rev["cross_parity_block_max_upper"] = _max_upper(Ve.transpose() * (ch["A"] - ch["B"]) * Vo)
        except (ArithmeticError, ValueError) as exc:
            ok = False
            blocks["error"] = str(exc)
        if ok or prec >= PREC_MAX:
            break
        prec *= 2
    lam_e = blocks.get("even", {}).get("lambda_min")
    lam_o = blocks.get("odd", {}).get("lambda_min")
    return {
        "L": f"{Lnum}/{Lden}",
        "L_float": Lnum / Lden,
        "K": K,
        "prime_cutoff_Q": ch["Q"],
        "prec_bits": prec,
        "seconds": round(time.time() - t0, 2),
        "pole_equals_G_minus_T_max_abs_upper": float(pole_check.upper()),
        **rev,
        "even": blocks.get("even"),
        "odd": blocks.get("odd"),
        "error": blocks.get("error"),
        "global_lambda_min_float": min(
            float(x["mid"]) for x in (lam_e, lam_o) if x is not None
        ) if (lam_e or lam_o) else None,
        "all_signs_certified": ok,
    }


def planted_point(Lnum: int, Lden: int, K: int, gam: tuple[int, int], dlt: tuple[int, int]) -> dict:
    prec = PREC_START
    while True:
        ctx.prec = prec
        L = _q(Lnum, Lden)
        gamma, delta = _q(*gam), _q(*dlt)
        ch = channels(L, K)
        D = planted_increment(L, K, gamma, delta)
        blocks, ok = {}, True
        try:
            for parity in ("even", "odd"):
                V = boundary_flat_parity_basis(K, parity)
                Linv = orthonormalizer(V)
                A = restrict(ch["A"], V, Linv)
                B = restrict(ch["B"], V, Linv)
                Dv = restrict(D, V, Linv)
                eInc = _eigs(_sym(-Dv))  # increment of E is -E_Delta
                block = ratio_block(_sym(A - Dv), B)
                block["increment_inertia"] = _inertia(eInc)
                block["increment_eig_min"] = _rec(eInc[0])
                block["increment_eig_max"] = _rec(eInc[-1])
                blocks[parity] = block
                ok = ok and _all_certified(block)
        except (ArithmeticError, ValueError) as exc:
            ok = False
            blocks["error"] = str(exc)
        if ok or prec >= PREC_MAX:
            break
        prec *= 2
    bad = any(
        blocks.get(p, {}).get("lambda_min", {}).get("certified_negative", False)
        for p in ("even", "odd")
    )
    return {
        "L": f"{Lnum}/{Lden}",
        "K": K,
        "gamma": f"{gam[0]}/{gam[1]}",
        "delta": f"{dlt[0]}/{dlt[1]}",
        "prec_bits": prec,
        "even": blocks.get("even"),
        "odd": blocks.get("odd"),
        "error": blocks.get("error"),
        "planted_state_certified_bad": bad,
        "all_signs_certified": ok,
    }


def _planted_min_lambda(ch: dict, L: arb, K: int, gamma: arb, delta: arb) -> arb:
    D = planted_increment(L, K, gamma, delta)
    best = None
    for parity in ("even", "odd"):
        V = boundary_flat_parity_basis(K, parity)
        Linv = orthonormalizer(V)
        E = restrict(ch["A"] - D - ch["B"], V, Linv)
        lam = _eigs(E)[0]
        if best is None or lam.mid() < best.mid():
            best = lam
    return best


def detection_threshold(Lnum: int, Lden: int, K: int, gam: tuple[int, int], steps: int = 48) -> dict:
    """Narrow certified sign-change bracket found by geometric search.

    Every bracket endpoint is an exact rational delta; ``hi`` is certified bad
    and ``lo`` is certified not bad at the recorded precision.  This search is
    not a global minimum certificate: monotonicity of the lowest eigenvalue in
    delta is not proved by this scout.
    """
    ctx.prec = 512
    L = _q(Lnum, Lden)
    gamma = _q(*gam)
    ch = channels(L, K)

    def bad(d: fmpq) -> bool | None:
        lam = _planted_min_lambda(ch, L, K, gamma, arb(d))
        if lam < 0:
            return True
        if lam > 0:
            return False
        return None

    lo, hi = fmpq(1, 10 ** 40), fmpq(1, 4)
    if bad(hi) is not True:
        return {"L": f"{Lnum}/{Lden}", "K": K, "gamma": f"{gam[0]}/{gam[1]}",
                "certified_bad_at_delta_1_4": False}
    if bad(lo) is not False:
        return {"L": f"{Lnum}/{Lden}", "K": K, "gamma": f"{gam[0]}/{gam[1]}",
                "lower_bracket_not_certified": True}
    for _ in range(steps):
        mid_f = math.sqrt(float(lo) * float(hi))
        mid = fmpq(int(round(mid_f * 10 ** 45)), 10 ** 45)
        verdict = bad(mid)
        if verdict is None:
            break
        if verdict:
            hi = mid
        else:
            lo = mid
    real_lam = _planted_min_lambda(ch, L, K, gamma, arb(0))
    return {
        "L": f"{Lnum}/{Lden}",
        "K": K,
        "gamma": f"{gam[0]}/{gam[1]}",
        "delta_certified_not_bad": float(lo),
        "delta_certified_bad": float(hi),
        "on_line_double_pair_lambda_min": _rec(real_lam),
    }


def explicit_formula_check(nzeros: int = 300) -> dict:
    """Sign-convention check of the planted term against the real zeros.

    R(x) = -zeta'/zeta(1/2) - sum_rho x^(rho-1/2)/(rho-1/2) + (trivial zeros),
    so the zero sum with the *same* sign as the planted term must track R.
    """
    import mpmath as mp

    mp.mp.dps = 30
    gammas = [mp.im(mp.zetazero(j)) for j in range(1, nzeros + 1)]
    const = -mp.zeta(mp.mpf(1) / 2, derivative=1) / mp.zeta(mp.mpf(1) / 2)
    import sympy as sp

    def R_exact(x: float) -> mp.mpf:
        tot = mp.mpf(0)
        for n in range(2, int(math.floor(x)) + 1):
            fac = sp.factorint(n)
            if len(fac) == 1:
                tot += mp.log(next(iter(fac))) / mp.sqrt(n)
        return tot - 2 * mp.sqrt(x)

    def zero_sum(x: float, sign: int) -> mp.mpf:
        tot = mp.mpf(0)
        lx = mp.log(x)
        for g in gammas:
            tot += 2 * mp.sin(g * lx) / g  # 2 Re[x^{i g}/(i g)]
        trivial = sum(mp.power(x, -2 * k - mp.mpf(1) / 2) / (2 * k + mp.mpf(1) / 2) for k in range(1, 40))
        return const - sign * tot + trivial

    xs = [n + 0.5 for n in range(20, 400, 7)]
    err_plus, err_minus = [], []
    for x in xs:
        r = R_exact(x)
        err_plus.append(abs(float(r - zero_sum(x, +1))))
        err_minus.append(abs(float(r - zero_sum(x, -1))))
    return {
        "nzeros": nzeros,
        "x_points": len(xs),
        "neg_zeta_log_derivative_at_half": float(const),
        "max_abs_error_planted_sign_convention": max(err_plus),
        "mean_abs_error_planted_sign_convention": sum(err_plus) / len(err_plus),
        "max_abs_error_flipped_sign": max(err_minus),
        "mean_abs_error_flipped_sign": sum(err_minus) / len(err_minus),
    }


def float_crosscheck() -> dict:
    """Arb canonical energy against the repository float builder."""
    import numpy as np
    from canonical_source_numeric import canonical_source_matrix_L

    ctx.prec = 256
    worst = 0.0
    for (Lnum, Lden) in ((1, 1), (3, 1), (5, 1)):
        for K in (4, 8):
            ch = channels(_q(Lnum, Lden), K)
            E = ch["A"] - ch["B"]
            M = canonical_source_matrix_L(Lnum / Lden, K)
            diff = max(
                abs(float(E[i, j].mid()) - M[i, j])
                for i in range(2 * K + 1)
                for j in range(2 * K + 1)
            )
            worst = max(worst, diff / max(1.0, float(np.abs(M).max())))
    return {"max_relative_entry_difference": worst}


FIRST_ZETA_ORDINATE = 14.134725141734693


def summarize(real: list[dict], planted: list[dict]) -> dict:
    """Aggregate certified facts; every field is recomputable from the rows."""
    ok = [r for r in real if r["even"] and r["odd"]]

    def both(r: dict, key: str, flag: str) -> bool:
        return r["even"][key][flag] and r["odd"][key][flag]

    slack = {}
    for r in ok:
        s = min(float(r[p]["slack_1_minus_ratio"]["mid"]) for p in ("even", "odd"))
        slack.setdefault(r["L"], {})[str(r["K"])] = s
    below, above = [], []
    for r in ok:
        bw = 2 * math.pi * r["K"] / r["L_float"]
        lam_max = max(float(r[p]["lambda_max"]["mid"]) for p in ("even", "odd"))
        (below if bw < FIRST_ZETA_ORDINATE else above).append(lam_max)
    on_line = [r for r in planted if r["delta"] == "0/1"]
    off_line = [r for r in planted if r["delta"] != "0/1"]
    return {
        "real_points": len(real),
        "real_all_signs_certified": sum(1 for r in real if r["all_signs_certified"]),
        "real_energy_certified_positive": sum(1 for r in ok if both(r, "lambda_min", "certified_positive")),
        "A_positive_definite_everywhere": all(
            r[p]["A_inertia"]["negative"] == 0 and r[p]["A_inertia"]["uncertified"] == 0
            for r in ok for p in ("even", "odd")
        ),
        "B_positive_definite_everywhere": all(
            r[p]["B_inertia"]["negative"] == 0 and r[p]["B_inertia"]["uncertified"] == 0
            for r in ok for p in ("even", "odd")
        ),
        "min_slack_by_L_then_K": slack,
        "bandwidth_split_at_first_zeta_ordinate": {
            "gamma_1": FIRST_ZETA_ORDINATE,
            "points_below": len(below),
            "max_lambda_max_E_below": max(below) if below else None,
            "points_above": len(above),
            "min_lambda_max_E_above": min(above) if above else None,
        },
        "planted_on_line_cases": len(on_line),
        "planted_on_line_certified_bad": sum(1 for r in on_line if r["planted_state_certified_bad"]),
        "planted_on_line_increment_rank_one_psd_per_parity": all(
            r[p]["increment_inertia"] == {"positive": 1, "negative": 0, "uncertified": r[p]["dim"] - 1}
            for r in on_line for p in ("even", "odd")
        ),
        "planted_off_line_cases": len(off_line),
        "planted_off_line_certified_bad": sum(1 for r in off_line if r["planted_state_certified_bad"]),
        "planted_off_line_increment_signature_1_1_per_parity": all(
            r[p]["increment_inertia"]["positive"] == 1 and r[p]["increment_inertia"]["negative"] == 1
            for r in off_line for p in ("even", "odd")
        ),
    }


def run(quick: bool = False) -> dict:
    real_L = REAL_GRID_L[:4] if quick else REAL_GRID_L
    real_K = REAL_GRID_K[:2] if quick else REAL_GRID_K
    real = [real_point(a, b, K) for (a, b) in real_L for K in real_K]
    planted = [
        planted_point(a, b, K, g, d)
        for (a, b) in (PLANT_GRID_L[:1] if quick else PLANT_GRID_L)
        for K in (PLANT_GRID_K[:1] if quick else PLANT_GRID_K)
        for g in PLANT_GAMMAS
        for d in PLANT_DELTAS
    ]
    thresholds = [
        detection_threshold(a, b, K, g)
        for (a, b) in (PLANT_GRID_L[:1] if quick else PLANT_GRID_L)
        for K in (PLANT_GRID_K[:1] if quick else PLANT_GRID_K)
        for g in PLANT_GAMMAS
    ]
    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "validation": {
            "float_crosscheck": float_crosscheck(),
            "explicit_formula_sign_check": explicit_formula_check(60 if quick else 300),
        },
        "summary": summarize(real, planted),
        "real": real,
        "planted": planted,
        "detection_thresholds": thresholds,
        "nonclaims": [
            "Arb enclosures on a finite (L, K) grid are not Lean theorem authority.",
            "Positivity on real data at finitely many (L, K) is not RH.",
            "The planted model is a synthetic control, not a statement about zeta.",
            "No ratio, slack or threshold here is a theorem about all (L, K).",
            "RH remains OPEN.",
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    result = run(quick=args.quick)
    text = json.dumps(result, indent=1, sort_keys=True)
    if args.out:
        args.out.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
