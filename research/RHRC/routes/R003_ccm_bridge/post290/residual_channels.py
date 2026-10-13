"""Native finite probe construction and signed residual arithmetic.

The source matrices come from the unchanged canonical_source_arb backend.
All vectors here are explicit finite probes, never zero-generated detectors.
"""
from __future__ import annotations

from fractions import Fraction


def exact_ball(value):
    if not value.is_finite():
        raise ArithmeticError("nonfinite enclosure")
    def endpoint(bound):
        m, e = bound.man_exp()
        q = Fraction(int(m)) * Fraction(2)**int(e)
        return [q.numerator, q.denominator]
    return {"lower": endpoint(value.lower()), "upper": endpoint(value.upper()), "finite": True}


def zero_consistency(value):
    return {"enclosure": exact_ball(value), "contains_zero": bool(value.contains(0)),
            "authority": "INTERVAL_CONSISTENCY_ONLY"}


def native_geometry(K, L):
    import sympy as s
    from flint import arb, arb_mat
    n = list(range(-K, K + 1))
    size = len(n)
    one = s.ones(size, 1)
    nv = s.Matrix(n)
    N2 = nv.applyfunc(lambda x: x*x) - one * sum(x*x for x in n) / size
    reversal = s.zeros(size)
    for i in range(size):
        reversal[i, size - i - 1] = 1
    E = (s.eye(size) + reversal) / 2 - one*one.T/size - N2*N2.T/N2.dot(N2)
    O = (s.eye(size) - reversal) / 2 - nv*nv.T/nv.dot(nv)
    convert = lambda M: arb_mat([[arb(int(M[i, j].p)) / int(M[i, j].q)
                                  for j in range(M.cols)] for i in range(M.rows)])
    E, O, N2 = map(convert, (E, O, N2))
    a = (L / (4*arb.pi()))**2
    h = arb_mat([[1/(a+t*t)] for t in n])
    D = arb_mat([[arb(n[i]) if i == j else arb(0) for j in range(size)] for i in range(size)])
    ve, vo = E*h, O*D*h
    even_normal_sq, odd_normal_sq = (ve.transpose()*ve)[0, 0], (vo.transpose()*vo)[0, 0]
    if not bool(even_normal_sq > 0 and odd_normal_sq > 0):
        raise ArithmeticError("pole normal norm is unresolved")
    Qe, Qo = E - ve*ve.transpose()/even_normal_sq, O - vo*vo.transpose()/odd_normal_sq
    e1 = [0, 1, -4, 6, -4, 1, 0]
    e2 = [1, 0, -9, 16, -9, 0, 1]
    values = [arb(0)]*size
    for i in range(7):
        values[K - 3 + i] = 6*(a+4)*e1[i] - (a+9)*e2[i]
    u = arb_mat([[v] for v in values])
    even_norm_sq = 84*(11*a*a + 18*a + 21)
    odd_norm_sq = 36*(21*a*a + 98*a + 181)
    pe, po = u/even_norm_sq.sqrt(), D*u/odd_norm_sq.sqrt()
    return {"n": n, "a": a, "h": h, "D": D, "E": E, "O": O, "Qe": Qe,
            "Qo": Qo, "N2": N2, "ve": ve, "vo": vo,
            "even_normal_sq": even_normal_sq, "odd_normal_sq": odd_normal_sq,
            "pe": pe, "po": po}


def seed_algebra():
    """Verify exact symbolic identities before substituting a native aperture."""
    import sympy as s
    a = s.symbols("a", positive=True)
    n = list(range(-3, 4))
    e1, e2 = [0, 1, -4, 6, -4, 1, 0], [1, 0, -9, 16, -9, 0, 1]
    u = s.Matrix([6*(a+4)*x - (a+9)*y for x, y in zip(e1, e2)])
    du = s.Matrix([t*v for t, v in zip(n, u)])
    checks = {
        "M0": s.simplify(sum(u)) == 0,
        "M2": s.simplify(sum(t*t*v for t, v in zip(n, u))) == 0,
        "elementary_even_pole": s.simplify(sum(v/(a+t*t) for t, v in zip(n, u))) == 0,
        "elementary_odd_pole": s.simplify(sum(t*v/(a+t*t) for t, v in zip(n, du))) == 0,
        "M4": s.expand(sum(t**4*v for t, v in zip(n, u))) == -720,
        "even_norm": s.expand((u.T*u)[0] - 84*(11*a*a+18*a+21)) == 0,
        "odd_norm": s.expand((du.T*du)[0] - 36*(21*a*a+98*a+181)) == 0,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def evaluate_row(carrier, G, M, channels):
    from flint import arb, arb_mat
    even = carrier.endswith("even")
    Q = G[("Qe" if even else "Qo") if carrier.startswith("pole_neutral") else ("E" if even else "O")]
    p = G["pe" if even else "po"]
    projected = Q*M*Q
    lam = (p.transpose()*M*p)[0, 0]
    residual = projected*p - p*lam
    actions = {k: Q*matrix*p for k, matrix in channels.items()}
    levels = {k: (p.transpose()*matrix*p)[0, 0] for k, matrix in channels.items()}
    parts = {k: actions[k] - p*levels[k] for k in actions}
    names = list(parts)
    gram = [[(parts[i].transpose()*parts[j])[0, 0] for j in names] for i in names]
    total = arb_mat([[arb(0)] for _ in range(p.nrows())])
    for part in parts.values():
        total += part
    residual_sq = (residual.transpose()*residual)[0, 0]
    variance = (p.transpose()*projected*projected*p)[0, 0] - lam*lam
    gram_sum = sum((value for row in gram for value in row), arb(0))
    consistency = {
        "unit_norm": zero_consistency((p.transpose()*p)[0, 0] - 1),
        "carrier_projection": [zero_consistency((Q*p - p)[i, 0]) for i in range(p.nrows())],
        "channel_residual_sum": [zero_consistency((total-residual)[i, 0]) for i in range(p.nrows())],
        "residual_variance": zero_consistency(residual_sq-variance),
        "full_gram_sum": zero_consistency(residual_sq-gram_sum),
    }
    gersh = []
    for i in range(M.nrows()):
        radius = sum((abs(projected[i, j]) for j in range(M.ncols()) if i != j), arb(0))
        gersh.append(projected[i, i]-radius)
    lower = min(value.lower() for value in gersh)
    m4 = sum((t**4*p[i, 0] for i, t in enumerate(G["n"])), arb(0))
    source = {"status": "NOT_APPLICABLE", "reason": "even source functional has even legal domain"}
    if even:
        N2, ve = G["N2"], G["ve"]
        nu = (N2.transpose()*N2)[0, 0]
        S = (N2.transpose()*M*p)[0, 0]/nu
        b = (G["h"].transpose()*N2)[0, 0]/nu
        alpha = (ve.transpose()*G["E"]*M*p)[0, 0]/G["even_normal_sq"]
        S0 = S - b*alpha
        source = {"status": "EVALUATED", "definition": "N2^* canonicalSourceMatrix p / ||N2||^2",
                  "source_binding": "Zeta23.CCM.evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment",
                  "S": exact_ball(S), "b": exact_ball(b), "alpha": exact_ball(alpha),
                  "S0": exact_ball(S0), "correction": exact_ball(S0-S),
                  "corrected_intertwining_authority": "PAPER; not claimed Lean-proved"}
    applicable = {"ground_vector": "UNRESOLVED: no eigenspace enclosure computed",
                  "parity_gap": "UNRESOLVED", "within_parity_cluster": "UNRESOLVED",
                  "resolvent": "NOT_EVALUATED: no certified strict branch",
                  "fixed_source_detector": "OPEN: probe is not the original detector"}
    return {"carrier": carrier, "status": "EVALUATED_NATIVE_PROBE", "probe_id": "K3_pole_neutral_symbolic_seed_zeroextended",
            "is_hypothetical_zero_generated_detector": False, "dimension": G["E"].nrows()//2-2 if carrier.startswith("pole_neutral") else G["E"].nrows()//2-1,
            "rayleigh": exact_ball(lam), "bottom_enclosure": {"lower": exact_ball(lower)["lower"], "upper": exact_ball(lam)["upper"],
                "method": "ambient compressed Gershgorin lower and exact-carrier trial upper"},
            "residual_norm_sq": exact_ball(residual_sq), "spectral_variance": exact_ball(variance),
            "channel_names": names, "channel_rayleigh": {k: exact_ball(v) for k, v in levels.items()},
            "residual_gram_real": [[exact_ball(v) for v in row] for row in gram],
            "residual_gram_imaginary": "ZERO_BY_REAL_PROBE_AND_REAL_SYMMETRIC_NATIVE_CHANNELS",
            "M4": exact_ball(m4), "native_source": source, "consistency": consistency,
            "remaining_quantities": applicable,
            "authority": "RIGOROUS_POINT_ENCLOSURES; consistency checks are not universal theorem authority"}
