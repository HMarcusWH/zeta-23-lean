"""Finite arithmetic, kernel normalization, and local signed-filter controls."""
from collections import Counter
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.integrate import simpson
from flint import acb, arb, ctx


def primes_up_to(limit):
    flags = np.ones(limit+1, dtype=bool)
    flags[:2] = False
    for i in range(2, int(limit**0.5)+1):
        if flags[i]:
            flags[i*i::i] = False
    return np.flatnonzero(flags)


def kernel_grid(u):
    v = np.abs(u)
    h = np.zeros_like(v)
    for n in range(1, 7):
        z = np.pi * n*n * np.exp(2*v)
        h += np.exp(v/2-z) * (4*z*z-6*z)
    return h


def xi(z):
    return z*(z-1)*mp.power(mp.pi, -z/2)*mp.gamma(z/2)*mp.zeta(z)/2


def signed_zero_bracket():
    ctx.prec = 180
    rows = []
    for t in [14,15]:
        s = acb(arb(1)/2,t)
        value = s*(s-1)/2 * acb(arb.pi())**(-s/2) * (s/2).gamma() * s.zeta()
        assert value.imag.contains(0)
        assert (value.real > 0 if t==14 else value.real < 0)
        rows.append({"ordinate":t,"xi_ball":str(value)})
    return {"endpoints":rows,"interpretation":"On the critical line xi is continuous and real by reflection. The opposite signs enclose a critical-line zero below 15, sufficient for the mean-square lower bound."}


def kernel_checks():
    mp.mp.dps = 52
    grid = np.linspace(-2.4, 2.4, 8193)
    weights = kernel_grid(grid)
    first = mp.zetazero(1)
    rows = []
    for z in [0, -1/6, 0.25, 0.2+4j, complex(first)-0.5]:
        computed = simpson(weights * np.exp(-z*grid), x=grid)
        expected = complex(xi(mp.mpc(z)+mp.mpf('0.5')))
        assert abs(computed-expected) < 3e-14
        rows.append({"shift": str(z), "quadrature_real": float(computed.real),
                     "quadrature_imag": float(computed.imag), "absolute_difference": abs(computed-expected)})
    return rows


def local_cost_checks():
    # Synthetic nonreal, off-axis parameter to exercise the conditional four-point formula.
    p = mp.mpc('0.2', '17')
    expected = 192/abs(p)**4
    rows = []
    for r in map(mp.mpf, ['0.04','0.01','0.0025','0.000625','0.00015625']):
        f, g = mp.cosh(p*r)-1, mp.cosh(p*r/mp.sqrt(2))-1
        a, b = mp.lu_solve(mp.matrix([[f.real, g.real], [f.imag, g.imag]]), mp.matrix([-1, 0]))
        c = 1-a-b
        residual = max(abs(a*mp.cosh(z*r)+b*mp.cosh(z*r/mp.sqrt(2))+c)
                       for z in [p, -p, p.conjugate(), -p.conjugate()])
        assert residual < mp.mpf('1e-32')
        ratio = r**4*(abs(a)+abs(b)+abs(c))/expected
        rows.append({"radius": str(r), "scaled_cost_over_limit": float(ratio),
                     "largest_annihilation_residual": float(residual)})
    assert abs(rows[-1]["scaled_cost_over_limit"]-1) < 1e-5
    return rows


def mobius(k):
    original = k
    sign = 1
    for p in range(2, original+1):
        if k % p == 0:
            k //= p
            if k % p == 0:
                return 0
            sign = -sign
    return sign


def incidence_checks(primes, cutoff):
    # Compare integer coefficients of log p for every p, before numerical summation.
    rows_by_layer = Counter()
    net_by_order = Counter()
    edges = 0
    for raw in primes[primes <= cutoff]:
        p = int(raw)
        value, order = p, 1
        prim_coeff = 0
        while value <= cutoff:
            net = 0
            for k in range(1, order+1):
                if order % k:
                    continue
                mu = mobius(k)
                rows_by_layer[k] += 1
                net += mu
                edges += 1
            assert net == (order == 1)
            net_by_order[order] += net
            prim_coeff += net * (cutoff-value)
            value *= p
            order += 1
        assert prim_coeff == cutoff-p
    return {"cutoff": cutoff, "divisibility_edges": edges, "edges_by_k": dict(rows_by_layer),
            "net_event_count_by_prime_power_exponent": dict(net_by_order)}


def true_local_edges():
    # The filter parameter is a test. Every prime location, weight and triangular edge below is genuine.
    import bisect
    primes = list(map(int, primes_up_to(32000)))
    logs = [mp.log(p) for p in primes]
    sums, moments = [mp.mpf(0)], [mp.mpf(0)]
    for p, weight in zip(primes, logs):
        sums.append(sums[-1]+weight)
        moments.append(moments[-1]+p*weight)

    def true_area(y):
        n = bisect.bisect_right(primes, y)
        return y*sums[n]-moments[n]-(y*y-4)/2

    rows = []
    p = mp.mpc('0.2', '17')
    for center in [300, 3000, 30000]:
        x = mp.mpf(center)
        index = bisect.bisect_right(primes, x)
        for r in map(mp.mpf, ['0.04','0.02','0.01']):
            f, g = mp.cosh(p*r)-1, mp.cosh(p*r/mp.sqrt(2))-1
            a, b = mp.lu_solve(mp.matrix([[f.real,g.real],[f.imag,g.imag]]),mp.matrix([-1,0]))
            cuts = [(-r,a/2),(-r/mp.sqrt(2),b/2),(mp.mpf(0),1-a-b),(r/mp.sqrt(2),b/2),(r,a/2)]
            direct = anchor = local = mp.mpf(0)
            edges = 0
            for u, w in cuts:
                y = x*mp.exp(u)
                j = bisect.bisect_right(primes,y)
                if y >= x:
                    tent = mp.fsum((y-primes[i])*logs[i] for i in range(index,j))
                else:
                    tent = mp.fsum((primes[i]-y)*logs[i] for i in range(j,index))
                edges += abs(j-index)
                factor = w/y**mp.mpf('1.5')
                direct += factor*true_area(y)
                anchor += factor*(true_area(x)+(y-x)*(sums[index]-x))
                local += factor*(tent-(y-x)**2/2)
            assert abs(direct-anchor-local) < mp.mpf('1e-38')
            rows.append({"center":center,"radius":float(r),"prime_cut_incidences":edges,
                         "filtered_true_area":float(direct),"signed_local_remainder":float(local),
                         "identity_residual":float(abs(direct-anchor-local))})
    return rows


def area_checks():
    centers = [1000, 10000, 100000, 1000000]
    bound = int(np.ceil(max(centers)*np.exp(2.4)))
    primes = primes_up_to(bound)
    logs = np.log(primes)
    theta = np.r_[0, np.cumsum(logs)]
    weighted = np.r_[0, np.cumsum(primes*logs)]
    rows = []
    for center in centers:
        values = []
        for samples in [4097, 8193]:
            grid = np.linspace(-2.4, 2.4, samples)
            x = center*np.exp(-grid)
            idx = np.searchsorted(primes, x, side="right")
            normalized = (x*theta[idx]-weighted[idx]-(x*x-4)/2)/x**1.5
            k = kernel_grid(grid)
            values.append(float(simpson(k*normalized, x=grid)/simpson(k, x=grid)))
        assert abs(values[1]-values[0]) < 1e-4
        rows.append({"center": center, "average_normalized_by_kernel_mass": values[1],
                     "quadrature_refinement_difference": abs(values[1]-values[0])})
    return rows, incidence_checks(primes, 1000000)


if __name__ == "__main__":
    kernel = kernel_checks()
    areas, incidence = area_checks()
    result = {"classification": "Finite integer identities and diagnostic quadrature; infinite-range results rely on the paper proofs.",
              "kernel_checks": kernel, "critical_pair_interval":signed_zero_bracket(),
              "genuine_weighted_prime_area_checks": areas,
              "prime_power_graph": incidence, "synthetic_quartet_checks": local_cost_checks(),
              "true_local_prime_edges_with_test_filter":true_local_edges()}
    Path(__file__).with_name("ECHO_CONTROLS.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf8")
    print(json.dumps({"quadrature": areas, "incidence_edges": incidence["divisibility_edges"],
                      "cost_ratios": [v["scaled_cost_over_limit"] for v in result["synthetic_quartet_checks"]]}))
