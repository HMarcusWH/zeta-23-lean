"""Check rational constants, cutoff endpoints and the small finite first-band range."""
from fractions import Fraction as Q
from hashlib import sha256
from math import comb
import json
from pathlib import Path

DIR = Path(__file__).resolve().parent


def root_floor(n, degree):
    lo, hi = 0, 1 << ((n.bit_length() + degree - 1) // degree)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** degree <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi ** degree <= n else lo


def small_table():
    low = [0, 1]
    for n in range(2, 33):
        low.append(-sum(low[d] for d in range(1, n) if n % d == 0))
    total = 0
    for n, value in enumerate(low[1:], 1):
        total += value
        assert total ** 2 <= n
    return low


def main():
    small_table()
    top = root_floor((10**16)**100, 101)
    assert top**101 <= 10**1600 < (top+1)**101
    ratio = Q(29,20)
    assert ratio**101 > 10**16 and ratio < Q(5,3)
    # Use r > sqrt(29/20) and monotonicity of the integral evaluated at r^2.
    r = Q(120417,100000)
    assert r*r > ratio
    f_bound = 2*Q(571,1000)*(Q(4,3)-2/r+Q(2,3)/r**3+(ratio-1)/2048)
    assert f_bound < Q(1,16)
    best, best_l = Q(0), None
    for l in range(2,2048):
        n = root_floor(l**101,100)
        assert n < 2*l
        h = n-l
        # Sum h(h-1)/2 over n=L+1,...,L+H (denominator replaced by L^3).
        upper_squared = Q(comb(h+1,3)**2, l**5)
        assert upper_squared < Q(1,256)
        if upper_squared > best:
            best, best_l = upper_squared, l
    # sqrt(1/2)<.7072, sqrt(1/3)<.5774, pi in (3.14,22/7).
    assert Q(7072,10000)**2>Q(1,2) and Q(5774,10000)**2>Q(1,3)
    geo = 1/((1-Q(7072,10000))*(1-Q(5774,10000)))
    assert geo<Q(81,10)
    pi_lo, pi_hi = Q(314,100), Q(22,7)
    sinc_lo = 1-(pi_hi/100)**2/6
    weight_upper = 1/(2*pi_lo**2*sinc_lo**2)
    assert weight_upper < Q(51,1000)
    assert 2*weight_upper*geo < Q(5,6)
    edge_fraction = Q(24,25)*(1-(3*pi_hi/16)**2/2)
    assert edge_fraction > Q(3,4)
    assert Q(98,100)**2 > Q(24,25)
    assert Q(3,4)*(1-Q(98,100)) == Q(3,200)
    out = {"qualification":"Exact endpoint and elementary constants of the transfer. Large-range Mertens input is published external evidence.",
           "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
           "full_statistic_top_L":top,
           "full_statistic_top_site":root_floor(top**101,100),
           "range_L_2_through_2047_checked":2046,
           "small_L_maximizing_trivial_normalized_squared_bound":best_l,
           "small_maximum_squared":str(best),
           "large_normalized_bound_strict_upper":str(f_bound),
           "coprime6_geometric_upper":str(geo),
           "literal_weight_upper_per_L":str(weight_upper),
           "literal_harmonic_top_L":10**16,
           "native_renewal_critical_defect_lower":"3/200",
           "recovery_norm_upper_critical":"200/3 when the input is T_L/w_L"}
    (DIR/"FINITE_RANGE_CONSTANTS.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(out))


if __name__=="__main__":
    main()
