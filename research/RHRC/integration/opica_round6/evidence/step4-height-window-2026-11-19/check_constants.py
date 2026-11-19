"""Rational checks for the external contact polynomial and the native height estimate."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

COEFF = [-274959111914881, 2643837682856883, -11291220876239226,
         28111661257098222, -44964545308854309, 47916748658170215,
         -34020380857037616, 15517896164111592, -4126408710053184,
         487371101862528]


def tracker(x):
    value = 0
    for c in reversed(COEFF):
        value = value*x+c
    return value


def contact(x):
    return 3888*19**5*(15*x-13)**4*(1-x)**5 - 7*(7-6*x)**4*(9*x-7)**5


def exp_interval(x, m=110):
    x = F(x)
    term = partial = F(1)
    for k in range(1, m+1):
        term = term*x/k
        partial += term
    assert 0 < x < m+2
    return partial, partial + (term*x/(m+1))/(1-x/(m+2))


def decfloor(x, digits):
    n = (x.numerator*10**digits)//x.denominator
    return f"{n//10**digits}.{n%10**digits:0{digits}d}"


def main():
    # Both expressions have degree at most nine. Ten distinct values prove identity.
    scale = F(contact(0), tracker(0))
    assert all(contact(x) == scale*tracker(x) for x in range(10))
    low, high = F(13,15), F(7,8)
    assert tracker(low)*tracker(high)<0
    for _ in range(160):
        mid = (low+high)/2
        if tracker(low)*tracker(mid)>0:
            low=mid
        else:
            high=mid
    assert decfloor(low,24)==decfloor(high,24)
    assert high-F(1,2) < F(374,1000)
    m0 = isqrt(3*10**12)
    assert m0==1732050
    # Geometric summation, exponential prefactor, and polynomial in the first bin.
    assert F(18,m0+2) < F(1,16)-F(1,17)
    assert exp_interval(F(1,17))[0] > 1+F(1,17)
    assert exp_interval(8+F(1,4096))[1] < 3000
    assert exp_interval(14)[0] > 1200000
    assert exp_interval(F(260,18))[0] > m0+2
    assert 14+260-F(m0,16) < -107900
    horizon=288000
    growth=F(374,1000)*horizon
    assert growth==107712
    mass_lower=F(4096,32)
    assert mass_lower==128 and 2/mass_lower<1 and growth-107900 < -180
    result=dict(endpoint_truncated=decfloor(low,24), tracker_scale=str(scale),
                endpoint_isolation_input="Candidate.bound_isolated at 42cf5415",
                fine_bracket=[str(low),str(high)], height=3*10**12,
                first_bin=m0, tail_log_upper=-107900, log_time=horizon,
                growth_log_upper=int(growth), mass_lower=int(mass_lower),
                normalized_negative_floor="-exp(-180)",
                scope="Exact rational scalar checks. Functional inequalities and external theorems are documented separately.")
    Path(__file__).with_name("HEIGHT_CONSTANTS.json").write_text(
        json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result["endpoint_truncated"],"height scalars PASS")


if __name__ == "__main__":
    main()
