"""Exact prefix discrepancy for the power-delay replay, with independent prefix inversion."""
from array import array
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
from time import monotonic

from flint import arb, ctx, fmpz


def ball(value):
    s = value.str(27)
    assert arb(s).contains(value)
    return s


def run():
    t0 = monotonic()
    ctx.prec = 128
    here = Path(__file__).resolve()
    full_path = here.with_name("POWER_DELAY_CHECK.json")
    data = json.loads(full_path.read_bytes())
    x = data["x"]
    Y, m, K = isqrt(isqrt(x)), data["m"], data["K"]
    b = {e:Fraction(int(fmpz(e).moebius_mu())) for e in range(1,Y+1) if gcd(e,6)==1}
    b = {e:c for e,c in b.items() if c}
    b[m] = -m*sum((v/e for e,v in b.items()),Fraction())
    den = b[m].denominator
    assert b[m]==Fraction(data["b_m"]) and sum((v/e for e,v in b.items()),Fraction())==0
    # Sieve all integer contributions. Backbone coefficients for e<=Y are integral.
    linear = array("b",[0])*(x+1)
    for e in b:
        if e==m:
            continue
        for off in (1,5):
            for k in range(e*off,x+1,6*e):
                linear[k]+=int(b[e])
    c6 = array("i",[0])*(x+1)
    for k in range(1,x+1):
        c6[k] = c6[k-1] + (k%6 in (1,5))
    vals = [(e,int(v)) for e,v in b.items() if e!=m]
    pref = lo = hi = 0
    arg_lo = arg_hi = 0
    lo_mid = hi_mid = lo_tail = hi_tail = None
    points = {1, Y,m,K,K+1,x}
    selected = {}
    num = b[m].numerator
    lower_count = 0
    nonzero = 0
    for k in range(1,x+1):
        wk = den*linear[k]+(num if k%m==0 and k//m%6 in (1,5) else 0)
        pref += wk
        nonzero += wk!=0
        if k==1 or 2<=k<=Y:
            assert wk==(den if k==1 else 0)
        # Independent closed formula sum_e b_e*C6(floor(k/e)); the cancelled
        # linear main term is (k/3)*sum_e b_e/e, exactly zero.
        alt = den*sum(v*c6[k//e] for e,v in vals)+num*c6[k//m]
        assert pref==alt
        lower_count += pref==alt
        if pref<lo:
            lo,arg_lo = pref,k
        if pref>hi:
            hi,arg_hi = pref,k
        if m<=k<=K:
            lo_mid=min(lo_mid,pref) if lo_mid is not None else pref
            hi_mid=max(hi_mid,pref) if hi_mid is not None else pref
        if K<k:
            lo_tail=min(lo_tail,pref) if lo_tail is not None else pref
            hi_tail=max(hi_tail,pref) if hi_tail is not None else pref
        if k in points:
            selected[str(k)]=str(Fraction(pref,den))
    absolute_uniform_bound=Fraction(2,3)*sum(map(abs,b.values()))
    assert max(abs(lo),abs(hi))<=absolute_uniform_bound*den
    data["exact_prefix_discrepancy"] = dict(
        definition="W(t)=sum_{k<=t}w(k)=sum_e b_e[C6(t/e)-t/(3e)], C6(u)=#{1<=n<=u:gcd(n,6)=1}. For real t, W is constant on each interval between integer sites.",
        independent_constructions="Every one of the integer prefixes compared from a divisor-weight sieve and the separate sum of b_e*C6(floor(t/e)); C6 is computed via the coprime-to-6 indicator.",
        integer_prefix_count=lower_count,through=x,nonzero_weight_indices=nonzero,
        exact_minimum=str(Fraction(lo,den)),first_minimum_at=arg_lo,
        exact_maximum=str(Fraction(hi,den)),first_maximum_at=arg_hi,
        exact_maximum_absolute=str(Fraction(max(abs(lo),abs(hi)),den)),
        all_real_t_discrepancy_absolute_upper=str(absolute_uniform_bound),
        bound_proof="C6(t+6)=C6(t)+2. Inspecting the jumps at t=1,5 in [0,6] gives |C6(t)-t/3|<=2/3 for all real t>=0.",
        middle_prefix_range=[str(Fraction(lo_mid,den)),str(Fraction(hi_mid,den))],
        tail_prefix_range=[str(Fraction(lo_tail,den)),str(Fraction(hi_tail,den))],selected_prefixes=selected)
    sqrt_x = arb(x).sqrt()
    normalized = {}
    for sector in ("middle","tail"):
        s = data[sector]
        norm = arb(s["historical_sup_abs_v_over_sqrt_argument"]["maximum"])
        signed = arb(s["signed"])/sqrt_x
        normalized[sector]=dict(signed_over_sqrt_x=ball(signed),
            absolute_signed_over_sqrt_x_over_discrete_sector_history_sup=ball(abs(signed)/norm),
            triangle_rows_over_sqrt_x=ball(arb(s["sum_absolute_rows"])/sqrt_x))
    data["critical_normalizations"] = normalized
    data["product_replay_receipt_sha256"] = sha256(full_path.read_bytes()).hexdigest()
    data["prefix_script_sha256"] = sha256(here.read_bytes()).hexdigest()
    data["prefix_seconds"] = round(monotonic()-t0,2)
    here.with_name("POWER_DELAY_REPLAY.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps([data["exact_prefix_discrepancy"],normalized,data["prefix_seconds"]],indent=2))


if __name__=="__main__":
    run()
