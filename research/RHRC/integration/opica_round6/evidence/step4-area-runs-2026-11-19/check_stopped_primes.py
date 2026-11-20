"""Certified branch comparisons for the complete finite prime graph, with control slopes."""
import json
from math import isqrt
from pathlib import Path

from flint import arb, ctx


def prime_list(bound):
    flags = bytearray([1]) * (bound+1)
    flags[:2] = b"\0\0"
    for p in range(2, isqrt(bound)+1):
        if flags[p]:
            flags[p*p::p] = b"\0" * (1 + (bound-p*p)//p)
    return [p for p in range(2,bound+1) if flags[p]]


def main():
    ctx.prec = 160
    limit = 10**6
    primes = prime_list(limit+1024)
    assert primes[-1] > limit
    cases = [(a,b,arb(a)/b) for a,b in [(1,1),(19,20),(49,50),(99,100),(199,200)]]
    reports = {f"{a}/{b}":{"stops":0,"positive":0,"negative":0,"examples":[]} for a,b,_ in cases}
    mass, moment, midpoint = arb(0), arb(0), arb(0)
    count = 0
    for p, successor in zip(primes,primes[1:]):
        if p>limit:
            break
        count += 1
        log_p = arb(p).log()
        mass += log_p
        moment += p*log_p
        midpoint += log_p * (mass-log_p/2-p)
        gap = mass*mass/2-moment
        assert (midpoint-gap).contains(0)
        for a,b,slope in cases:
            # Avoid division when deciding the strict stopped-vertex inequalities.
            if mass < slope*p or mass > slope*successor:
                continue
            assert mass > slope*p and mass < slope*successor
            row = reports[f"{a}/{b}"]
            row["stops"] += 1
            x = mass/slope
            vertex = mass*mass/(2*slope)-moment+2*slope
            direct = x*mass-moment-slope*(x*x-4)/2
            vertex_at_prime = p*mass-moment-slope*(arb(p)**2-4)/2 + slope*(x-p)**2/2
            assert (direct-vertex).contains(0) and (vertex_at_prime-vertex).contains(0)
            assert vertex > 0 or vertex < 0
            row["positive" if vertex>0 else "negative"] += 1
            if len(row["examples"])<3:
                row["examples"].append({"p":p,"next":successor,"vertex":str(vertex),"location":str(x)})
    assert reports["1/1"]["stops"] == 0
    assert all(reports[f"{a}/{b}"]["stops"]>0 for a,b,_ in cases if a!=b)
    result = {"upper_prime":limit,"primes_checked_with_successor":count,"precision_bits":ctx.prec,
              "arithmetic":"Arb balls; selection, sign, and interior comparisons exclude zero. Equivalent finite evaluations have overlapping enclosures.",
              "slope_1":"Actual ordinary-prime Step 4 input. The prefix has no eligible interior maximum.",
              "other_slopes":"Controls use the same primes and log weights and a different continuum; they exercise the branch without supplying evidence about later true stops.",
              "rows":reports}
    Path(__file__).with_name("STOPPED_PRIME_CHECK.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print(count, {k:(r["stops"],r["positive"]) for k,r in reports.items()})


if __name__=="__main__":
    main()
