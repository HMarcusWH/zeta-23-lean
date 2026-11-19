"""Finite true-weight controls for the squarefree inequality and the mismatch identity."""
from bisect import bisect_right
import json
from pathlib import Path

from flint import arb, ctx


def main():
    ctx.prec = 160
    bound = 40000
    factors = [[] for _ in range(bound+1)]
    squarefree = bytearray([1])*(bound+1)
    primes = []
    for p in range(2,bound+1):
        if not factors[p]:
            primes.append(p)
            for n in range(p, bound+1, p):
                factors[n].append(p)
            for n in range(p*p, bound+1, p*p):
                squarefree[n] = 0
    logs = {p:arb(p).log() for p in primes}
    smallest = None
    stop = 0
    total = 0
    for n in range(8,bound+1):
        if not squarefree[n]:
            continue
        total += 1
        source = factors[n]
        z = arb(n).log()
        assert (z-sum((logs[p] for p in source),arb(0))).contains(0)
        w = sum((p*logs[p] for p in source),arb(0))
        d = z*z/2-w+2
        assert d<0
        if smallest is None or -d<smallest[1]:
            smallest = (n,-d)
        j = int(z.floor().unique_fmpz())
        assert z>j and z<j+1
        for center in (z, arb(j)):
            last = bisect_right(primes, j)
            base = primes[:last]
            delta = set(base)^set(source)
            mismatch = sum((abs(center-p)*logs[p] for p in delta),arb(0))
            area = sum(((center-p)*logs[p] for p in base),arb(0))-(center*center-4)/2
            assert (mismatch-area+d-(z-center)**2/2).contains(0)
            if center==j:
                stop += int(not delta)
    result = {"upper_n": bound,"precision_bits":ctx.prec,"squarefree_n_examined":total,"violations":0,
              "smallest_observed_margin_for_W_minus_log_squared_over_two_minus_two":
                  {"n":smallest[0],"ball":str(smallest[1])},
              "equal_factor_sets_at_integer_center":stop,
              "scope":"Genuine primes, squarefree products, real and integer bucket centers. Algebra independently bounds enumerated values. Finite check only."}
    Path(__file__).with_name("SQUAREFREE_CHECK.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print(total, smallest[0], str(smallest[1]))


if __name__=="__main__":
    main()
