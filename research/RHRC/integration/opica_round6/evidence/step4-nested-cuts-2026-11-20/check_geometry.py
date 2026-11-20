"""Cross-check the Lean definitions' integer conventions against the pinned generator."""
from collections import Counter
from fractions import Fraction
from math import isqrt
from finite_replay import native, replay, require


def check(x, generator):
    cap = 1
    floor_log = x.bit_length()-1
    s = isqrt(floor_log) + int(isqrt(floor_log)**2<floor_log)
    y = (x-1).bit_length()**2
    # Independent smallest-prime-factor table, direct signature and cell calculation.
    factors = list(range(x+1))
    for p in range(2,isqrt(x)+1):
        if factors[p] == p:
            for multiple in range(p*p, x+1, p):
                if factors[multiple] == multiple:
                    factors[multiple] = p
    rows = []
    keys = Counter()
    plus = Counter()
    minus = Counter()
    lower = generator.first_terminal(x)
    require((lower-1)**100 <= x**99 < lower**100, "strict terminal cutoff")
    for n in range(lower,x+1):
        q,ps = n, []
        while q>1:
            p=factors[q]
            ps.append(p)
            q//=p
        if len(set(ps))!=len(ps) or any(p<=y for p in ps):
            continue
        sign = (-1)**len(ps)
        cone = n//max(ps,default=1) <= cap
        rows.append((n,sign,cone,sign*(-1 if cone else 1),-1 if cone else 1))
        j = n.bit_length()-1
        for k in range(j+1-s):
            h = 2**(j-s-k)
            key=(j,k,n//h)
            require(key[2]*h <= n < (key[2]+1)*h, "cell membership")
            keys[key]+=1
            (plus if sign==1 else minus)[key]+=1
    require(rows == list(generator.vertex_rows(x,cap)), "genuine signed/cone label mismatch")
    coarse = [k for k in keys if 2*k[1] < k[0]-s]
    complete = [k for k in coarse if x**99 < (2**k[0])**100 and 2**(k[0]+1)<=x+1]
    energy = sum((Fraction(max(plus[k]-minus[k],0)**2,2**(k[0]+k[1])) for k in coarse),Fraction())
    official = generator.measure(x,cap)
    require(str(energy) == official["positive_charge_energy"] and len(keys) == official["occupied_nodes"],
            "coarse energy or occupied node mismatch")
    return dict(X=x,s=s,y=y,first_label_candidate=lower,rough_squarefree_count=len(rows),
                even=len([r for r in rows if r[1]==1]),odd=len([r for r in rows if r[1]==-1]),
                occupied_nodes=len(keys),coarse_nodes=len(coarse),strict_complete_shell_coarse_nodes=len(complete),
                true_generator_energy=str(energy),source_match=True)

def calculate():
    generator = native()
    rows = [check(x, generator) for x in (65536, 65537, 1049155, 1656575)]
    return dict(method="All true signed generator rows, cone membership and occupied keys. Integer source boundary and native coarse energy recomputed independently.", rows=rows)


if __name__ == "__main__":
    replay("GEOMETRY_REPLAY.json", calculate, sort_keys=False)
