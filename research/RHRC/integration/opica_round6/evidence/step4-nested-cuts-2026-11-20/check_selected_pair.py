"""Track one actual opposite-sign deletion at every native coarse depth."""
from collections import Counter
from fractions import Fraction
from math import isqrt
from finite_replay import GENERATOR_SHA256, native, replay, require


def calculate():
    generator = native()
    x=1656575
    s=isqrt(x.bit_length()-1)
    s+=s*s<x.bit_length()-1
    rows=list(generator.vertex_rows(x,1))
    base={}
    charge=Counter()
    counts=Counter()
    def keys(n):
        j=n.bit_length()-1
        for k in range((j-s+1)//2):
            yield (j,k,n//(2**(j-s-k)))
    for n,sign,cone,_,_ in rows:
        ks=list(keys(n))
        base.setdefault(ks[0],[]).append((n,sign,cone))
        for key in ks:
            charge[key]+=sign
            counts[key]+=1
    # Choose the first occupied native base cell with an observable positive-energy change.
    for (j,k,i),eligible in sorted(base.items()):
        targets=[n for n,sg,c in eligible if sg==-1 and c]
        donors=[n for n,sg,c in eligible if sg==1 and not c]
        if targets and donors:
            target=min(targets)
            target_keys=set(keys(target))
            partner=next((n for n in donors if any(key not in target_keys and charge[key]>0 for key in keys(n))),None)
            if partner is not None:
                break
    else:
        raise ValueError("no genuine coarse base-cell match")
    full=selected=loss=change=Fraction()
    moved=Counter()
    for key in keys(target):
        moved[key]-=1
    for key in keys(partner):
        moved[key]+=1
    for key,n in counts.items():
        j,k,i=key
        w=Fraction(1,2**(j+k))
        f=charge[key]
        g=moved[key]
        full+=w*max(f,0)**2
        selected+=w*max(f-g,0)**2
        change+=w*abs(max(f,0)**2-max(f-g,0)**2)
        loss+=2*w*n*abs(g)
    require(full == Fraction(generator.measure(x,1)["positive_charge_energy"]), "full energy mismatch")
    require(change <= loss and full <= selected + loss, "selector cost mismatch")
    require(change > 0, "empty positive change control")
    require(any(moved.values()) and moved[next(iter(keys(target)))] == 0, "coarse endpoint accounting")
    return dict(X=x,selector="First occupied native base with a prime target and a positive noncone donor belonging to a separate coarse node of strictly positive charge. Illustrative finite selector.",
                 target=target,partner=partner,native_parent=next(iter(keys(target))),signed_removed_by_node=[
                     dict(key=list(key),charge=g) for key,g in sorted(moved.items())],full_positive_energy=str(full),
                 survivor_positive_energy=str(selected),absolute_change=str(change),signed_removal_cost=str(loss),
                 coarse_nodes=len(counts),source_sha256=GENERATOR_SHA256)


if __name__ == "__main__":
    replay("SELECTED_PAIR.json", calculate, sort_keys=False)
