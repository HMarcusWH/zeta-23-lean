"""Exhaustive whole-coarse positive-energy timelines on four native integer slabs."""
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

import numpy as np


LOW, HIGH = 20,24
MAX_X = 1<<HIGH


def floor_root(n,k):
    a,b=0,1<<((n.bit_length()+k-1)//k)
    while a<b:
        m=(a+b+1)//2
        if m**k<=n:
            a=m
        else:
            b=m-1
    return a


def primes_upto(n):
    sieve=np.ones(n+1,dtype=bool)
    sieve[:2]=False
    for p in range(2,isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p]=False
    return sieve


def source(y,primes):
    # Any retained q>1 has at most two prime factors with multiplicity here.
    assert (y+1)**3>MAX_X
    a=np.ones(MAX_X+1,dtype=np.int8)
    a[primes]=-1
    for p in np.flatnonzero(primes[:y+1]):
        a[::p]=0
    large=np.flatnonzero(primes[y+1:isqrt(MAX_X)+1])+y+1
    a[large*large]=0
    a[0]=0
    return a


def factors(n,small_primes):
    out=[]
    for p in small_primes:
        if p*p>n:
            break
        while n%p==0:
            out.append(p)
            n//=p
    if n>1:
        out.append(n)
    return out


def event_segments(pos,xlo,xhi):
    deltas=defaultdict(lambda:[0,Fraction(0)])
    for n in pos:
        value=Fraction(n["surplus"]**2,1<<(n["shell_exponent"]+n["depth"]))
        for time,sg in ((n["active_from"],1),(n["active_to"]+1,-1)):
            deltas[time][0]+=sg
            deltas[time][1]+=sg*value
    for t in (xlo,xhi+1):
        deltas[t]
    events=sorted(deltas)
    n=0
    v=Fraction(0)
    intervals=[]
    for t,u in zip(events,events[1:]):
        n+=deltas[t][0]
        v+=deltas[t][1]
        assert n>=0 and v>=0 and bool(v)==bool(n)
        if n:
            intervals.append({"first_X":t,"last_X":u-1,"positive_nodes":n,"V_plus_whole":str(v)})
    return intervals


def timeline(t,rough,a,primes):
    xlo=(1<<t)+1
    xhi=1<<(t+1)
    s=1+isqrt(t-1)
    assert s==1+isqrt(t) # s at final power-of-two endpoint
    first=floor_root(xlo**99,100)+1
    positive=[]
    possible=Counter()
    for j in range(first.bit_length()-1,t+1):
        u=1<<j
        d=max(0,j-s)
        # Every eligible node starting past first already fits the lower
        # cutoff at its own right endpoint, if that endpoint is later than xlo.
        assert (u+(1<<d))**99 < u**100
        for k in range((d+1)//2):
            h=1<<(d-k)
            i0=max(u//h,(first+h-1)//h)
            i1=min(2*u//h,(xhi+1)//h)
            if i1<=i0:
                continue
            block=a[i0*h:i1*h].reshape(-1,h)
            signed=block.sum(axis=1,dtype=np.int32)
            possible["positive"]+=int(np.count_nonzero(signed>0))
            possible["zero"]+=int(np.count_nonzero(signed==0))
            possible["negative"]+=int(np.count_nonzero(signed<0))
            for off in np.flatnonzero(signed>0):
                i=i0+int(off)
                l,r=i*h,(i+1)*h
                entry=max(xlo,r-1)
                exit=min(xhi,floor_root(l**100-1,99))
                assert entry<=exit and l**100>exit**99 and r-1<=entry
                assert entry==xlo or r-1==entry
                assert exit==xhi or l**100<=(exit+1)**99
                pc=int(np.count_nonzero(primes[l:r]))
                sc=int(np.count_nonzero(a[l:r]>0))
                f=int(signed[off])
                assert f==sc-pc
                positive.append(dict(shell_exponent=j,depth=k,lower=l,upper_exclusive=r,
                                     primes=pc,semiprimes=sc,surplus=f,active_from=entry,active_to=exit))
    positive.sort(key=lambda n:(n["active_from"],n["lower"],n["depth"]))
    intervals=event_segments(positive,xlo,xhi)
    return dict(integer_X_range=[xlo,xhi],y=rough,s=s,eligible_distinct_whole_cells=dict(possible),
                possible_cells_cover_every_eligible_depth=True,positive_cells=positive,
                positive_X_count=sum(v["last_X"]-v["first_X"]+1 for v in intervals),
                positive_intervals=intervals,maximum_positive_charge=max([0]+[v["surplus"] for v in positive]))


def direct(x,a):
    jstar=x.bit_length()-1
    s=1+isqrt(jstar-1)
    first=floor_root(x**99,100)+1
    energies=[Fraction(0),Fraction(0)]
    cnt=[Counter(),Counter()]
    for j in range(first.bit_length()-1,jstar+1):
        l,r=max(first,1<<j),min(x+1,2<<j)
        d=max(0,j-s)
        for k in range((d+1)//2):
            h=1<<(d-k)
            for i in range(l//h,(r-1)//h+1):
                lo,hi=max(l,i*h),min(r,(i+1)*h)
                kind=int((lo,hi)!=(i*h,(i+1)*h))
                sig=int(a[lo:hi].sum(dtype=np.int32))
                cnt[kind][("positive" if sig>0 else "negative" if sig<0 else "zero")]+=1
                if sig>0:
                    energies[kind]+=Fraction(sig*sig,1<<(j+k))
    return dict(X=x,first=first,counts_whole_clipped=[dict(q) for q in cnt],
                V_plus_whole=str(energies[0]),V_plus_clipped=str(energies[1]))


def first_higher_layers():
    from math import prod
    # The least squarefree label with k distinct prime factors has the first
    # k primes above y. This tests the exact threshold on each integer slab.
    result=[]
    for k in range(3,7):
        for t in range(LOW,180):
            y=(t+1)**2
            ps=[]
            n=y+1
            while len(ps)<k:
                if all(n%j for j in range(2,isqrt(n)+1)):
                    ps.append(n)
                n+=1
            q=prod(ps)
            if q<=1<<(t+1):
                assert q>1<<t and (q-1).bit_length()**2==y and q**100>q**99
                result.append({"number_distinct_prime_factors":k,"first_horizon_X":q,
                               "first_actual_label":q,"mu":(-1)**k,"y":y,"prime_factors":ps,
                               "all_earlier_integer_slabs_exhausted_from":1<<LOW})
                break
        else:
            raise AssertionError("Increase layer-onset search range")
    return result


def main():
    sieve=primes_upto(MAX_X)
    small=[int(p) for p in np.flatnonzero(sieve[:isqrt(MAX_X)+1])]
    fixed=source(400,sieve)
    base=direct(1<<LOW,fixed)
    assert base["V_plus_whole"]==base["V_plus_clipped"]=="0"
    native=[]
    controls=[]
    checks=[base]
    first_witness=None
    first_event=None
    for t in range(LOW,HIGH):
        y=(t+1)**2
        data=source(y,sieve)
        assert np.all(data[1<<(LOW-1):]<=fixed[1<<(LOW-1):])
        n=timeline(t,y,data,sieve)
        control=timeline(t,400,fixed,sieve)
        native.append(n)
        controls.append({"integer_X_range":control["integer_X_range"],"y":400,
                         "eligible_distinct_whole_cells":control["eligible_distinct_whole_cells"],
                         "positive_X_count":control["positive_X_count"],"maximum_positive_charge":control["maximum_positive_charge"],
                         "first_positive_X":min((v["active_from"] for v in control["positive_cells"]),default=None)})
        if n["positive_cells"] and first_witness is None:
            hit=n["positive_cells"][0]
            first_event=hit["active_from"]
            labels=[]
            for q in range(hit["lower"],hit["upper_exclusive"]):
                f=factors(q,small)
                sg=0 if min(f)<=y or len(set(f))!=len(f) else (-1)**len(f)
                assert int(data[q])==sg
                if sg:
                    labels.append({"q":q,"factors":f,"mu":sg})
            first_witness={"X":first_event,"cell":hit,"all_nonzero_labels":labels,
                           "checked_every_integer_in_cell_by_independent_trial_factorization":True,
                           "individual_node_weight":str(Fraction(1,1<<(hit["shell_exponent"]+hit["depth"])))}
        direct_points={n["integer_X_range"][0],n["integer_X_range"][1]}
        if t==LOW:
            direct_points.update([1049155,first_event-1,first_event])
        for x in sorted(direct_points):
            row=direct(x,data)
            current=[r for r in n["positive_intervals"] if r["first_X"]<=x<=r["last_X"]]
            assert len(current)<=1
            assert row["V_plus_whole"]==(current[0]["V_plus_whole"] if current else "0")
            checks.append(row)
    return {"scope":"Original positive coarse node form, strictly complete means all integer members of the underlying half-open node belong to the terminal integer set. The complete function is zero off the listed native intervals. No rescaling and no GCD truncation inside a node charge.",
            "X_range_inclusive":[1<<LOW,1<<HIGH],"strict_terminal_test":"q^100 > X^99, q <= X",
            "positive_source_signs":"Each actual nonzero label here is an ordinary prime (-1) or a product of two distinct rough primes (+1); (y+1)^3 exceeds the entire numerical range.",
            "native_slabs":native,"prior_y_fixed_controls":controls,"first_whole_cell_witness":first_witness,
            "exact_first_higher_layers_after_2_to_20":first_higher_layers(),
            "independent_per_X_clipped_vs_whole":checks,"numpy_version":np.__version__,
            "script_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=="__main__":
    result=main()
    Path(__file__).with_name("WHOLE_COARSE_SURPLUS.json").write_text(
        json.dumps(result,indent=2)+"\n",encoding="utf8")
    for r in result["native_slabs"]:
        print(r["integer_X_range"],r["y"],r["eligible_distinct_whole_cells"],r["positive_X_count"],r["maximum_positive_charge"])
