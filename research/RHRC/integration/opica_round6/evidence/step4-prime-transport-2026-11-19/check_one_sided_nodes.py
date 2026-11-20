"""Actual positive/negative node energies and sign-restricted prime minors."""
from bisect import bisect_left
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations_with_replacement
from math import isqrt
from pathlib import Path
import json

from check_two_probes import X, make_labels


HERE = Path(__file__).resolve().parent


def compute(first, data, coarse):
    labels = sorted(data)
    pref_f, pref_p = [0], [0]
    for n in labels:
        f,p,_ = data[n]
        pref_f.append(pref_f[-1]+f)
        pref_p.append(pref_p[-1]+p)
    top = X.bit_length()-1
    s = 1+isqrt(top-1)
    shift = 2*top-s
    den = 1<<shift
    depths = []
    by_sign = {sg: Counter() for sg in (-1,0,1)}
    p_energy = fp = 0
    for j in range(first.bit_length()-1,top+1):
        lo,hi=max(first,1<<j),min(X+1,1<<(j+1))
        d=max(0,j-s)
        for k in range(d+1):
            if coarse and 2*k>=d:
                continue
            width,w=1<<(d-k),1<<(shift-j-k)
            charges = Counter()
            for idx in range(lo//width,(hi-1)//width+1):
                a=bisect_left(labels,max(lo,idx*width))
                b=bisect_left(labels,min(hi,(idx+1)*width))
                f,p=pref_f[b]-pref_f[a],pref_p[b]-pref_p[a]
                charges[(f,p)]+=1
                sg=(f>0)-(f<0)
                stats=by_sign[sg]
                stats["nodes"]+=1
                stats["occupied_nodes"]+=int(b>a)
                stats["sum_charges_counting_all_depths"]+=f
                stats["energy"]+=w*f*f
                p_energy+=w*p*p
                fp+=w*f*p
            depths.append((1<<d,width,w,charges))
    pair_stats={}
    for width_kind in ("cheap","remaining"):
        for pole in ("opposite_or_zero","same_nonzero"):
            pair_stats[width_kind,pole]=Counter()
    for it,(base,h,w,charges) in enumerate(depths):
        for jt in range(it,len(depths)):
            otherbase,g,v,ocharges=depths[jt]
            same=it==jt
            width_kind="cheap" if (h*g)**2<=X*base*otherbase else "remaining"
            stream=(combinations_with_replacement(charges.items(),2) if same else
                    ((s,t) for s in charges.items() for t in ocharges.items()))
            for ((f,p),ni),((e,r),nj) in stream:
                multiplicity=ni*(ni-1)//2 if same and (f,p)==(e,r) else ni*nj
                if multiplicity==0:
                    continue
                vals=pair_stats[width_kind,"opposite_or_zero" if f*e<=0 else "same_nonzero"]
                vals["unordered_distinct_node_pairs"]+=multiplicity
                minor=(p*e-r*f)**2
                vals["nonzero_squared_minor_pairs"]+=multiplicity*bool(minor)
                vals["area"]+=w*v*multiplicity*minor
    total_nodes=sum(sg["nodes"] for sg in by_sign.values())
    assert sum(v["unordered_distinct_node_pairs"] for v in pair_stats.values())==total_nodes*(total_nodes-1)//2
    total=sum(sg["energy"] for sg in by_sign.values())
    det=p_energy*total-fp*fp
    assert sum(val["area"] for val in pair_stats.values())==det
    opp=sum(val["area"] for (width_kind,pole),val in pair_stats.items() if pole=="opposite_or_zero")
    lower=p_energy*min(by_sign[-1]["energy"],by_sign[1]["energy"])
    assert opp>=lower
    def exact(v,scale=den):
        return str(Fraction(v,scale))
    statistics={}
    for sg,name in ((1,"positive"),(-1,"negative"),(0,"zero")):
        vals=by_sign[sg]
        statistics[name]={key:vals[key] for key in ("nodes","occupied_nodes","sum_charges_counting_all_depths")}
        statistics[name]["energy"]=exact(vals["energy"])
    return {"node_set":"2*k<d" if coarse else "all depths",
            "intersecting_nodes":total_nodes,"per_sign":statistics,"V_plus":exact(by_sign[1]["energy"]),
            "V_minus":exact(by_sign[-1]["energy"]),"total_F_norm_squared":exact(total),
            "total_P_norm_squared":exact(p_energy),"full_prime_wedge_squared":exact(det,den**2),
            "sign_restricted_prime_wedge_squared":exact(opp,den**2),
            "verified_lower_P_squared_min_V":exact(lower,den**2),
            "node_pair_partition":[{"width":wk,"polarity":sg,
                                    "unordered_distinct_node_pairs":v["unordered_distinct_node_pairs"],
                                    "nonzero_squared_minor_pairs":v["nonzero_squared_minor_pairs"],
                                    "prime_wedge_squared":exact(v["area"],den**2)}
                                   for (wk,sg),v in pair_stats.items()]}


def independent_coarse_energy(first,data):
    # Direct independent enumeration of source LABEL pairs with common eligible
    # ancestors via xor, as opposed to moments of charges on NODE pairs.
    top=X.bit_length()-1
    s=1+isqrt(top-1)
    shift=2*top-s
    buckets={}
    for n,(f,_,_) in data.items():
        j=n.bit_length()-1
        d=max(0,j-s)
        buckets.setdefault((j,d,n>>d),[]).append((n,f))
    numerator=0
    for (j,d,_),rows in buckets.items():
        levels=(d+1)//2
        if not levels:
            continue
        full=1<<(shift-j+1)
        numerator+=len(rows)*(full-(full>>levels))
        for i,(n,f) in enumerate(rows):
            for r,e in rows[:i]:
                num_common=min(levels,d+1-(n^r).bit_length())
                numerator+=2*f*e*(full-(full>>num_common))
    return str(Fraction(numerator,1<<shift))


if __name__=="__main__":
    first,y,data=make_labels()
    full=compute(first,data,False)
    coarse=compute(first,data,True)
    prior_rough=HERE/"ROUGH_TREE_CHECK.json"
    prior_gram=HERE/"TWO_PROBE_CHECK.json"
    reference=next(row for row in json.loads(prior_rough.read_text())["cases"] if row["X"]==X)
    reference_energy=reference["results"]["rough"]["total_positive_energy"]
    assert reference_energy==full["total_F_norm_squared"]
    previous=json.loads(prior_gram.read_text())["cases"][0]
    assert previous["squared_wedges"]["P_F"]==full["full_prime_wedge_squared"]
    independent=independent_coarse_energy(first,data)
    assert coarse["total_F_norm_squared"]==independent
    result={"X":X,"first_terminal":first,"roughness":y,"actual_label_signs":dict(Counter(v[0] for v in data.values())),
            "vectors":"f=complete squarefree y-rough Mobius signs; p=-1 on the actual ordinary primes and 0 otherwise",
            "scope":"Positive original node form, before mask or diagonal subtraction. No whole terminal shell at this finite X.",
            "full":full,"coarse":coarse,"independent_checks":{"full_prior_energy":reference_energy,
            "coarse_direct_sum_over_all_coarse_common_ancestors_of_true_signed_label_pairs":independent,
            "full_prime_wedge_matches_previous":True},
            "sha256":{p.name:sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),HERE/"check_two_probes.py",prior_rough,prior_gram)}}
    (HERE/"ONE_SIDED_NODE_CHECK.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print("full",full["V_plus"],full["V_minus"])
    print("coarse",coarse["V_plus"],coarse["V_minus"])
