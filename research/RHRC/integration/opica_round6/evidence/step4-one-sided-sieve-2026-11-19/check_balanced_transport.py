"""Hierarchical matching of actual positive balanced semiprimes to negative primes."""
from array import array
from bisect import bisect_left
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt
import json
from pathlib import Path


CASES=(131093,221189,1656575)


def make_spf(limit):
    spf=array("I",range(limit+1))
    for p in range(2,isqrt(limit)+1):
        if spf[p]==p:
            for n in range(p*p,limit+1,p):
                if spf[n]==n:
                    spf[n]=p
    return spf


def factors(spf,n):
    fs=[]
    while n>1:
        fs.append(spf[n])
        n//=spf[n]
    return fs


def extract(x,spf):
    lo,hi=0,x
    target=x**99
    while hi-lo>1:
        m=(hi+lo)//2
        if m**100>target:
            hi=m
        else:
            lo=m
    first=hi
    y=(x-1).bit_length()**2
    signs={}
    primes=set()
    targets=set()
    audit=Counter()
    for n in range(first,x+1):
        fs=factors(spf,n)
        if min(fs)<=y:
            continue
        if len(set(fs))!=len(fs):
            audit["rough_nonsquarefree"]+=1
            continue
        signs[n]=(-1)**len(fs)
        audit["rough_squarefree_degree_"+str(len(fs))]+=1
        if len(fs)==1:
            primes.add(n)
        if len(fs)==2 and 16*fs[0]*fs[0]>9*x and 16*fs[1]*fs[1]>9*x:
            targets.add(n)
    return first,y,signs,targets,primes,dict(audit)


def match(x,s,targets,primes):
    left,right=set(targets),set(primes)
    paired=[]
    stage=Counter()
    for logh in range(max(0,x.bit_length()-1-s)+1):
        groups=defaultdict(list)
        supply=defaultdict(list)
        for n in sorted(left):
            j=n.bit_length()-1
            if logh<=max(0,j-s):
                groups[j,n>>logh].append(n)
        for n in sorted(right):
            key=(n.bit_length()-1,n>>logh)
            if key in groups:
                supply[key].append(n)
        for key,group in groups.items():
            for a,b in zip(group,supply[key]):
                left.remove(a)
                right.remove(b)
                paired.append((a,b))
                stage[str(1<<logh)]+=1
    return paired,left,right,dict(stage)


def exact(n,shift):
    return str(Fraction(n,1<<shift))


def audit_transport(x,s,signs,targets,primes,paired,first):
    top=x.bit_length()-1
    shift=top+max(0,top-s)
    buckets=defaultdict(list)
    charges=defaultdict(lambda:[0,0,0,0])
    # Coordinates are the complete field F, all targets minus matched donors T-D,
    # matched targets minus matched donors E, and the true complement F-(T-D).
    mt={a for a,b in paired}
    donor={b for a,b in paired}
    assert len(mt)==len(donor)==len(paired) and mt<=targets and donor<=primes
    removed=targets|donor
    for n,sg in signs.items():
        j=n.bit_length()-1
        d=max(0,j-s)
        buckets[j,n>>d].append(n)
        v=(sg,sg if n in removed else 0,sg if n in mt or n in donor else 0,
           0 if n in removed else sg)
        for k in range(d+1):
            row=charges[j,k,n>>(d-k)]
            for i in range(4):
                row[i]+=v[i]
    norms=[0]*4
    dot=0
    dot_retired=0
    for (j,k,index),v in charges.items():
        assert v[0]==v[1]+v[3]
        w=1<<(shift-j-k)
        for i in range(4):
            norms[i]+=w*v[i]*v[i]
        dot+=w*v[1]*v[3]
        dot_retired+=w*v[1]*v[0]
    assert norms[0]-norms[3]==norms[1]+2*dot==2*dot_retired-norms[1]

    # Independent direct ordered-pair reconstruction using integer XOR for the
    # common ancestors; include every edge incident to removed labels.
    e_squared=0
    m_squared=0
    diag=0
    incident=0
    kept=0
    failed=Counter()
    cap=1
    assert 1<x<=2**100
    for n in sorted(removed):
        j=n.bit_length()-1
        d=max(0,j-s)
        full=1<<(shift-j+1)
        nd=full-(full>>(d+1))
        e_squared+=nd
        if n in mt or n in donor:
            m_squared+=nd
        diag+=nd
        for r in buckets[j,n>>d]:
            if r==n or (r in removed and r<n):
                continue
            levels=d+1-(n^r).bit_length()
            assert levels>=1
            val=2*signs[n]*signs[r]*(full-(full>>levels))
            incident+=val
            if r in removed:
                e_squared+=val
                if (n in mt or n in donor) and (r in mt or r in donor):
                    m_squared+=val
            if gcd(n,r)<=cap:
                kept+=val
            else:
                failed["pairs"]+=1
                failed["signed"]+=val
    assert e_squared==norms[1] and m_squared==norms[2]
    assert incident+diag==norms[0]-norms[3]
    assert incident-kept==failed["signed"]
    def base(n):
        j=n.bit_length()-1
        return j,n>>max(0,j-s)
    bleft,bright=base(first),base(x)
    remainder=sorted(targets-mt)
    cells=[]
    for name,key in (("first",bleft),("last",bright)):
        j,idx=key
        h=1<<max(0,j-s)
        l,r=idx*h,(idx+1)*h
        rows=buckets[key]
        cells.append({"which":name,"underlying":[l,r],"clipped":[max(first,l),min(x+1,r)],
                      "actual_target_count":sum(n in targets for n in rows),
                      "actual_donor_pool_count":sum(n in primes for n in rows),
                      "unmatched_targets":[n for n in remainder if base(n)==key]})
    displacement=[abs(a-b) for a,b in paired]
    return {"matches":len(paired),"matched_base_crossings":sum(base(a)!=base(b) for a,b in paired),
            "matched_shell_crossings":sum(a.bit_length()!=b.bit_length() for a,b in paired),
            "unmatched_count":len(remainder),"unmatched_labels":remainder,
            "max_pair_displacement":max(displacement,default=0),"sum_pair_displacement":sum(displacement),
            "number_donors_below_target":sum(b<a for a,b in paired),"boundary_base_cells":cells,
            "norms_squared":{"F":exact(norms[0],shift),"all_targets_minus_selected_donors":exact(norms[1],shift),
                            "actually_matched_targets_minus_donors":exact(norms[2],shift),
                            "F_minus_all_targets_plus_selected_donors":exact(norms[3],shift)},
            "dot_of_all_targets_minus_donors_with_remainder":exact(dot,shift),
            "full_minus_remainder_norm_squared_difference":exact(norms[0]-norms[3],shift),
            "true_incident_ordered_off_diagonal":{"all":exact(incident,shift),"native_gcd_admitted":exact(kept,shift),
                                                 "native_gcd_rejected":exact(failed["signed"],shift),
                                                 "rejected_unordered_pairs":failed["pairs"],"diagonal":exact(diag,shift)},
            "all_pairing_sha256":sha256(json.dumps(paired,separators=(",",":")).encode()).hexdigest(),
            "exact_crosschecks":["node identity F=E+R at every node","both squared difference norms via direct signed source label pairs",
                                 "full-minus-remainder via every incident label pair, retaining the literal gcd and its complement"]}


def case(x,spf):
    first,y,signs,targets,primes,counts=extract(x,spf)
    s=isqrt(x.bit_length()-2)+1
    assert targets and primes
    paired,waiting,free,stages=match(x,s,targets,primes)
    local=audit_transport(x,s,signs,targets,primes,paired,first)
    assert local["matched_base_crossings"]==0
    # Explicit auxiliary comparison only: pay the entire unmatched boundary
    # debt with the closest unused prime inside the same terminal interval.
    extra=[]
    free=sorted(free)
    for n in sorted(waiting):
        i=bisect_left(free,n)
        inds=[k for k in (i-1,i) if 0<=k<len(free)]
        index=min(inds,key=lambda k:(abs(free[k]-n),free[k]))
        extra.append((n,free.pop(index)))
    resolved=audit_transport(x,s,signs,targets,primes,paired+extra,first) if extra else local
    assert resolved["unmatched_count"]==0
    return {"X":x,"first_terminal_integer":first,"roughness_y":y,"s":s,"all_source_degrees":counts,
            "balanced_semiprime_targets":len(targets),"actual_prime_pool":len(primes),
            "number_matched_by_dyadic_integer_width":stages,"base_local":local,
            "auxiliary_terminal_spill_pairs":[{"target":a,"factors":factors(spf,a),"donor":b} for a,b in extra],
            "after_terminal_spill":resolved if extra else "Identical to base_local; no spill.",
            "endpoint_control":"All tested targets and donors belong to the same actual native terminal interval. The auxiliary spill may cross bases or shells, which is measured explicitly."}


if __name__=="__main__":
    spf=make_spf(max(CASES))
    result={"scope":"Finite source/dyadic-tree transport check; fixed target cone p<q with 16p²>9X and 16q²>9X. True squarefree rough source, all tree depths; separate optional global matching step for terminal debt. No asymptotic cost or signed bound inferred.",
            "algorithm":"Increasing dyadic widths through the actual base; in each node pair remaining targets and prime donors in increasing label order. Any terminal spill selects nearest unused eligible prime, lower breaks ties.",
            "cases":[case(x,spf) for x in CASES],"script_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name("BALANCED_TRANSPORT_CHECK.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    for c in result["cases"]:
        v=c["base_local"]
        print(c["X"],c["balanced_semiprime_targets"],v["matches"],v["unmatched_labels"],v["norms_squared"])
