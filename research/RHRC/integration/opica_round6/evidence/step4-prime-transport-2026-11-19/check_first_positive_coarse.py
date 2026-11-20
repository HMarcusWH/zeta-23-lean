"""Find the first positive native coarse charge immediately above 2^20."""
from array import array
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path


X0 = 1 << 20
LIMIT = X0 + 2048


def sieve():
    least = array("I",range(LIMIT+1))
    for p in range(2,isqrt(LIMIT)+1):
        if least[p] != p:
            continue
        for n in range(p*p,LIMIT+1,p):
            if least[n] == n:
                least[n] = p
    return least


def facts(least,n):
    out=[]
    while n>1:
        p=least[n]
        out.append(p)
        n//=p
    return out


def label(factors,y):
    return ((-1)**len(factors) if factors and min(factors)>y and
            len(set(factors))==len(factors) else 0)


def first_terminal(x):
    low,high=0,x
    target=x**99
    while high-low>1:
        m=(low+high)//2
        if m**100<=target:
            low=m
        else:
            high=m
    return high


def all_coarse(first,x,prefix,offset):
    top=x.bit_length()-1
    s=isqrt(top-1)+1
    counts=Counter()
    hits=[]
    v_plus=Fraction(0)
    for j in range(first.bit_length()-1,top+1):
        d=max(0,j-s)
        a,b=max(first,1<<j),min(x+1,1<<(j+1))
        for k in range((d+1)//2):
            width=1<<(d-k)
            for idx in range(a//width,(b-1)//width+1):
                l,r=max(a,idx*width),min(b,(idx+1)*width)
                f=prefix[r-offset]-prefix[l-offset]
                counts[(f>0)-(f<0)]+=1
                if f>0:
                    hits.append((j,k,idx,width,l,r,f))
                    v_plus+=Fraction(f*f,1<<(j+k))
    return counts,hits,v_plus


if __name__=="__main__":
    least=sieve()
    origin=first_terminal(X0)
    prefix={400:[0],441:[0]}
    for n in range(origin,LIMIT+1):
        fs=facts(least,n)
        for y,z in prefix.items():
            z.append(z[-1]+label(fs,y))
    first=origin
    base_counts,_,base_plus=all_coarse(first,X0,prefix[400],origin)
    assert base_plus==0
    for x in range(X0+1,LIMIT+1):
        y=(x-1).bit_length()**2
        assert y==441
        target=x**99
        while first**100<=target:
            first+=1
        assert (first-1)**100<=target<first**100
        counts,hits,v_plus=all_coarse(first,x,prefix[y],origin)
        if hits:
            break
    else:
        raise ValueError("No positive cutoff in scan")
    j,k,idx,width,l,r,f=min(hits,key=lambda row:row[5]-row[4])
    labels=[{"n":n,"prime_factors":facts(least,n),"mu_y":label(facts(least,n),y)}
            for n in range(l,r)]
    assert sum(row["mu_y"] for row in labels)==f
    prev_first=first_terminal(x-1)
    _,prev_hits,prev_plus=all_coarse(prev_first,x-1,prefix[y],origin)
    assert not prev_hits and prev_plus==0
    leaving=[{"n":n,"prime_factors":facts(least,n),"mu_y":label(facts(least,n),y)}
             for n in range(prev_first,first)]
    clipped_hash=sha256(json.dumps(labels,sort_keys=True,separators=(",",":")).encode("ascii")).hexdigest()
    result={
        "scope":"Every intersecting native coarse node at every integer from 2^20 through the first positive V_plus, with strict moving terminal bound. Integer sieve, all labels factorized in the witness. No asymptotic inference.",
        "baseline":{"X":X0,"y":400,"counts_negative_zero_positive":[base_counts[a] for a in [-1,0,1]],"V_plus":str(base_plus)},
        "first_positive_X":x,"offset_from_2_to_20":x-X0,"roughness_y":y,"first_terminal":first,
        "consecutive_preceding_integer_cutoffs_with_zero_V_plus_including_baseline":x-X0,
        "all_coarse":{"counts_negative_zero_positive":[counts[a] for a in [-1,0,1]],"V_plus":str(v_plus)},
        "previous_cutoff":{"X":x-1,"first_terminal":prev_first,"V_plus":str(prev_plus),
                           "labels_leaving_through_lower_boundary":leaving},
        "all_positive_coordinates":[{"j":jj,"k":kk,"node_index":ii,"clipped_range":[ll,rr],"charge":ff}
                                    for jj,kk,ii,ww,ll,rr,ff in hits],
        "witness":{"j":j,"k":k,"base_depth_d":j-5,"s":5,"coarse":2*k<j-5,"grid_index":idx,
                   "underlying_half_open_integer_range":[idx*width,(idx+1)*width],
                   "clipped_half_open_integer_range":[l,r],"charge":f,"weight":str(Fraction(1,1<<(j+k))),
                   "positive_energy_contribution":str(Fraction(f*f,1<<(j+k))),
                   "nonzero_labels":[a for a in labels if a["mu_y"]],
                   "label_count_including_zero":len(labels),"all_label_factorizations_sha256":clipped_hash},
        "script_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name("FIRST_POSITIVE_COARSE.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print(x,first,counts,v_plus,(j,k,idx,width,l,r,f))
