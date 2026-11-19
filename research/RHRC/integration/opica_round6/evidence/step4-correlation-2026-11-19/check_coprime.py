"""Check marked and coprime coefficient identities over a formal prime-log basis."""
import hashlib
import json
from collections import Counter
from math import gcd
from pathlib import Path


def add(dst, src, mul):
    for k, v in src.items():
        dst[k] += v*mul


def cleaned(c):
    return {k: v for k, v in c.items() if v}


def factors(n):
    d=2
    f={}
    while d*d<=n:
        while n%d==0:
            f[d]=f.get(d,0)+1
            n//=d
        d+=1
    if n>1:
        f[n]=f.get(n,0)+1
    return f


def tensor(a,b):
    return {(k,l):v*w for k,v in a.items() for l,w in b.items()}


def check(limit, y):
    fact=[{}]+[factors(k) for k in range(1,limit+1)]
    mu=[0]+[(-1)**len(f) if all(ex==1 for ex in f.values()) else 0 for f in fact[1:]]
    ds=[[]]+[[d for d in range(1,k+1) if k%d==0] for k in range(1,limit+1)]
    lam=[{next(iter(f)):1} if len(f)==1 else {} for f in fact]
    rows={}
    marks={}
    marked_count=0
    coprime_checks=0
    record=hashlib.sha256()
    for k in range(1,limit+1):
        rows[k]={}
        for d in ds[k]:
            if not mu[d]:
                continue
            r=1
            for p in fact[d]:
                if p>y:
                    r*=p
            add(rows[k].setdefault(r,Counter()),fact[k//d],mu[d])
        rows[k]={r:cleaned(v) for r,v in rows[k].items() if cleaned(v)}
        marks[k]={}
        for r,v in rows[k].items():
            for u in ds[r]:
                add(marks[k].setdefault(u,Counter()),v,1)
        assert cleaned(marks[k].get(1,{}))==lam[k]
        for u in ds[k]:
            if not mu[u] or any(p<=y for p in fact[u]):
                continue
            via=Counter()
            for b in ds[k//u]:
                if set(fact[b])<=set(fact[u]):
                    add(via,lam[k//(u*b)],mu[u])
            expect=cleaned(via)
            assert cleaned(marks[k].get(u,{}))==expect
            record.update(repr((k,u,sorted(expect.items()))).encode())
            marked_count+=1
    for k in range(1,limit+1):
        for l in range(1,limit+1):
            lhs=Counter()
            rhs=Counter()
            for r,v in rows[k].items():
                for s,w in rows[l].items():
                    if gcd(r,s)==1:
                        add(lhs,tensor(v,w),1)
            for u in marks[k].keys() & marks[l].keys():
                add(rhs,tensor(marks[k][u],marks[l][u]),mu[u])
            assert cleaned(lhs)==cleaned(rhs)
            coprime_checks+=1
    return {"y":y,"integer_indices":limit,"marked_linear_checks":marked_count,
            "ordered_coprime_bilinear_checks":coprime_checks,
            "coefficient_stream_sha256":record.hexdigest()}


if __name__=="__main__":
    out=[check(150,y) for y in (2,5,11)]
    txt=json.dumps({"cases":out,"basis":"formal ordered products of prime logarithms",
          "scope":"Finite arithmetic coefficients in the exact identities. The continuum norm estimate is a paper inequality."},indent=2)+"\n"
    Path(__file__).with_name("COPRIME_CHECK.json").write_text(txt,encoding="utf-8")
    print(txt)
