"""Exact native rational pair covariance, with verification by complete squared moments."""
from collections import Counter
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
from time import monotonic

import flint
from flint import fmpq, fmpz


SCALE = 10**28


def balanced_sum(xs):
    xs = list(xs)
    while len(xs)>1:
        ys = [xs[i]+xs[i+1] for i in range(0,len(xs)-1,2)]
        if len(xs)%2:
            ys.append(xs[-1])
        xs = ys
    return xs[0] if xs else fmpq(0)


def rational_summary(x):
    p,q = int(x.p),int(x.q)
    descriptor = bytearray([int(p<0)])
    for v in (abs(p),q):
        raw=v.to_bytes(max(1,(v.bit_length()+7)//8),"big")
        descriptor.extend(len(raw).to_bytes(8,"big"))
        descriptor.extend(raw)
    data = dict(sha256=sha256(descriptor).hexdigest(),numerator_bits=abs(p).bit_length(),
                denominator_bits=q.bit_length(),
                outward_base10_scaled=[str((x*SCALE).floor()),str((x*SCALE).ceil())])
    if max(abs(p).bit_length(),q.bit_length())<=512:
        data["exact"]=str(x)
    return data


def count_sum(counts,scale):
    return balanced_sum(fmpq(scale*c,d) for d,c in counts.items() if c)


def evaluate(x,powers=16):
    t=(x-1).bit_length()
    s=isqrt(t)
    s+=int(s*s!=t)
    start=int(fmpz(x**99).root(100))+1
    assert (start-1)**100<=x**99<start**100
    assert (s-1)**2<t<=s*s and (1<<(t-1))<x<=1<<t
    lattice={}
    for q in range(start,x+1):
        k=q.bit_length()-1
        w=1<<max(0,k-s)
        Q=(q//w+1)*w
        assert (1<<k)<=q<(1<<(k+1)) and Q-w<=q<Q
        atom=lattice.setdefault((k,Q),dict(k=k,Q=Q,width=w,sites=[],atoms=[]))
        atom["sites"].append(q)
        sign=int(fmpz(q).moebius_mu()) if gcd(q,6)==1 else 0
        if sign:
            atom["atoms"].append((q,sign))
    sums={stat:[] for stat in ("diagonal","signed_retained","absolute_retained","signed_omitted","full_energy")}
    shells=[]
    for (k,Q),part in sorted(lattice.items()):
        ls=part["atoms"]
        nc=Counter()
        ac=Counter()
        omitted=Counter()
        dc=Counter()
        common_gcd=Counter()
        for i,(r,mr) in enumerate(ls):
            dc[Q*Q-2*(Q-r)**2]+=1
            for q,mq in ls[:i]:
                d=gcd(q,r)
                common_gcd[d]+=1
                den=Q*Q-2*(Q-q)*(Q-r)
                assert den>0 and (d**100<x)==(d==1)
                if d**100<x:
                    nc[den]+=mq*mr
                    ac[den]+=1
                else:
                    omitted[den]+=mq*mr
        di=count_sum(dc,Q)
        retained=count_sum(nc,2*Q)
        abs_retained=count_sum(ac,2*Q)
        extra=count_sum(omitted,2*Q)
        full=di+retained+extra
        assert sum(dc.values())==len(ls)
        assert len(ls)*(len(ls)-1)//2==sum(common_gcd.values())
        # For the unrestricted full form, geometric expansion term j equals
        # 2^j/Q^(2j+1) times the square of the true integer signed moment.
        moments=[sum(m*(Q-q)**j for q,m in ls) for j in range(powers+1)]
        partial=balanced_sum(fmpq((1<<j)*v*v,Q**(2*j+1)) for j,v in enumerate(moments))
        A=max((Q-q for q,_ in ls),default=0)
        z=fmpq(2*A*A,Q*Q)
        assert 0<=z<1
        tail=fmpq(len(ls)**2,Q)*z**(powers+1)/(1-z)
        assert partial<=full<=partial+tail
        for stat,v in zip(sums,(di,retained,abs_retained,extra,full)):
            sums[stat].append(v)
        shells.append(dict(k=k,Q=Q,width=part["width"],
            integer_cut=[min(part["sites"]),max(part["sites"])],active=len(ls),
            positive_labels=[q for q,m in ls if m>0],negative_labels=[q for q,m in ls if m<0],
            all_unordered_pairs=sum(common_gcd.values()),retained_unordered_pairs=common_gcd[1],gcd_counts=dict(common_gcd),
            diagonal=rational_summary(di),signed_retained=rational_summary(retained),
            absolute_retained=rational_summary(abs_retained),signed_omitted=rational_summary(extra),
            full_bin_energy=rational_summary(full),integer_moments=[str(v) for v in moments],
            moment_partial=rational_summary(partial),majorant_ratio=str(z),
            rigorously_positive_or_zero_remainder=True,geometric_tail_upper=rational_summary(tail)))
    summary={stat:rational_summary(balanced_sum(values)) for stat,values in sums.items()}
    return dict(X=x,terminal_first=start,s=s,ceil_log2=t,
        active=sum(a["active"] for a in shells),same_bin_pairs=sum(a["all_unordered_pairs"] for a in shells),
        retained_pairs=sum(a["retained_unordered_pairs"] for a in shells),bins=shells,aggregates=summary)


def run():
    ts=monotonic()
    xs=[1045,2048,8494]
    rows=[evaluate(x) for x in xs]
    signs=[int(r["aggregates"]["signed_retained"]["outward_base10_scaled"][0]) for r in rows]
    if not any(n>0 for n in signs) or not any(n<0 for n in signs):
        for x in range(1024,1537):
            if x in xs:
                continue
            r=evaluate(x)
            value=int(r["aggregates"]["signed_retained"]["outward_base10_scaled"][0])
            if (value>0 and max(signs)<=0) or (value<0 and min(signs)>=0):
                rows.append(r)
                signs.append(value)
                if min(signs)<0<max(signs):
                    break
    assert min(signs)<0<max(signs)
    data=dict(status="EXACT_RATIONAL_NATIVE_PAIR_CONTROL",evaluations=rows,
        source_rule="q^100>X^99, q<=X, mu6(q)=mu(q)1_(q,6)=1; group by (k,Q), k=floor(log2(q)), w=2^max(0,k-s), Q=(floor(q/w)+1)w.",
        covariance_rule="Off-diagonal twice-oriented exact weight 2*mu6(q)*mu6(r)*Q/[Q²-2*(Q-q)*(Q-r)], small gcd iff gcd(q,r)^100<X. The diagonal uses its single unrepeated weight.",
        complete_bin_psd_check="Unrestricted true-bin energy was expanded through signed squared integer moments of orders 0..16. The positive tail is bounded by n_atoms²/Q times z^17/(1-z), where z=2*max(Q-q)^2/Q². Both comparisons are exact rational inequalities.",
        scale_for_outward_intervals=str(SCALE),
        rational_digest_encoding="Canonical reduced numerator/denominator. One sign byte (0 nonnegative or 1 negative), then for |numerator| and positive denominator: eight-byte unsigned big-endian byte count, followed by unsigned big-endian magnitude (at least one byte).",
        flint_version=flint.__version__,source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=round(monotonic()-ts,2),scope="Finite controls at specified cutoffs. Full-bin PSD applies before the distinct-label and small-gcd restriction.")
    Path(__file__).with_name("RATIONAL_PAIR_CHECK.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    for r in rows:
        print(r["X"],r["active"],r["retained_pairs"],[(k,v["outward_base10_scaled"]) for k,v in r["aggregates"].items()])


if __name__=="__main__":
    run()
