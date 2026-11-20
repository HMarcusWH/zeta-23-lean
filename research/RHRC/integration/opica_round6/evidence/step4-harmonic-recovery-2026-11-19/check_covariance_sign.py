"""Find and certify positive zero-center examples on the fixed terminal small-gcd sector."""
from fractions import Fraction
from hashlib import sha256
import json
from math import cos, exp, gcd, log, sin, sqrt
from pathlib import Path
from time import monotonic

from flint import arb, ctx, fmpz


def ball(z):
    s=z.str(29)
    assert arb(s).contains(z)
    return s


def first_eligible(x):
    # Strict terminal cutoff, including the case of an exact integer 100th root.
    r=int(fmpz(x**99).root(100))
    assert r**100<=x**99<(r+1)**100
    return r+1


def explore(x,source):
    # This inexpensive candidate screen carries no certificate or extremum claim.
    start=first_eligible(x)
    width=exp(-sqrt(log(x)))
    shells={}
    for q in range(start,x+1):
        if source[q]:
            g=int(log(x/q)/width)
            shells.setdefault(g,[]).append((q,source[q]/sqrt(q)))
    score=0.0
    for points in shells.values():
        for i,(r,b) in enumerate(points):
            for q,a in points[:i]:
                if gcd(q,r)!=1:
                    continue
                t=log(r/q)
                score+=4*a*b*sin(5*t)/t
    return score


def certify(x):
    ctx.prec=160
    start=first_eligible(x)
    log_x=arb(x).log()
    width=(-log_x.sqrt()).exp()
    cells={}
    bin_sites={}
    for q in range(start,x+1):
        t=(arb(x)/q).log()/width
        fi=t.floor().unique_fmpz()
        assert fi is not None
        i=int(fi)
        if q<x:
            assert i<t and t<i+1
        else:
            assert t.is_zero() and i==0
        bin_sites.setdefault(i,[]).append(q)
        mu=int(fmpz(q).moebius_mu())
        if mu and gcd(q,6)==1:
            cells.setdefault(i,[]).append((q,mu))
    complete=positive=negative=absolute=flat=arb(0)
    pairs=0
    details={}
    for g,labels in sorted(cells.items()):
        subtotal=arb(0)
        local=0
        for i,(r,mr) in enumerate(labels):
            for q,mq in labels[:i]:
                d=gcd(q,r)
                assert (d==1)==(d**100<x)
                if d**100>=x:
                    continue
                t=(arb(r)/q).log()
                assert 0<t and t<width
                coeff=4*mr*mq/arb(r*q).sqrt()
                term=coeff*(5*t).sin()/t
                subtotal+=term
                absolute+=abs(term)
                flat+=5*coeff
                if term>0:
                    positive+=term
                else:
                    assert term<0
                    negative-=term
                local+=1
        pairs+=local
        complete+=subtotal
        details[str(g)]=dict(first_integer=bin_sites[g][0],last_integer=bin_sites[g][-1],
            positive_labels=[q for q,m in labels if m>0],
            negative_labels=[q for q,m in labels if m<0],
            all_pairs=len(labels)*(len(labels)-1)//2,retained_unordered_pairs=local,signed=ball(subtotal))
    assert complete>0 and (positive-negative).overlaps(complete) and (positive+negative).overlaps(absolute)
    flat_error=arb(0)
    for labels in cells.values():
        for i,(r,mr) in enumerate(labels):
            for q,mq in labels[:i]:
                if gcd(q,r)!=1:
                    continue
                # |sin(z)/z-1|<=z²/6 and log(r/q)<=r/q-1.
                flat_error+=20/arb(r*q).sqrt()*25*as_arb(Fraction((r-q)**2,q*q))/6
    assert abs(complete-flat)<flat_error
    return dict(X=x,terminal_first_integer=start,log_bin_width=ball(width),active_labels=sum(map(len,cells.values())),
        retained_unordered_pairs=pairs,terminal_bins=details,signed_covariance_C0=ball(complete),
        positive_pair_mass=ball(positive),negative_pair_magnitude=ball(negative),absolute_integrated_pair_mass=ball(absolute),
        independent_flat_kernel=ball(flat),certified_flat_kernel_error=ball(flat_error),
        flat_kernel_lower_is_also_positive=bool(flat-flat_error>0))


def as_arb(r):
    return arb(r.numerator)/r.denominator


def main():
    t0=monotonic()
    ranges=[(1024,4096),(8193,10000)]
    source=[int(fmpz(q).moebius_mu()) if q>=1 and gcd(q,6)==1 else 0 for q in range(10001)]
    answers=[]
    for lo,hi in ranges:
        # Test the prescribed range with stride 7; report certified examples only.
        for k,x in enumerate(range(lo,hi+1,7),1):
            if explore(x,source)>1/100:
                result=certify(x)
                result["candidate_screens_in_range"]=k
                answers.append(result)
                break
        else:
            raise AssertionError(f"No positive candidate in range {lo}..{hi}")
    data=dict(status="COUNTEREXAMPLES_TO_ALWAYS_NONPOSITIVE_ZERO_CENTER",H=5,center=0,theta="1/100",
        criterion="Strict q^100 > X^99; unique floor of log(X/q)/exp(-sqrt(log X)); same bin and gcd(q,r)^100<X, q<r. Each unordered pair includes its conjugate multiplicity; no diagonal.",
        search="Bounded stride-seven exploratory double-precision screen with exact source sign and terminal endpoints. Positive candidates are independently fully recomputed with certified bins and Arb. No assertion of earliest or extremal examples.",
        search_ranges=ranges,examples=answers,precision_bits=ctx.prec,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=round(monotonic()-t0,2))
    Path(__file__).with_name("COVARIANCE_SIGN_CONTROL.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    for r in answers:
        print({k:r[k] for k in ("X","active_labels","retained_unordered_pairs","signed_covariance_C0","certified_flat_kernel_error","flat_kernel_lower_is_also_positive")})


if __name__=="__main__":
    main()
