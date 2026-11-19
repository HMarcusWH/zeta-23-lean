"""Complete fixed-band arithmetic covariance and independent rigorous real-axis quadrature."""
from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, gcd
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx, fmpz


def as_arb(r):
    return arb(r.numerator)/r.denominator


def ball(v):
    s = v.str(29)
    assert arb(s).contains(v)
    return s


def rational_quadrature_weights(p):
    # Integrate degree p-1 Lagrange basis polynomials on [0,1] exactly.
    nodes = [Fraction(i,p-1) for i in range(p)]
    weights=[]
    for x in nodes:
        coefficients=[Fraction(1)]
        denominator=Fraction(1)
        for y in nodes:
            if y==x:
                continue
            new=[Fraction(0) for _ in range(len(coefficients)+1)]
            for k,c in enumerate(coefficients):
                new[k]-=y*c
                new[k+1]+=c
            coefficients=new
            denominator*=x-y
        weights.append(sum((v/(k+1) for k,v in enumerate(coefficients)),Fraction())/denominator)
    for degree in range(p):
        assert sum((w*t**degree for w,t in zip(weights,nodes)),Fraction())==Fraction(1,degree+1)
    return weights


def quadrature(source,lo,hi,cutoff):
    p,panels=16,256
    weights=list(map(as_arb,rational_quadrature_weights(p)))
    delta=arb(hi-lo)/panels
    stride=delta/(p-1)
    total=arb(0)
    previous=None
    for panel in range(panels):
        for i,w in enumerate(weights):
            if i==0 and previous is not None:
                value=previous
            else:
                t=lo+(panel*(p-1)+i)*stride
                re,im=arb(0),arb(0)
                for _,a,logq in source:
                    sn,cs=(t*logq).sin_cos()
                    re+=a*cs
                    im-=a*sn
                value=re**2+im**2
            total+=w*delta*value
        previous=value
    l1=sum((abs(a) for _,a,_ in source),arb(0))
    # Multiply D(t) by exp(i*t*log(X)/2), preserving |D|. Each resulting
    # frequency has modulus at most log(X)/2. The Leibniz rule bounds the
    # p-th derivative of |D|^2 by l1^2*log(X)^p. Apply the real interpolation
    # remainder and bound the nodal product by delta^p on its own panel.
    err=(hi-lo)*l1**2*(delta*arb(cutoff).log())**p/factorial(p)
    return total+arb(0,err.upper()),err,dict(polynomial_degree=p-1,panels=panels,
        distinct_grid_samples=panels*(p-1)+1,raw_sum=ball(total),analytic_remainder_upper=ball(err))


def main():
    start=monotonic()
    ctx.prec=128
    X,H=2048,5
    centers=(0,14,25)
    labels=[(q,int(fmpz(q).moebius_mu())) for q in range(1,X+1) if gcd(q,6)==1]
    source=[(q,arb(mu)/arb(q).sqrt(),arb(q).log()) for q,mu in labels if mu]
    diag_exact=2*H*sum((Fraction(1,q) for q,_,_ in source),Fraction())
    diag=as_arb(diag_exact)
    cross=[arb(0) for _ in centers]
    terms_abs=[arb(0) for _ in centers]
    pos=[0 for _ in centers]
    neg=[0 for _ in centers]
    for i,(_,aq,lgq) in enumerate(source):
        for _,ap,lgp in source[:i]:
            u=lgq-lgp
            assert u>0
            common=4*ap*aq*(H*u).sin()/u
            for k,j in enumerate(centers):
                term=common if j==0 else common*(j*u).cos()
                cross[k]+=term
                terms_abs[k]+=abs(term)
                if term>0:
                    pos[k]+=1
                else:
                    assert term<0
                    neg[k]+=1
    expected=len(source)*(len(source)-1)//2
    results={}
    for i,j in enumerate(centers):
        assert pos[i]+neg[i]==expected and diag+cross[i]>0
        results[str(j)] = dict(band=[j-H,j+H],diagonal=ball(diag),signed_cross=ball(cross[i]),
            absolute_cross=ball(terms_abs[i]),energy=ball(diag+cross[i]),positive_cross_pairs=pos[i],
            negative_cross_pairs=neg[i])
    direct,err,details=quadrature(source,14-H,14+H,X)
    assert direct.overlaps(diag+cross[1]) and direct.contains(diag+cross[1])
    assert err<arb(1)/10**14
    details["certified_direct_integral"]=ball(direct)
    details["band"]=[9,19]
    details["reason"]="Integrate the original |D(t)|^2 directly. Exact rational polynomial weights are checked against every monomial through degree 15. Remainder <= (2H)*(sum|a_q|)^2*(panel_width*log(X))^16/16!."
    data=dict(status="FINITE_COMPLETE_SIGNED_COVARIANCE",X=X,half_width_H=H,centers=list(centers),
        coprime_to_six_labels=len(labels),nonzero_labels=len(source),positive_labels=sum(mu>0 for _,mu in labels),
        negative_labels=sum(mu<0 for _,mu in labels),zero_labels=sum(mu==0 for _,mu in labels),
        unordered_cross_pairs_per_center=expected,ordered_cross_terms_per_center=2*expected,
        exact_diagonal_rational_sha256=sha256(str(diag_exact).encode("ascii")).hexdigest(),
        rational_diagonal_rule="2H times the exact sum of 1/q over 1<=q<=X with (q,6)=1 and mu(q) nonzero; includes q=1.",
        signed_cross_rule="Each p<q denotes two ordered integer labels, contributing 4 mu6(p)mu6(q) cos(j*log(q/p))*sin(H*log(q/p))/(sqrt(pq)*log(q/p)).",
        absolute_cross_rule="Sum of the absolute values of these integrated paired contributions, taken after each conjugate pair is combined; not the integral of a pointwise absolute cross sum.",
        results=results,independent_quadrature=details,precision_bits=ctx.prec,flint_version=flint.__version__,
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),seconds=round(monotonic()-start,2),
        scope="Three actual length-ten bands at one finite integer cutoff. No claim of a bound as X or the band center varies.")
    Path(__file__).with_name("FIXED_BAND_CHECK.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps(data,indent=2))


if __name__=="__main__":
    main()
