"""Evaluate every unpaid reduced frequency at the first surviving integer site."""
from array import array
import hashlib
import json
from math import gcd
from pathlib import Path
import time

import flint
from flint import arb, ctx, fmpz


ctx.prec = 128
folder = Path(__file__).resolve().parent


def first_site():
    # This integer inequality is necessary and sufficient for a nonempty tail.
    for l in range(2,300001):
        z = fmpz(l)
        prefix = int((z**5).root(6))
        if (l+prefix+1)**100 <= l**101:
            end = int((z**101).root(100))
            assert prefix**6 <= l**5 < (prefix+1)**6
            assert end**100 <= l**101 < (end+1)**100
            return l,prefix,end
    raise ArithmeticError("No nonempty cutoff in the search.")


def mobius_sieve(n):
    mu = array("b",[0])*(n+1)
    mu[1]=1
    composite=bytearray(n+1)
    primes=[]
    for k in range(2,n+1):
        if not composite[k]:
            primes.append(k)
            mu[k]=-1
        for p in primes:
            j=k*p
            if j>n:
                break
            composite[j]=1
            if k%p==0:
                break
            mu[j]=-mu[k]
    return mu


def coefficients(l,mu):
    a={m:-arb(mu[m])/m for m in range(2,l+1) if mu[m]}
    low0=sum(a.values(),arb(0))
    low1=-sum(mu[m] for m in range(2,l+1))
    low2=-sum(m*mu[m] for m in range(2,l+1))
    mass=1-low0
    centres=range(9*((2*l)//9+1),3*l+1,9)
    assert len(centres)>0
    for r in centres:
        lin=arb(3-low1)/r
        quad=arb(13-low2)/(r*r)
        z=(quad-3*lin+2*mass)/6
        y=lin-mass-3*z
        for m,v in ((r,mass-y-z),(2*r,y),(4*r,z)):
            a[m]=a.get(m,0)+v/len(centres)
    for k,target in enumerate((1,3,13)):
        assert sum((v*m**k for m,v in a.items()),arb(0)).contains(target)
    return a,centres


def cosines(seed,limit):
    # Half-index recurrence has logarithmic depth. No floating-point phases.
    c=[arb(1),seed]
    for h in range(2,limit+1):
        k=h//2
        if h%2:
            c.append(2*c[k]*c[k+1]-seed)
        else:
            c.append(2*c[k]*c[k]-1)
    return c


def fraction_bounds(x,scale):
    # Independently machine-readable outward integer bounds on x*scale.
    return [str((x*scale).lower().floor().unique_fmpz()),
            str((x*scale).upper().ceil().unique_fmpz())]


def run():
    start=time.monotonic()
    l,prefix,end=first_site()
    ns=list(range(l+prefix+1,end+1))
    assert (l,ns)==(205793,[232576])
    n=ns[0]
    assert n<=2*l
    mu=mobius_sieve(n)
    a,centres=coefficients(l,mu)
    exact=sum(mu[j]*(n-j) for j in range(l+1,n+1))
    modulus_ramp=arb(-1)+sum((v*(n%m)*(m-n%m) for m,v in a.items()),arb(0))/2
    assert modulus_ramp.contains(exact)
    nscale=l
    blocks=[]
    all_signed=arb(0)
    maxm=max(a)
    d=1
    while d<=maxm:
        dstop=min(2*d-1,maxm)
        k=1
        unpaid=[]
        while k<=dstop//2:
            if d**5*l>nscale**5*k**3 and d**4*l>nscale**4*k**4:
                unpaid.append(k)
            k*=2
        if not unpaid:
            d*=2
            continue
        assert unpaid==[1<<j for j in range(len(unpaid))]
        maxh=2*unpaid[-1]-1
        assert 2*maxh<d
        signed={k:arb(0) for k in unpaid}
        counts={k:0 for k in unpaid}
        denoms=terms=spots=0
        for q in range(d,dstop+1):
            terms_q=[a[m] for m in range(q,maxm+1,q) if m in a]
            if not terms_q:
                continue
            denoms+=1
            terms+=len(terms_q)
            sq=sum(terms_q,arb(0))
            # q and q-h are conjugate at integer n. Their total equals
            # -S_q cos(2*pi*h*n/q)/(1-cos(2*pi*h/q)).
            theta=arb(2)/q
            unscaled=cosines(theta.cos_pi(),maxh)
            rotated=cosines((theta*(n%q)).cos_pi(),maxh)
            check_direct=denoms==1 or q%7919==0
            local={k:arb(0) for k in unpaid}
            for h in range(1,maxh+1):
                if gcd(h,q)!=1:
                    continue
                k=1<<(h.bit_length()-1)
                denom=1-unscaled[h]
                assert denom>0
                term=rotated[h]/denom
                if check_direct:
                    reference=(arb(2*((h*n)%q))/q).cos_pi()/(2*(arb(h)/q).sin_pi()**2)
                    assert term.overlaps(reference)
                    spots+=1
                local[k]+=term
                counts[k]+=2
            for k in unpaid:
                signed[k]-=sq*local[k]
        for k in unpaid:
            all_signed+=signed[k]
        blocks.append(dict(D=d,q_last=dstop,denominators_with_any_source_multiple=denoms,
                      source_multiple_terms=terms,independent_trig_checks=spots,
                      K_blocks=[dict(K=k,reduced_frequencies_with_conjugates=counts[k],
                                     signed_amplitude=signed[k].str(27)) for k in unpaid]))
        print(f"D={d}: {denoms} denominators, {sum(counts.values())} reduced frequencies",flush=True)
        d*=2
    h_stat=abs(all_signed)/(n**3)
    level=1/arb(l).sqrt()
    b_site=arb(abs(exact))/(n**3)
    assert h_stat>0 and h_stat<level
    assert (h_stat*10**20).rad()<1
    bound=(1/arb(l).sqrt()).str(28)
    data=dict(status="BOUNDED_NATIVE_FREQUENCY_CALCULATION",precision_bits=ctx.prec,flint_version=flint.__version__,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              exhaustive_nonempty_search=dict(first_L=l,integers_checked_from=2,integers_checked_through=l,
                floor_L_5_over_6=prefix,floor_L_101_over_100=end,surviving_sites=ns),
              exact_rational_calibration="a_m=-mu(m)/m for 2<=m<=L with rational 0th,1st,2nd targets 1,3,13; corrections at R,2R,4R equally averaged over 9|R, 2L<R<=3L; evaluated with Arb enclosures.",
              centre_count=len(centres),centre_first=centres[0],centre_last=centres[-1],
              source_moduli_with_a_coefficient=len(a),max_modulus=maxm,denominator_blocks=blocks,
              both_strict_conditions="D^5*L > N^5*K^3 and D^4*L > N^4*K^4, N=L for the sole native site",
              signed_before_absolute=all_signed.str(29),weighted_H=h_stat.str(29),
              H_scaled_outward_1e30=fraction_bounds(h_stat,10**30),critical_scale=bound,
              H_over_critical=(h_stat/level).str(29),
              full_knot_exact_integer_from_Mobius=exact,full_knot_from_true_modular_formula=modulus_ramp.str(29),
              full_knot_weight_at_this_site=b_site.str(29),
              inferred_paid_signed_at_this_site=(exact-all_signed).str(29),
              reduced_frequencies_including_conjugates=sum(x["reduced_frequencies_with_conjugates"] for group in blocks for x in group["K_blocks"]),
              timing_seconds=round(time.monotonic()-start,2),
              scope="Entire finite H at this one integer cutoff, with no discarded correction moduli or numerator contributions. A single comparison with L^(-1/2) cannot establish the cofinal inequality or RH.")
    out=folder/"NATIVE_RESIDUAL_CHECK.json"
    out.write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print("H:",data["weighted_H"],"H/critical:",data["H_over_critical"],flush=True)


if __name__=="__main__":
    run()
