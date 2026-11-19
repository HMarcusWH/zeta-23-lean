"""Finite control of the genuine grouped spectrum. Requires python-flint."""
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import json
from math import gcd
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpz

from check_period_graph import calibration, kernel, mobius


ctx.prec = 160
folder = Path(__file__).resolve().parent


def ball(x):
    return arb(x.numerator)/x.denominator


def dyadic(x):
    return 1 << (x.bit_length()-1)


def gate(l, nscale, d, k):
    return (d**5*l <= nscale**5*k**3, d**4*l <= nscale**4*k**4)


def geometric_controls():
    prefixes = divisibility_counts = interval_counts = geometric_identities = 0
    for q in range(2,49):
        factors = [(d,mobius(d)) for d in range(1,q+1) if q%d==0 and mobius(d)]
        k = 1
        while k <= q//2:
            stop = min(2*k-1,q//2)
            for v in range(k,stop+1):
                direct = [int(k<=h<=v and gcd(h,q)==1) for h in range(q)]
                inverted = [0]*q
                for d,mu in factors:
                    first, last = (k+d-1)//d, v//d
                    length = max(0,last-first+1)
                    assert length <= q//d
                    divisibility_counts += 1
                    for j in range(first,last+1):
                        inverted[d*j] += mu
                assert direct == inverted
                prefixes += 1
            k *= 2
    for Q in range(1,33):
        env = [F(Q) if r==0 else F(Q,2*min(r,Q-r)) for r in range(Q)]
        harmonic = sum((F(1,t) for t in range(1,Q//2+1)),F(0))
        assert sum(env)/Q <= 1+harmonic
        for n in range(Q):
            # (1-z^n) times every geometric prefix, as integer coefficients
            # modulo z^Q-1. Starting at zero suffices by unit rotation.
            sums = [0]*Q
            for length in range(Q+1):
                lhs = [sums[a]-sums[(a-n)%Q] for a in range(Q)]
                rhs = [0]*Q
                rhs[0] += 1
                rhs[(n*length)%Q] -= 1
                assert lhs==rhs
                if n==0:
                    assert length <= env[0]
                sums[(n*length)%Q] += 1
                geometric_identities += 1
        for start in range(Q):
            for N in (1,Q,max(1,2*Q-1),2*Q+3):
                exact = sum((env[(start+t)%Q] for t in range(N)),F(0))
                assert exact <= ((N+Q-1)//Q)*sum(env)
                interval_counts += 1
    return dict(moduli_up_to=48,coprime_prefix_indicator_vectors=prefixes,
                exact_divisor_interval_counts=divisibility_counts,
                fully_enumerated_reduced_periods_up_to=32,
                exact_cyclic_geometric_identities=geometric_identities,
                exact_consecutive_site_envelope_tests=interval_counts,
                envelope="Q at zero; Q/(2*min(r,Q-r)) elsewhere; finite mean <= 1+H_floor(Q/2)")


def current(l):
    a=calibration(l)
    mean=-1+sum((am*(m*m-1)/12 for m,am in a.items()),F(0))
    assert mean==0
    nend=int(fmpz(l**101).root(100))
    native=list(range(l+1,nend+1))
    extended=[2*l,3*l+1,max(a)+1]
    ns=sorted(set(native+extended))
    bysite={n:defaultdict(acb) for n in ns}
    bydiv={n:defaultdict(acb) for n in ns}
    amp_bounds=0
    exact_residues=0
    denominator_count=0
    direct_spots=0
    primitive_count=0
    positive=negative=0
    zero_q=[]
    midpoint_count=0
    actual_blocks=set()
    for q in sorted({q for m in a for q in range(2,m+1) if m%q==0}):
        terms={m:am for m,am in a.items() if m%q==0}
        s=sum(terms.values(),F(0))
        # Direct source values before Fourier transformation. The integer second
        # difference acts on the source distribution modulo q, including wrap.
        folded=[sum((am*sum(kernel(t,m) for t in range(r,m,q))/(2*m)
                     for m,am in terms.items()),F(0)) for r in range(q)]
        for r in range(q):
            assert folded[(r+1)%q]+folded[(r-1)%q]-2*folded[r] == s*(int(r==0)-F(1,q))
        exact_residues+=q
        if not s:
            zero_q.append(q)
            continue
        denominator_count+=1
        phase=[acb((arb(2*h)/q).cos_pi(),(arb(2*h)/q).sin_pi()) for h in range(q)]
        weights=[None]+[-ball(s)/(4*(arb(h)/q).sin_pi()**2) for h in range(1,q)]
        factors=[(d,mobius(d)) for d in range(1,q+1) if q%d==0 and mobius(d)]
        for h in range(1,q):
            if gcd(h,q)!=1:
                continue
            primitive_count+=1
            hs=min(h,q-h)
            if 2*h==q:
                midpoint_count+=1
            key=dyadic(q),dyadic(hs)
            actual_blocks.add(key)
            ah=weights[h]
            assert (ah>0 if s<0 else ah<0)
            positive+=s<0
            negative+=s>0
            assert (ah*(2*phase[h].real-2)).overlaps(ball(s))
            amp_bounds+=1
            if q<=24 or h==1:
                direct=sum((ball(c)*phase[(-h*r)%q] for r,c in enumerate(folded)),acb(0))
                assert direct.real.overlaps(ah) and direct.imag.contains(0)
                direct_spots+=1
            for n in ns:
                bysite[n][key]+=ah*phase[(h*n)%q]
        # Independent ordering: first the true lower half, then Möbius divisor
        # d|q, then interval in j with h=d*j. Reflect and count q/2 only once.
        k=1
        while k<=q//2:
            key=dyadic(q),k
            last=min(2*k-1,q//2)
            for d,mu in factors:
                for j in range((k+d-1)//d, last//d+1):
                    h=d*j
                    for n in ns:
                        z=phase[(j*n%(q//d))*d]
                        reflected=z if 2*h==q else z+z.conjugate()
                        bydiv[n][key]+=mu*weights[h]*reflected
            k*=2
    site_rows=[]
    for n in ns:
        expected=-1+sum((v*kernel(n,m)/2 for m,v in a.items()),F(0))
        direct, regroup=acb(0),acb(0)
        nscale=l
        while 2*nscale<n:
            nscale*=2
        splits=defaultdict(acb)
        counts=defaultdict(int)
        for key in sorted(set(bysite[n])|set(bydiv[n])):
            f,alternate=bysite[n][key],bydiv[n][key]
            assert f.overlaps(alternate) and f.imag.contains(0) and alternate.imag.contains(0)
            direct+=f
            regroup+=alternate
            old,new=gate(l,nscale,*key)
            label="both" if old and new else "large_sieve_only" if old else "numerator_only" if new else "open"
            splits[label]+=f
            counts[label]+=int(key in actual_blocks)
        assert direct.real.contains(ball(expected)) and regroup.real.contains(ball(expected))
        assert sum(splits.values(),acb(0)).overlaps(direct)
        site_rows.append(dict(n=n,scope="native" if n in native else "wider diagnostic",
                              scale=nscale,direct_exact=str(expected),
                              signed_numerator_only=splits["numerator_only"].real.str(23),
                              signed_unpaid=splits["open"].real.str(23),nonzero_block_counts=dict(counts)))
    return dict(L=l,centres=[r for r in range(2*l+1,3*l+1) if r%9==0],
                native_cap=nend,native_H_after_L_plus_floor_L_to_5_over_6=max(0,nend-l-int(fmpz(l**5).root(6))),
                nonzero_coefficients=len(a),exact_mean=str(mean),denominators_with_nonzero_S=denominator_count,
                denominators_with_exact_zero_S=zero_q,primitive_frequencies=primitive_count,
                by_amplitude_sign=[positive,negative],midpoint_occurrences=midpoint_count,
                exact_folded_second_difference_entries=exact_residues,symbol_checks=amp_bounds,
                independent_direct_source_DFT_coefficients=direct_spots,site_checks=site_rows)


def main():
    cases=[current(l) for l in (9,36,128)]
    classification=[]
    for l,k in [(128,4),(16384,16),(16384,8),(16384,32)]:
        old,new=gate(l,l,l,k)
        classification.append(dict(L=l,N=l,D=l,K=k,old=old,new=new,
                                   K_strictly_between_fourth_and_third_roots=k**4>l>k**3))
    assert [r["new"] and not r["old"] for r in classification]==[True,True,False,False]
    assert any(s["nonzero_block_counts"].get("numerator_only",0)>0 for s in cases[-1]["site_checks"]
               if s["scope"]=="native")
    out=dict(scope="Finite exact rational/integer and Arb checks of three-moment factorial graph; no asymptotic bound or closure test.",
             precision_bits=ctx.prec,flint_version=flint.__version__,source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
             coefficient_module_sha256=sha256((folder/"check_period_graph.py").read_bytes()).hexdigest(),
             true_calibrations=cases,integer_gate_examples=classification,geometric_envelopes=geometric_controls())
    (folder/"FREQUENCY_BLOCK_CHECK.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf8")
    print([(r["L"],r["primitive_frequencies"],len(r["site_checks"])) for r in cases],out["geometric_envelopes"])


if __name__=="__main__":
    main()
