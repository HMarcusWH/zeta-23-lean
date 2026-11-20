"""Terminal same-bin small-gcd residue with exact cutoff tests and certified log bins."""
from collections import Counter
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx, fmpz


def ball(v):
    enc = v.str(29)
    assert arb(enc).contains(v)
    return enc


def main():
    begin=monotonic()
    ctx.prec=160
    X,H=2048,5
    centers=[0,14,25]
    width=(-arb(X).log().sqrt()).exp()
    power=X**99
    active=[]
    all_terminal={}
    margins=[]
    for q in range(1,X+1):
        if q**100>power:
            t=(arb(X)/q).log()/width
            r=t.floor().unique_fmpz()
            assert r is not None
            group=int(r)
            if q<X:
                assert group<t and t<group+1
                margins.extend([t-group,group+1-t])
            else:
                assert t.is_zero() and group==0
            all_terminal.setdefault(group,[]).append(q)
        else:
            group=-1
        if gcd(q,6)==1:
            mu=int(fmpz(q).moebius_mu())
            if mu:
                active.append((q,group,mu,arb(mu)/arb(q).sqrt(),arb(q).log()))
    assert len(all_terminal)==2 and 1<X<2**100
    assert min(margins)>0
    groups=sorted({g for _,g,_,_,_ in active})
    intervals={g:[q for q,c,_,_,_ in active if c==g] for g in groups}
    sizes={g:len(qs) for g,qs in intervals.items()}
    diagonal={g:arb(0) for g in groups}
    for q,g,*_ in active:
        diagonal[g]+=arb(2*H)/q
    keys=[(a,b) for a in groups for b in groups if a<=b]
    cross={j:{k:arb(0) for k in keys} for j in centers}
    signed={j:{g:arb(0) for g in all_terminal} for j in centers}
    abs_cross={j:{g:arb(0) for g in all_terminal} for j in centers}
    omitted={j:{g:arb(0) for g in all_terminal} for j in centers}
    counts=Counter()
    multiplicities={g:Counter() for g in all_terminal}
    for i,(r,h,_,ar,logr) in enumerate(active):
        for q,g,_,aq,logq in active[:i]:
            assert q<r
            key=tuple(sorted((g,h)))
            counts[key]+=1
            u=logr-logq
            assert u>0
            kernel=4*aq*ar*(H*u).sin()/u
            same=(g==h and g>=0)
            D=gcd(q,r) if same else 0
            if same:
                multiplicities[g][D]+=1
                assert (D**100<X)==(D==1)
            for j in centers:
                term=kernel if j==0 else kernel*(j*u).cos()
                cross[j][key]+=term
                if same:
                    if D==1:
                        signed[j][g]+=term
                        abs_cross[j][g]+=abs(term)
                    else:
                        omitted[j][g]+=term
    prior_path=Path(__file__).with_name("FIXED_BAND_CHECK.json")
    prior=json.loads(prior_path.read_bytes())
    assert prior["X"]==X and prior["centers"]==centers and prior["half_width_H"]==H
    assert sum(counts.values())==len(active)*(len(active)-1)//2==prior["unordered_cross_pairs_per_center"]
    for a,b in keys:
        assert counts[a,b]==(sizes[a]*(sizes[a]-1)//2 if a==b else sizes[a]*sizes[b])
    shells={}
    for g,qs in sorted(all_terminal.items()):
        assert sorted(qs)==list(range(min(qs),max(qs)+1))
        shells[str(g)]=dict(integer_range=[min(qs),max(qs)],all_integer_sites=len(qs),
            coprime_to_six_sites=sum(gcd(q,6)==1 for q in qs),active_labels=intervals[g],
            active_count=sizes[g],diagonal=ball(diagonal[g]),
            all_unordered_pairs=counts[g,g],same_bin_coprime_pairs=multiplicities[g][1],
            gcd_counts=dict(sorted(multiplicities[g].items())),center_results={})
        for j in centers:
            assert (signed[j][g]+omitted[j][g]).overlaps(cross[j][g,g])
            shells[str(g)]["center_results"][str(j)]=dict(shell_energy=ball(diagonal[g]+cross[j][g,g]),
                retained_coprime_signed=ball(signed[j][g]),retained_coprime_absolute=ball(abs_cross[j][g]),
                omitted_nontrivial_gcd_signed=ball(omitted[j][g]))
    output_by_center={}
    for j in centers:
        whole=sum(diagonal.values(),arb(0))+sum(cross[j].values(),arb(0))
        assert arb(prior["results"][str(j)]["energy"]).overlaps(whole)
        energy={g:diagonal[g]+cross[j][g,g] for g in groups}
        # Cauchy-Schwarz from the true same-band complex L2 Gram matrix. An
        # off-diagonal total here is twice the real part of the inner product.
        for a,b in keys:
            if a!=b:
                assert cross[j][a,b]**2<4*energy[a]*energy[b]
        terminal_diag=sum((diagonal[g] for g in all_terminal),arb(0))
        retained=sum(signed[j].values(),arb(0))
        ab=sum(abs_cross[j].values(),arb(0))
        output_by_center[str(j)]=dict(terminal_diagonal=ball(terminal_diag),
            same_bin_small_gcd_signed=ball(retained),same_bin_small_gcd_absolute=ball(ab),
            diagonal_plus_retained_signed=ball(terminal_diag+retained),
            sum_individual_shell_energies=ball(sum((energy[g] for g in all_terminal),arb(0))),
            between_terminal_shells_signed=ball(cross[j][0,1]),
            energy_of_full_terminal_field=ball(energy[0]+energy[1]+cross[j][0,1]),
            full_energy_from_three_group_Gram=ball(whole),
            three_group_Gram_diagonal={str(g):ball(energy[g]) for g in groups},
            three_group_cross_twice_real={f"{a},{b}":ball(cross[j][a,b]) for a,b in keys if a!=b})
    out=dict(X=X,H=H,centers=centers,theta="1/100",log_bin_width=ball(width),
        support_checks=dict(terminal="q^100 > X^99 and q <= X",
            gcd="gcd(q,r)^100 < X, equivalent here to gcd=1 since 1<X<2^100",
            bins="floor(log(X/q)/exp(-sqrt(log X))) via a uniquely determined Arb floor at every terminal integer; q=X has exact quotient 0",
            separated_nonendpoint_bin_decisions=min(margins).str(24),
            all_complete_active_labels=len(active),outside_terminal_active=sizes[-1],
            terminal_active=sum(sizes[g] for g in all_terminal),
            same_bin_unordered_pairs=sum(counts[g,g] for g in all_terminal),
            retained_same_bin_unordered_pairs=sum(row[1] for row in multiplicities.values())),
        shell_results=shells,center_results=output_by_center,
        convention="Complex Dirichlet polynomial of all mu(q)*1_(q,6)=1/sqrt(q); diagonal counts are separate. Every unordered off-diagonal pair contributes in both ordered directions. Absolute values apply after integrating each complete conjugate pair.",
        previous_complete_energy_sha256=sha256(prior_path.read_bytes()).hexdigest(),
        precision_bits=ctx.prec,flint_version=flint.__version__,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=round(monotonic()-begin,2),status="FINITE_TERMINAL_SECTOR; no asymptotic statement")
    Path(__file__).with_name("NATIVE_PAIR_SECTOR.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf8")
    print(out["support_checks"])
    for j in centers:
        print(j,{k:output_by_center[str(j)][k] for k in ("same_bin_small_gcd_signed","same_bin_small_gcd_absolute","terminal_diagonal","sum_individual_shell_energies")})


if __name__=="__main__":
    main()
