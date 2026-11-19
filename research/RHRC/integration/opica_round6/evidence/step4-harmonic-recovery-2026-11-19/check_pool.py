"""Complete finite squared literal h=1 row, with two evaluations of all long gaps."""
from bisect import bisect_left, bisect_right
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx, fmpz


def ball(v):
    text = v.str(28)
    assert arb(text).contains(v)
    return text


def run(first_l=100, last_l=8192, gap=16):
    begin = monotonic()
    ctx.prec = 128
    mu = [int(fmpz(q).moebius_mu()) if q>=1 and gcd(q,6)==1 else 0
          for q in range(last_l+1)]
    active = [q for q in range(2,last_l+1) if mu[q]]
    weights = {q: arb(mu[q])/(2*q*(arb(1)/q).sin_pi()**2) for q in active}
    short_val = [arb(0) for _ in range(gap+1)]
    short_num = [0]*(gap+1)
    energy = diagonal = long_direct = absolute_long = arb(0)
    pairs = long_num = count = eligible = positive_rows = negative_rows = zero_rows = 0
    positive_labels = negative_labels = short_localizable = outer_cutoff_sites = 0
    long_support_min = long_support_max = None
    for L in range(first_l,last_l+1):
        n = (21*L)//20
        low = (24*L)//25+1
        # For q coprime to 6 in this band, q is the unique low multiple
        # and 9*q>3L excludes all the distributed calibration moduli.
        assert 2*low>L and 9*low>3*L
        assert (3*L)//9 > (2*L)//9
        assert n>L and 8*n<9*low
        short_localizable += int((n-L)**6 > L**5)
        outer_cutoff_sites += int(n**100<=L**101)
        eligible += sum((L-r)//6-(low-1-r)//6 for r in (1,5))
        qs = active[bisect_left(active,low):bisect_right(active,L)]
        rlen = len(qs)
        count += rlen
        pairs += rlen*(rlen-1)//2
        previous = []
        row = diag = long_sum = long_abs = hist = hist_abs = arb(0)
        short = [arb(0) for _ in range(gap+1)]
        long_ct = short_ct = prefix = 0
        for i,q in enumerate(qs):
            term = weights[q]*(arb(2*(n-q))/q).cos_pi()
            if mu[q]>0:
                assert term>0
                positive_labels+=1
            else:
                assert term<0
                negative_labels+=1
            row += term
            diag += term**2
            while prefix<i and q-qs[prefix]>gap:
                hist += previous[prefix]
                hist_abs += abs(previous[prefix])
                prefix += 1
            long_sum += 2*term*hist
            long_abs += 2*abs(term)*hist_abs
            long_ct += prefix
            if prefix:
                lo = q-qs[prefix-1]
                hi = q-qs[0]
                long_support_min = lo if long_support_min is None else min(lo,long_support_min)
                long_support_max = hi if long_support_max is None else max(hi,long_support_max)
            for j in range(prefix,i):
                h = q-qs[j]
                assert 1<=h<=gap
                short[h]+=2*term*previous[j]
                short_num[h]+=1
                short_ct+=1
            previous.append(term)
        assert rlen*(rlen-1)//2==long_ct+short_ct
        long_num += long_ct
        assert (row**2-diag-sum(short,arb(0))).overlaps(long_sum)
        factor = arb(1)/(L**4)
        energy += row**2*factor
        diagonal += diag*factor
        long_direct += long_sum*factor
        absolute_long += long_abs*factor
        for h in range(1,gap+1):
            short_val[h] += short[h]*factor
        if row>0:
            positive_rows+=1
        elif row<0:
            negative_rows+=1
        else:
            assert row.is_zero()
            zero_rows+=1
    short_total=sum(short_val,arb(0))
    long_difference=energy-diagonal-short_total
    assert long_difference.overlaps(long_direct)
    assert sum(short_num)+long_num==pairs and positive_labels+negative_labels==count
    assert positive_rows+negative_rows+zero_rows==last_l-first_l+1
    assert energy>0 and absolute_long>=abs(long_direct)
    data=dict(status="FINITE_COMPLETE_POOLED_LITERAL_ROW",L_inclusive=[first_l,last_l],cutoffs=last_l-first_l+1,short_gap_max=gap,
        input="n=floor(21L/20), 24L/25<q<=L, gcd(q,6)=1; coefficient mu(q)cos(2*pi*n/q)/(2q sin^2(pi/q)); squared arithmetic row weighted by 1/L^4.",
        literal_row_count_by_sign=dict(positive=positive_rows,negative=negative_rows,zero=zero_rows),
        integer_support=dict(coprime_labels_including_zeros=eligible,zero_mobius_labels=eligible-count,
            active_labels=count,mu_positive=positive_labels,mu_negative=negative_labels,
            diagonal_terms=count,total_distinct_unordered_pairs=pairs,short_unordered_pairs=sum(short_num),
            long_unordered_pairs=long_num,min_and_max_long_gap=[long_support_min,long_support_max],
            signed_cross_terms_include_both_orders=True),
        complete_energy=ball(energy),diagonal=ball(diagonal),short_signed_cross=ball(short_total),
        long_signed_cross_by_total_difference=ball(long_difference),long_signed_cross_by_prefix=ball(long_direct),
        long_absolute_cross_by_prefix=ball(absolute_long),complete_energy_over_diagonal=ball(energy/diagonal),
        short_by_exact_gap=[dict(gap=i,unordered_pairs=short_num[i],contribution=ball(short_val[i])) for i in range(1,gap+1)],
        native_position_scope=dict(cutoffs_with_site_above_L_plus_floor_L_5_over_6=short_localizable,
            cutoffs_with_site_at_most_floor_L_101_over_100=outer_cutoff_sites,
            qualifier="The row formula is literal for all checked L; the additional late-site qualification used by the full unpaid graph is recorded separately."),
        validation="At each L, the entire signed long-gap sector was independently computed both by subtraction from the row square and by prefixing all earlier q with q_current-q>H. Counts partition every unordered pair, and every off-diagonal term is doubled.",
        precision_bits=ctx.prec,flint_version=flint.__version__,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=round(monotonic()-begin,2))
    output=Path(__file__).with_name("POOL_CHECK.json")
    output.write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps({k:data[k] for k in ("complete_energy","diagonal","short_signed_cross","long_signed_cross_by_prefix","long_absolute_cross_by_prefix","integer_support","native_position_scope","seconds")},indent=2))


if __name__=="__main__":
    run()
