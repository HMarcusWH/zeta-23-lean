"""Exact product-by-product and interval evaluation of the rational power-delay replay."""
from array import array
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx

from check_dilation_replay import mobius, show


def largest_sample(record, k, field, x):
    # Zero samples cannot increase the initialized nonnegative maximum.
    ratio = abs(field)*arb(k).sqrt()/arb(x).sqrt()
    if ratio > record[0]:
        return (ratio,[k])
    if ratio < record[0] or ratio.is_zero():
        return record
    return (ratio.union(record[0]),record[1]+[k])


def run():
    t0 = monotonic()
    ctx.prec = 128
    x = 2**22
    y = isqrt(isqrt(x))
    m = y+1
    cut = y*isqrt(x)
    first = 24*x//25+1
    span = x-first+1
    assert y**4<=x<m**4 and cut**2<=y*y*x<(cut+1)**2
    mu = mobius(x)
    fq = array("b",(mu[q] if q%6 in (1,5) else 0 for q in range(x+1)))
    small = {e:fq[e] for e in range(1,y+1) if fq[e]}
    bm = -m*sum((Fraction(c,e) for e,c in small.items()),Fraction())
    scale, coeff = bm.denominator, bm.numerator
    assert sum((Fraction(c,e) for e,c in small.items()),Fraction()) + bm/m == 0
    base = array("i",[0])*(x+1)
    for e, ce in small.items():
        # Integer incidence, exactly the two residue classes of k/e coprime to 6.
        for r in (1,5):
            for k in range(e*r,x+1,6*e):
                base[k] += ce
    def int_weight(k):
        return base[k]*scale + (coeff if k%m==0 and (k//m)%6 in (1,5) else 0)
    assert int_weight(1)==scale and all(int_weight(k)==0 for k in range(2,y+1))
    # Independent literal divisor construction for the entire delayed initial segment.
    bc = dict(small)
    bc[m] = bm
    for k in range(1,2*m+1):
        expected = sum((b for e,b in bc.items() if k%e==0 and (k//e)%6 in (1,5)),Fraction())
        assert int_weight(k)==expected*scale
    weights = []
    for j in range(first,x+1):
        wj = (arb(21*x)/(10*j)).cos_pi()*j/x
        assert wj>0
        weights.append(wj)
    native_int = [scale*s for s in fq[first:x+1]]
    middle_int = [0]*span
    tail_int = [0]*span
    native = sum((v*c for v,c in zip(weights,native_int) if c),arb(0))/scale
    middle = mid_rows_abs = mid_terms_abs = mid_critical_abs = mid_critical_signed = arb(0)
    tail = tail_rows_abs = tail_terms_abs = arb(0)
    mid_max, tail_max = (arb(0),[]),(arb(0),[])
    active_mid = mid_pairs = mid_nonempty = tail_pairs = 0
    for k in range(m,cut+1):
        wk = int_weight(k)
        if wk==0:
            continue
        active_mid += 1
        mod_norm = arb(wk)/(scale*arb(k).sqrt())
        mid_critical_abs += abs(mod_norm)
        mid_critical_signed += mod_norm
        v_k = abs_k = arb(0)
        support = 0
        for q in range((first+k-1)//k,x//k+1):
            if not fq[q]:
                continue
            idx = k*q-first
            c = fq[q]
            middle_int[idx] += wk*c
            v_k += weights[idx]*c
            abs_k += weights[idx]
            support += 1
        mid_pairs += support
        mid_nonempty += int(support>0)
        if support:
            mid_max = largest_sample(mid_max,k,v_k,x)
        middle += wk*v_k/scale
        mid_rows_abs += abs(wk*v_k/scale)
        mid_terms_abs += abs(wk)*abs_k/scale
    # Independent order for k>cut. Enumerate every q first, with exact endpoints.
    tail_by_k = {}
    tail_critical_used_abs = arb(0)
    for q in range(1,x//(cut+1)+1):
        if not fq[q]:
            continue
        for k in range(max(cut+1,(first+q-1)//q),x//q+1):
            wk = int_weight(k)
            if not wk:
                continue
            idx = k*q-first
            c = wk*fq[q]
            tail_int[idx] += c
            assert k not in tail_by_k
            tail_by_k[k] = fq[q]*weights[idx]
            tail_terms_abs += abs(c)*weights[idx]/scale
            tail_pairs += 1
    for k,v_k in tail_by_k.items():
        wk = int_weight(k)
        tail += wk*v_k/scale
        tail_rows_abs += abs(wk*v_k/scale)
        tail_max = largest_sample(tail_max,k,v_k,x)
        tail_critical_used_abs += abs(wk)/(scale*arb(k).sqrt())
    # b*A*mu6=b; every b_j vanishes on the product window.
    assert first>m and first>cut
    for idx in range(span):
        assert native_int[idx]+middle_int[idx]+tail_int[idx]==int(bc.get(first+idx,0)*scale)==0
    def product_sum(cs,absolute=False):
        return sum((v*(abs(c) if absolute else c) for v,c in zip(weights,cs) if c),arb(0))/scale
    assert product_sum(middle_int).overlaps(middle)
    assert product_sum(tail_int).overlaps(tail)
    assert (native+middle+tail).contains(0)
    assert all(not a.contains(0) for a in (native,middle,tail))
    assert mid_rows_abs < mid_terms_abs
    # The support in q has width <2, while two consecutive coprime-to-6
    # integers differ by at least 2. Every occupied tail row is a singleton.
    assert x < 50*(cut+1) and tail_rows_abs.overlaps(tail_terms_abs)
    assert mid_rows_abs/arb(x).sqrt() <= mid_critical_abs*mid_max[0]
    assert tail_rows_abs/arb(x).sqrt() <= tail_critical_used_abs*tail_max[0]
    dig = sha256()
    for arr in (native_int,middle_int,tail_int):
        for c in arr:
            dig.update(c.to_bytes(16,"little",signed=True))
    previous = Path(__file__).with_name("DILATION_REPLAY.json")
    assert arb(json.loads(previous.read_bytes())["v_x"]).overlaps(native)
    def data_max(item):
        return dict(maximum=show(item[0]),maximizing_k=item[1],
                    inputs_x_over_k=[str(Fraction(x,k)) for k in item[1]])
    data=dict(scope="Full finite rational dilation replay of homogeneous v(x) at the actual real arguments x/k. No discrete site rounding, sine-normalization replacement, or continuous-history supremum is asserted.",
        x=x,Y=y,m=m,K=cut,b_m=str(bm),common_denominator=scale,small_b=small,
        delay=dict(first_nonzero_after_k_1=next(k for k in range(2,x+1) if int_weight(k)),exact_zero_weight_interval=[2,y]),
        product_j=[first,x],all_product_coefficients_exactly_zero=span,
        scaled_integer_coefficients_sha256=dig.hexdigest(),
        digest_encoding="Three consecutive arrays in native, middle, tail order; all j ascending, coefficients multiplied by common_denominator, signed int128 little-endian.",
        middle=dict(k_interval=[m,cut],nonzero_weight_k=active_mid,nonempty_rows=mid_nonempty,nonzero_pairs=mid_pairs,
            nonzero_after_product_grouping=sum(map(bool,middle_int)),signed=show(middle),sum_absolute_rows=show(mid_rows_abs),
            sum_absolute_pairs=show(mid_terms_abs),sum_absolute_grouped_products=show(product_sum(middle_int,True)),
            critical_coefficient_l1=show(mid_critical_abs),signed_critical_coefficients=show(mid_critical_signed),
            historical_sup_abs_v_over_sqrt_argument=data_max(mid_max)),
        tail=dict(k_interval=[cut+1,x],nonempty_rows=len(tail_by_k),nonzero_pairs=tail_pairs,
            exactly_one_source_pair_per_nonempty_row=True,
            nonzero_after_product_grouping=sum(map(bool,tail_int)),signed=show(tail),sum_absolute_rows=show(tail_rows_abs),
            sum_absolute_pairs=show(tail_terms_abs),sum_absolute_grouped_products=show(product_sum(tail_int,True)),
            critical_coefficient_l1_on_nonempty_rows=show(tail_critical_used_abs),
            historical_sup_abs_v_over_sqrt_argument=data_max(tail_max)),
        v_x=show(native),v_x_over_sqrt_x=show(native/arb(x).sqrt()),signed_complete=show(native+middle+tail),
        precision_bits=ctx.prec,flint_version=flint.__version__,
        sqrt_sup_scope="All k in the indicated sector with rational weight nonzero; empty v(x/k) rows have field zero, so cannot enlarge either strictly positive maximum.",
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        imported_helper_sha256=sha256(Path(__file__).with_name("check_dilation_replay.py").read_bytes()).hexdigest(),
        prior_v_x_receipt_sha256=sha256(previous.read_bytes()).hexdigest(),seconds=round(monotonic()-t0,2))
    Path(__file__).with_name("POWER_DELAY_CHECK.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps(data,indent=2))


if __name__=="__main__":
    run()
