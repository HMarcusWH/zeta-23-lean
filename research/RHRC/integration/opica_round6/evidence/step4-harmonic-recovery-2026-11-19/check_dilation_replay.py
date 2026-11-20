"""Independent integer and Arb replay of both sides of the signed dilation identity."""
from array import array
from hashlib import sha256
import json
from math import gcd, isqrt, prod
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx


def mobius(limit):
    values = array("b",[0])*(limit+1)
    values[1] = 1
    composite = bytearray(limit+1)
    primes = []
    for n in range(2,limit+1):
        if not composite[n]:
            primes.append(n)
            values[n] = -1
        for p in primes:
            m = p*n
            if m > limit:
                break
            composite[m] = 1
            if n%p == 0:
                break
            values[m] = -values[n]
    return values


def w(k, modulus, dilation):
    return int(gcd(k,modulus)==1)-dilation*int(k%dilation==0 and gcd(k//dilation,modulus)==1)


def show(a):
    s = a.str(28)
    assert arb(s).contains(a)
    return s


def convolution_rhs(j, extra, d, mu):
    first = mu[j] if extra%j==0 else 0
    second = mu[j//d] if j%d==0 and extra%(j//d)==0 else 0
    return first-d*second


def run():
    ctx.prec = 128
    begin = monotonic()
    x = 2**22
    # Prove 7 < 11*log(2) < 8 using exact rationals 2/3 < log(2) < 7/10.
    # For the upper bound, exp(7/10)>1+t+t^2/2+t^3/6 > 2;
    # the lower follows from log(2)=2*atanh(1/3)>2/3.
    assert 3*7 < 2*11 and 7*11 < 8*10
    assert 6000+4200+1470+343 > 12000
    z = 7
    Q = prod((2,3,5,7))
    d = 1 << z.bit_length()
    cut = isqrt(x)
    first = 24*x//25+1
    span = x-first+1
    assert d//2<=z<d and cut**2==x and d*(Q//6)<first
    mu = mobius(x)
    fq = array("b", [mu[q] if gcd(q,6)==1 else 0 for q in range(x+1)])
    physical = []
    for j in range(first,x+1):
        value = (arb(21*x)/(10*j)).cos_pi()*j/x
        assert value>0
        physical.append(value)
    coeff0 = array("i", fq[first:x+1])
    coeff_m = array("i",[0])*span
    coeff_t = array("i",[0])*span
    native = sum((physical[i]*v for i,v in enumerate(coeff0) if v),arb(0))
    by_k = {}
    middle = middle_tv = middle_label_tv = arb(0)
    critical_middle_l1 = critical_middle_signed = arb(0)
    tail_label_tv = arb(0)
    middle_pairs = tail_pairs = middle_rows = 0
    middle_raw = tail_raw = 0
    for k in range(2,cut+1):
        wk = w(k,Q,d)
        if not wk:
            continue
        critical_coefficient = arb(wk)/arb(k).sqrt()
        critical_middle_l1 += abs(critical_coefficient)
        critical_middle_signed += critical_coefficient
        subtotal = arb(0)
        present = 0
        for q in range((first+k-1)//k,x//k+1):
            c = wk*fq[q]
            if not c:
                continue
            idx = q*k-first
            coeff_m[idx] += c
            val = c*physical[idx]
            subtotal += val
            middle_label_tv += abs(val)
            middle_raw += abs(c)
            present += 1
        middle_pairs += present
        middle_rows += int(present>0)
        middle += subtotal
        middle_tv += abs(subtotal)
    # Change the outer variable for the entire tail: q <= floor(x/(cut+1)).
    for q in range(1,x//(cut+1)+1):
        if not fq[q]:
            continue
        for k in range(max(cut+1,(first+q-1)//q),x//q+1):
            c = w(k,Q,d)*fq[q]
            if not c:
                continue
            idx = q*k-first
            val = c*physical[idx]
            coeff_t[idx] += c
            by_k[k] = by_k.get(k,0)+val
            tail_label_tv += abs(val)
            tail_raw += abs(c)
            tail_pairs += 1
    tail = sum(by_k.values(),arb(0))
    tail_tv = sum((abs(v) for v in by_k.values()),arb(0))
    def row(cc):
        return sum((v*m for v,m in zip(physical,cc) if m),arb(0))
    def j_variation(cc):
        return sum((v*abs(m) for v,m in zip(physical,cc) if m),arb(0))
    rm, rt = row(coeff_m), row(coeff_t)
    assert rm.overlaps(middle) and rt.overlaps(tail)
    agreement = bad = nonzero_total = 0
    for idx in range(span):
        total = coeff0[idx]+coeff_m[idx]+coeff_t[idx]
        expected = convolution_rhs(first+idx,Q//6,d,mu)
        agreement += int(total==expected)
        bad += int(total!=expected)
        nonzero_total += int(total!=0)
    assert agreement==span and not bad and not nonzero_total
    assert (native+middle+tail).contains(0)
    assert all(not val.contains(0) for val in (native,middle,tail))
    assert abs(middle)<=middle_tv and middle_tv<=middle_label_tv
    assert abs(tail)<=tail_tv and tail_tv<=tail_label_tv
    raw_digest = sha256()
    for cc in (coeff0,coeff_m,coeff_t):
        for value in cc:
            raw_digest.update(value.to_bytes(4,"little",signed=True))
    out = dict(scope="Finite replay of the homogeneous physical h=1 row, with continuous site c*x. The separate integer-site and sine-normalization rounding is not built into v.",
        x=x,z=z,Q=Q,d=d,extra_primes_product=Q//6,middle_k=[2,cut],tail_k=[cut+1,x],
        product_integer_interval=[first,x],product_sites=span,input_rows=dict(native_nonzero_labels=sum(map(bool,coeff0)),
        middle_nonempty_k_rows=middle_rows,tail_nonempty_k_rows=len(by_k),middle_nonzero_pairs=middle_pairs,tail_nonzero_pairs=tail_pairs,
        middle_unweighted_absolute_pair_coefficients=middle_raw,tail_unweighted_absolute_pair_coefficients=tail_raw),
        integer_coefficient_check=dict(sites_matching_independent_convolution_rhs=agreement,
        sites_with_nonzero_total=nonzero_total,middle_nonzero_after_j_grouping=sum(map(bool,coeff_m)),
        tail_nonzero_after_j_grouping=sum(map(bool,coeff_t)),max_abs_middle=max(map(abs,coeff_m)),max_abs_tail=max(map(abs,coeff_t)),
        coefficients_sha256=raw_digest.hexdigest(),encoding="int32 little-endian, native then middle then tail, j increasing"),
        v_x=show(native),v_x_over_sqrt_x=show(native/cut),signed_middle=show(middle),signed_tail=show(tail),
        full_signed_sum=show(native+middle+tail),separately_product_grouped_middle=show(rm),separately_product_grouped_tail=show(rt),
        row_triangle_middle=show(middle_tv),row_triangle_tail=show(tail_tv),
        middle_dilation_sqrt_weight_operator_l1=show(critical_middle_l1),
        middle_signed_sqrt_weight_coefficients=show(critical_middle_signed),
        product_triangle_middle=show(j_variation(coeff_m)),product_triangle_tail=show(j_variation(coeff_t)),
        absolute_pair_triangle_middle=show(middle_label_tv),absolute_pair_triangle_tail=show(tail_label_tv),
        precisions_bits=ctx.prec,flint_version=flint.__version__,source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=round(monotonic()-begin,2))
    Path(__file__).with_name("DILATION_REPLAY.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf8")
    print(json.dumps(out,indent=2))


if __name__=="__main__":
    run()
