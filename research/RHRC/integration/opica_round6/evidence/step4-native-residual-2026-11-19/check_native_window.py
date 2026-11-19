"""Certify the entire native frequency residual at L=2^18; requires python-flint."""
from array import array
from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, gcd, prod
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx, fmpz


def mobius_values(limit):
    values = array("b", [0]) * (limit + 1)
    values[1] = 1
    composite = bytearray(limit + 1)
    primes = []
    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            values[n] = -1
        for p in primes:
            nxt = n*p
            if nxt > limit:
                break
            composite[nxt] = 1
            if n % p == 0:
                break
            values[nxt] = -values[n]
    return values


def calibrated_moduli(L, mu):
    a = {m: -arb(mu[m])/m for m in range(2, L+1) if mu[m]}
    debt0 = 1 - sum(a.values(), arb(0))
    debt1 = 3 + sum(mu[m] for m in range(2, L+1))
    debt2 = 13 + sum(m*mu[m] for m in range(2, L+1))
    centres = range(((2*L)//9+1)*9, 3*L+1, 9)
    for r in centres:
        slope = arb(debt1)/r
        curve = arb(debt2)/(r*r)
        z = (curve-3*slope+2*debt0)/6
        y = slope-debt0-3*z
        for m, v in ((r, debt0-y-z), (2*r, y), (4*r,z)):
            a[m] = a.get(m, 0) + v/len(centres)
    for i, target in enumerate((1, 3, 13)):
        assert sum((v*m**i for m, v in a.items()), arb(0)).contains(target)
    return a, centres


def cos_multiples(x, top):
    # cos((2k+1)t)=2 cos(kt)cos((k+1)t)−cos(t). Logarithmic dependency depth.
    values = [arb(1), x.cos_pi()]
    for h in range(2, top+1):
        k = h//2
        if h%2:
            values.append(2*values[k]*values[k+1]-values[1])
        else:
            values.append(2*values[k]*values[k]-1)
    return values


def signed_observations(L, a, nodes, end):
    max_m = max(a)
    out = [arb(0) for _ in nodes]
    direct_end = arb(0)
    amplitude_l1 = arb(0)
    maxfreq = Fraction()
    blocks = []
    step = nodes[1]-nodes[0]
    for exp in range(1, max_m.bit_length()):
        D = 1 << exp
        q_max = min(max_m, 2*D-1)
        Ks = [1 << k for k in range(q_max.bit_length()) if
              (1 << k) <= q_max//2 and D**5*L > L**5*(1 << k)**3 and
              D**4*L > L**4*(1 << k)**4]
        if not Ks:
            continue
        assert Ks == [1 << i for i in range(len(Ks))]
        top = 2*Ks[-1]-1
        assert 2*top < D
        pairs = active = 0
        for q in range(D, q_max+1):
            vals = [a[m] for m in range(q, max_m+1, q) if m in a]
            if not vals:
                continue
            active += 1
            sq = sum(vals, arb(0))
            two_q = arb(2)/q
            base = cos_multiples(two_q, top)
            previous = cos_multiples(two_q*((nodes[0]-step)%q), top)
            first = cos_multiples(two_q*(nodes[0]%q), top)
            stride = cos_multiples(two_q*(step%q), top)
            at_end = cos_multiples(two_q*(end%q), top)
            q_top = 0
            for h in range(1, top+1):
                if gcd(q,h) != 1:
                    continue
                q_top = h
                pairs += 1
                denominator = 1-base[h]
                assert denominator > 0
                coefficient = -sq/denominator
                amplitude_l1 += abs(coefficient)
                direct_end += coefficient*at_end[h]
                # Recur on the already weighted, signed conjugate-pair contributions.
                p0, p1 = coefficient*previous[h], coefficient*first[h]
                stride2 = 2*stride[h]
                out[0] += p1
                for i in range(1, len(nodes)):
                    p0, p1 = p1, stride2*p1-p0
                    out[i] += p1
                if active == 1:
                    raw = (-sq*(arb(2*((h*nodes[-1])%q))/q).cos_pi() /
                           (2*(arb(h)/q).sin_pi()**2))
                    assert raw.overlaps(p1)
            if q_top*maxfreq.denominator > maxfreq.numerator*q:
                maxfreq = Fraction(q_top, q)
        blocks.append(dict(D=D, q_max=q_max, K=Ks, contributing_denominators=active,
                           reduced_frequencies_including_conjugates=2*pairs))
        print(f"D={D}, denominators={active}, reduced frequencies={2*pairs}", flush=True)
    return out, direct_end, amplitude_l1, maxfreq, blocks


def strball(x):
    return x.str(28)


def scaled_bounds(x, scale):
    return [str((x*scale).lower().floor().unique_fmpz()),
            str((x*scale).upper().ceil().unique_fmpz())]


def run():
    started = monotonic()
    ctx.prec = 128
    L = 2**18
    prefix = int(fmpz(L**5).root(6))
    end = int(fmpz(L**101).root(100))
    start = L+prefix+1
    assert prefix**6 <= L**5 < (prefix+1)**6
    assert end**100 <= L**101 < (end+1)**100
    assert end < 2*L and end-start+1 == 2066
    p = 16
    stride = (end-start)//(p-1)
    nodes = [start+i*stride for i in range(p)]
    mu = mobius_values(end)
    a, centres = calibrated_moduli(L, mu)
    samples, endpoint, norm, freq, blocks = signed_observations(L, a, nodes, end)
    checkpoint = monotonic()
    # Real interpolation remainder is valid also over the few sites beyond the last node.
    # Every signed pair's pth derivative is bounded by |coefficient|*(2*pi*h/q)^p.
    omega = 2*arb.pi()*freq.numerator/freq.denominator
    remainder_scale = norm*omega**p/factorial(p)
    denominators = [prod(x-y for y in nodes if y != x) for x in nodes]
    interpolation_weights = [v/d for v,d in zip(samples, denominators)]
    indexed = dict(zip(nodes,samples))
    reference_sites = {start, (start+end)//2, end}
    modular_checks = {n: arb(-1)+sum((v*(n%m)*(m-n%m) for m,v in a.items()), arb(0))/2
                      for n in reference_sites}
    full_checks = {}
    H = full_H = paid_H = native_signed = complete_signed = arb(0)
    max_error = arb(0)
    signs = dict(positive=0, negative=0, unresolved=0)
    exact = increment = 0
    selected = {}
    site_digest = sha256()
    for n in range(L+1, end+1):
        # e_L(n)=sum_{L<j<=n} mu(j)(n-j) on n<2L.
        exact += increment
        increment += mu[n]
        if n < start:
            continue
        if n in indexed:
            value = indexed[n]
            err = arb(0)
        else:
            factors = [n-x for x in nodes]
            product = prod(factors)
            approx = sum((w*(product//v) for w,v in zip(interpolation_weights,factors)), arb(0))
            err = abs(product)*remainder_scale
            value = approx + arb(0, err.upper())
        if err.upper() > max_error.upper():
            max_error = err
        if n in reference_sites:
            assert modular_checks[n].contains(exact)
            full_checks[str(n)] = dict(exact=exact, modular=strball(modular_checks[n]))
            selected[str(n)] = dict(unpaid=strball(value), exact_full=exact, paid=strball(exact-value))
        if n == end:
            assert value.overlaps(endpoint)
        signs["positive" if value > 0 else "negative" if value < 0 else "unresolved"] += 1
        weight = arb(1)/n**3
        H += abs(value)*weight
        full_H += abs(exact)*weight
        paid_H += abs(exact-value)*weight
        native_signed += value
        complete_signed += exact
        site_digest.update(f"{n} {strball(value)} {exact}\n".encode("ascii"))
    level = 1/arb(L).sqrt()
    assert H > 0 and H < level and H.rad() < H.mid()/10**7
    assert sum(signs.values()) == end-start+1
    out = dict(status="BOUNDED_COMPLETE_NATIVE_WINDOW", precision_bits=ctx.prec, flint=flint.__version__,
               L=L, N=L, prefix=prefix, first=start, last=end, site_count=end-start+1,
               source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
               calibration=dict(rule="a_m=-mu(m)/m, 2<=m<=L; exact three targets 1,3,13 corrected at R,2R,4R and equally averaged over 9|R, 2L<R<=3L",
                   first=centres[0], last=centres[-1], count=len(centres), moduli=len(a), max_modulus=max(a)),
               blocks=blocks, frequencies_including_conjugates=sum(b["reduced_frequencies_including_conjugates"] for b in blocks),
               all_signed_conjugate_coefficients_L1=strball(norm), maximum_abs_frequency=str(freq),
               interpolation=dict(method="Degree 15 real Lagrange, integer nodes, derivative remainder norm*(2*pi*maxfreq)^16*|product(n-x_i)|/16!, direct independent right endpoint",
                   nodes=nodes, signed_values=[strball(v) for v in samples], maximum_site_remainder=strball(max_error),
                   signed_right_endpoint_direct=strball(endpoint), signed_site_examples=selected),
               H=strball(H), H_scaled_outward_1e25=scaled_bounds(H,10**25),
               critical_scale=strball(level), H_over_critical=strball(H/level),
               weighted_absolute_full_knot_on_same_window=strball(full_H),
               weighted_absolute_inferred_paid_on_same_window=strball(paid_H),
               unweighted_signed_unpaid_sum=strball(native_signed),
               unweighted_signed_sum_of_full_integer_knots=strball(complete_signed),
               signs_of_unpaid_response=signs, true_modulus_ramp_checks=full_checks,
               site_digest_input="One ASCII line per native n: n, signed Arb value printed with 28 digits, exact complete integer, separated by spaces.",
               site_sha256=site_digest.hexdigest(), sampling_seconds=round(checkpoint-started,2),
               total_seconds=round(monotonic()-started,2),
               scope="Fully retained signed residual at one L. The exact full knot includes every paid frequency and the zero mode, hence is a separate comparison. Finite calculations leave cofinal arithmetic upper and RH open.")
    destination = Path(__file__).resolve().with_name("NATIVE_WINDOW_CHECK.json")
    destination.write_text(json.dumps(out,indent=2)+"\n", encoding="utf8")
    print("H",out["H"],"ratio",out["H_over_critical"],"seconds",out["total_seconds"],flush=True)


if __name__ == "__main__":
    run()
