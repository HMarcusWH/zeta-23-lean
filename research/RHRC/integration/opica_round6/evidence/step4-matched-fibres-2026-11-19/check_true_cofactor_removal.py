"""True finite factorial/eta labels, with all ordinary-prime cofactors included."""
from bisect import bisect_right
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from hashlib import sha256
import json
from math import isqrt, prod
from pathlib import Path


UNITS = 10**30


def least_factors(n):
    factors = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if factors[p] == p:
            for m in range(p*p, n + 1, p):
                if factors[m] == m:
                    factors[m] = p
    return factors


def subset_divisors(primes):
    terms = [(1, 1)]
    for p in primes:
        terms += [(d*p, -mu) for d, mu in terms]
    return terms


def prefix(data):
    counts, moments = [0], [0]
    for n, r in data:
        counts.append(counts[-1] + r)
        moments.append(moments[-1] + n*r)
    return counts, moments


def magnitude(x, p, pref, k):
    counts, moments = pref
    return x*counts[k] - p*moments[k]


def interval_log(p):
    # Decimal.ln is correctly rounded, including when the final digit is a tie.
    with localcontext() as ctx:
        ctx.prec = 72
        v = Decimal(p).ln()
        lo = int((v.next_minus()*UNITS).to_integral_value(rounding=ROUND_FLOOR))
        hi = int((v.next_plus()*UNITS).to_integral_value(rounding=ROUND_CEILING))
    assert hi - lo <= 2
    return lo, hi


def dataset(x, l1, l2):
    # This finite-control constructor accepts explicit cutoffs; the asymptotic
    # source theorem separately prescribes growth relations between them and x.
    assert min(l1, l2) >= 9
    spf = least_factors(x//2)
    primes = [p for p in range(2, len(spf)) if spf[p] == p]
    low_log, high_log = interval_log(2*l1)
    lower_threshold = x**3 * UNITS**8
    def above_lower(p):
        low = (p*l1)**4 * low_log**8
        high = (p*l1)**4 * high_log**8
        assert low > lower_threshold or high < lower_threshold
        return low > lower_threshold
    fac = [p for p in primes if p*(l1+1) < x and above_lower(p)]
    eta = [p for p in primes if p*(l2+1) < x and p**40 > x]
    return [check_list(x, "factorial", l1, fac, spf),
            check_list(x, "eta", l2, eta, spf)]


def check_list(x, name, cutoff, outers, spf):
    assert outers
    maximum = (x-1)//outers[0]
    bases = list(range(9*((2*cutoff)//9 + 1), 3*cutoff+1, 9))
    assert bases and all(2*cutoff < v <= 3*cutoff for v in bases)
    # The distributed real moment coefficients are carried at these nodes;
    # none can divide a squarefree integer. On all tested indices H(d)=1
    # and the inverse coefficient is mu(d) for BOTH factorial and eta symbols.
    nodes = sorted({r*4**i for r in bases for i in range(4)})
    prime_rows, composite_rows = [], []
    balanced_rows = {}
    prime_scan = squarefree_tests = semis = triples = 0
    for n in range(2, maximum + 1):
        m, factors = n, []
        while m > 1:
            p = spf[m]
            factors.append(p)
            m //= p
        isprime = len(factors) == 1
        prime_scan += isprime
        if n <= cutoff:
            if isprime:
                assert sum(mu for d, mu in subset_divisors(factors) if d <= cutoff) == 0
            continue
        if len(factors) > 3 or len(set(factors)) != len(factors):
            continue
        assert prod(factors) == n and n % 9 and all(n % node for node in nodes)
        squarefree_tests += 1
        r = -sum(mu for d, mu in subset_divisors(factors) if d <= cutoff)
        if len(factors) == 2 and factors[0]**200 >= n**97:
            assert r == sum(p <= cutoff for p in factors) - 1
            balanced_rows[n] = r
        if isprime:
            assert r == -1
            prime_rows.append((n, 1))
        elif r > 0:
            assert r in (1, 2)
            composite_rows.append((n, r))
            semis += len(factors) == 2
            triples += len(factors) == 3
    pj = [n for n, _ in prime_rows]
    cj = [n for n, _ in composite_rows]
    pi_pref, comp_pref = prefix(prime_rows), prefix(composite_rows)
    # An independent primality enumeration verifies the full cofactor mask.
    assert pj == [n for n in range(cutoff + 1, maximum + 1) if spf[n] == n]

    deficit = [0, 0]
    supply = [0, 0]
    no_local_supply = []
    logs, fibre_data = {}, []
    prime_labels = composite_labels = 0
    for p in outers:
        cap = (x-1)//p  # zero terminal ramps omitted everywhere
        np, nc = bisect_right(pj, cap), bisect_right(cj, cap)
        wp, wc = magnitude(x, p, pi_pref, np), magnitude(x, p, comp_pref, nc)
        assert wp >= 0 and wc >= 0
        lo, hi = logs[p] = interval_log(p)
        for bound, log in enumerate((lo, hi)):
            deficit[bound] += wp*log
            supply[bound] += wc*log
        prime_labels += np
        composite_labels += nc
        fibre_data.append((p, nc, wc))
        if wp > wc:
            no_local_supply.append(p)

    selected_labels, selected_lo, selected_hi = 0, 0, 0
    crossing = None
    manifest = sha256()
    if supply[0] >= deficit[1]:
        for p, nc, wc in fibre_data:
            lo, hi = logs[p]
            keep = nc
            if selected_lo + wc*lo >= deficit[1]:
                left, right = 0, nc
                while left < right:
                    mid = (left + right)//2
                    if selected_lo + magnitude(x, p, comp_pref, mid)*lo >= deficit[1]:
                        right = mid
                    else:
                        left = mid + 1
                keep = left
                crossing = [p, cj[keep-1]] if keep else [p, None]
            manifest.update(f"{p} {keep}\n".encode("ascii"))
            mass = magnitude(x, p, comp_pref, keep)
            selected_lo += mass*lo
            selected_hi += mass*hi
            selected_labels += keep
            if crossing:
                break
    signed = [selected_lo - deficit[1], selected_hi - deficit[0]]
    if crossing:
        assert signed[0] >= 0
        assert signed[1] < (2*x*logs[max(outers)][1] + UNITS)
    def interval(v):
        return [str(Decimal(q).scaleb(-30)) for q in v]
    balanced = check_mandatory_balanced(x, pj, pi_pref, composite_rows,
                                        balanced_rows, outers, logs)
    return dict(family=name, horizon=x, cutoff=cutoff, correction_bases=bases,
                correction_nodes=nodes, outer_primes=len(outers), outer_endpoints=[outers[0], outers[-1]],
                cofactor_cap=maximum, prime_cofactors_including_zero_prefix=prime_scan,
                positive_ramp_prime_cofactor_labels=prime_labels,positive_composite_labels=composite_labels,
                squarefree_direct_divisor_evaluations=squarefree_tests,
                distinct_positive_semiprimes=semis,distinct_positive_three_prime_products=triples,
                deficit_log_interval=interval(deficit), available_log_interval=interval(supply),
                reserve_ratio_lower=str(Decimal(supply[0])/Decimal(deficit[1])),
                individually_deficient_fibres=len(no_local_supply),
                first_individually_deficient_fibres=no_local_supply[:8],
                selected_positive_labels=selected_labels, final_selected_label=crossing,
                selected_outer_prefix_manifest_sha256=manifest.hexdigest() if crossing else None,
                full_signed_after_selection_interval=interval(signed) if crossing else None,
                all_positive_ramp_prime_cofactor_labels_included=True,
                aggregate_payment_passed=bool(crossing),
                also_keep_all_balanced_squarefree_semiprimes=balanced)


def check_mandatory_balanced(x, pj, primes_pref, composites, balanced, outers, logs):
    indices = sorted(balanced)
    signed_pref = prefix([(n, balanced[n]) for n in indices])
    remaining = [(n, r) for n, r in composites if n not in balanced]
    remain_indices = [n for n, _ in remaining]
    remain_pref = prefix(remaining)
    fixed_lo = fixed_hi = reserve_lo = reserve_hi = 0
    mandatory_labels = optional_labels = 0
    active = []
    for p in outers:
        cap = (x-1)//p
        count = bisect_right(indices, cap)
        fixed = (magnitude(x, p, signed_pref, count)
                 - magnitude(x, p, primes_pref, bisect_right(pj, cap)))
        mandatory_labels += count
        k = bisect_right(remain_indices, cap)
        optional_labels += k
        pool = magnitude(x, p, remain_pref, k)
        lo, hi = logs[p]
        fixed_lo += min(lo*fixed, hi*fixed)
        fixed_hi += max(lo*fixed, hi*fixed)
        reserve_lo += lo*pool
        reserve_hi += hi*pool
        active.append((p, k, pool))
    assert fixed_hi < 0
    sufficient = reserve_lo >= -fixed_lo
    selected = 0
    if sufficient:
        for p, k, pool in active:
            lo, hi = logs[p]
            keep = k
            last = fixed_lo + lo*pool >= 0
            if last:
                left, right = 0, k
                while left < right:
                    mid = (left+right)//2
                    if fixed_lo + lo*magnitude(x,p,remain_pref,mid) >= 0:
                        right = mid
                    else:
                        left = mid+1
                keep = left
            mass = magnitude(x, p, remain_pref, keep)
            fixed_lo += lo*mass
            fixed_hi += hi*mass
            selected += keep
            if last:
                break
        assert 0 <= fixed_lo <= fixed_hi < 2*x*logs[max(outers)][1]+UNITS
    return dict(definition="j=u*v>L, distinct primes u<v, u^200 >= j^97; all signs mandatory",
                mandatory_balanced_labels_including_zero_weights=mandatory_labels,
                optional_positive_composite_labels=optional_labels,
                optional_positive_labels_selected=selected,
                aggregate_payment_passed=sufficient,
                full_signed_after_selection_interval=[str(Decimal(z).scaleb(-30)) for z in (fixed_lo,fixed_hi)] if sufficient else None)


def main():
    with localcontext() as ctx:
        ctx.prec = 80
        cases = [row for x, l1, l2 in [(100_003, 20, 91), (200_003, 31, 121),
                                       (300_007, 41, 160), (300_007, 89, 160)]
                 for row in dataset(x, l1, l2)]
    result = dict(scope="Bounded native arithmetic with explicit finite cutoffs. No asymptotic theorem, CI or Step 4 closure.",
                  precision="All row and Möbius sums exact integers; 72-digit correctly rounded log enclosure, then scaled outward to 30 decimal places. Final enclosure endpoints use integers.",
                  selector="All active prime cofactors against squarefree positive 2/3-factor prefixes ordered by (outer prime, cofactor). Stop at the first rigorous upper crossing.",
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), cases=cases)
    out = Path(__file__).with_name("TRUE_COFACTOR_REMOVAL_CHECK.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf8")
    for row in cases:
        print(row["family"], row["horizon"], row["cutoff"], row["reserve_ratio_lower"],
              row["positive_ramp_prime_cofactor_labels"], row["aggregate_payment_passed"])
    # Deliberately retain both genuinely insufficient finite factorial pools.
    assert [r["aggregate_payment_passed"] for r in cases] == [
        False, True, True, True, False, True, True, True]
    return True


if __name__ == "__main__":
    raise SystemExit(0 if main() else 1)
