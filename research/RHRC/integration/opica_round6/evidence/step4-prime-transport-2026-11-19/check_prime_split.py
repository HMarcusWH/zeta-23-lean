"""Compare selected-node algebra with native pair enumeration and an auxiliary gcd cap."""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt
import json
from pathlib import Path


def check(x):
    top = x.bit_length() - 1
    s = isqrt(top) + (isqrt(top) ** 2 < top)
    least = list(range(x + 1))
    for p in range(2, isqrt(x) + 1):
        if least[p] == p:
            for n in range(p * p, x + 1, p):
                if least[n] == n:
                    least[n] = p
    factor = {}
    for n in range(2, x + 1):
        if n ** 100 <= x ** 99 or gcd(n, 6) > 1:
            continue
        primes = []
        rest = n
        while rest != 1:
            p = least[rest]
            primes.append(p)
            rest //= p
        if len(set(primes)) == len(primes):
            factor[n] = primes
    targets = {n for n, f in factor.items() if len(f) == 1}
    pools = {n for n, f in factor.items() if len(f) == 2 and f[0] in (5, 7, 11, 13)}
    waiting = targets.copy()
    free = pools.copy()
    selected = set()
    levels = []
    for stage in range(3):
        left = defaultdict(list)
        right = defaultdict(list)
        for bucket, labels in ((left, waiting), (right, free)):
            for n in sorted(labels):
                j = n.bit_length() - 1
                d = max(0, j - s)
                logh = (d // 2, d // 2 + (d - d // 2) // 2, d)[stage]
                bucket[j, n >> logh].append(n)
        pairs = [(p, q) for key, ps in left.items() for p, q in zip(ps, right[key])]
        for p, q in pairs:
            waiting.remove(p)
            free.remove(q)
            selected.update((p, q))
        levels.append(len(pairs))
    shift = top + max(0, top - s)
    mask_caps = (1, 13)
    assert 1 <= x - 1 < 2**100
    direct = dict.fromkeys(mask_caps, 0)
    defects = dict.fromkeys(mask_caps, 0)
    defect_counts = dict.fromkeys(mask_caps, 0)
    algebra = 0
    counts = defaultdict(lambda: [0, 0, 0])
    prior = defaultdict(list)
    for n, fs in factor.items():
        j = n.bit_length() - 1
        d = max(0, j - s)
        sg = (-1) ** len(fs)
        sel = n in selected
        base = (j, n >> d)
        for r, rg, rsel in prior[base]:
            if not (sel or rsel):
                continue
            common_levels = d - (n ^ r).bit_length() + 1
            weight = sum(1 << (shift - j - k) for k in range(common_levels))
            divisor = gcd(n, r)
            for cap in mask_caps:
                value = 2 * weight * sg * rg
                if divisor <= cap:
                    direct[cap] += value
                else:
                    defects[cap] += value
                    defect_counts[cap] += 1
        prior[base].append((n, sg, sel))
        for k in range(d + 1):
            node = counts[j, k, n >> (d - k)]
            node[0 if sel else 1] += sg
            node[2] += int(sel)
    for (j, k, _), (charge, remaining, selected_count) in counts.items():
        algebra += (charge**2 + 2 * charge * remaining - selected_count) << (shift - j - k)
    for cap in mask_caps:
        assert direct[cap] == algebra - defects[cap]
    assert defect_counts[13] == 0 and defect_counts[1] > 0
    assert all(max(fs) > (1 << max(0, n.bit_length() - 1 - s))
               for n, fs in factor.items() if n in selected)
    return {"cutoff": x, "source_labels": len(factor), "prime_targets": len(targets),
            "pairs_by_stage": levels, "remaining_prime_targets": len(waiting),
            "unmasked_signed_incidence": str(Fraction(algebra, 1 << shift)),
            "mask_comparisons": [{"cap": cap, "native_cap": cap == 1,
                                  "distinct_rejected_incident_pairs": defect_counts[cap],
                                  "direct_signed_incidence": str(Fraction(direct[cap], 1 << shift)),
                                  "signed_defect": str(Fraction(defects[cap], 1 << shift))}
                                 for cap in mask_caps]}


if __name__ == "__main__":
    script = Path(__file__)
    result = {"scope": "Exact finite native interval/signs/tree; auxiliary cofactors and matching "
                       "heights; native and auxiliary gcd caps independently compared. Does not "
                       "exercise asymptotic surplus, cutoff alignment or the all-prime theorem.",
              "script_sha256": sha256(script.read_bytes()).hexdigest(),
              "cases": [check(16384), check(32768)]}
    script.with_name("PRIME_SPLIT_CHECK.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
