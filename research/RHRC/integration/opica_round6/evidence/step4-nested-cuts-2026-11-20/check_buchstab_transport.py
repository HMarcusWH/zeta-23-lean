"""Exact true-vertex control. Run with --write to create the sidecar receipt."""
import hashlib
import json
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
from math import isqrt, prod
from finite_replay import replay


def need(ok, message):
    if not ok:
        raise ValueError(message)


def prime_table(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for d in range(2, isqrt(limit) + 1):
        if sieve[d]:
            sieve[d * d::d] = bytes((limit - d * d) // d + 1)
    return sieve, [n for n in range(2, limit + 1) if sieve[n]]


def readout():
    X = 2**36 + 1
    floor_log = X.bit_length() - 1
    s = isqrt(floor_log - 1) + 1
    y = (X - 1).bit_length() ** 2
    U = 2**floor_log // 2
    H0 = U >> s
    H = 2**17
    lo = 2 * U - H0
    hi = lo + H - 1
    need(lo % H0 == 0 and lo ** 100 > X ** 99 and hi <= X, "native cell")
    z = 1800
    cap = 2_400_000
    flags, primes = prime_table(2**20)
    bound_idx = bisect_right(primes, isqrt(hi))

    residuals = list(range(lo, hi + 1))
    factors = [[] for _ in residuals]
    for p in primes[:bound_idx]:
        for i in range((-lo) % p, H, p):
            value = residuals[i]
            while value % p == 0:
                factors[i].append(p)
                value //= p
            residuals[i] = value
    rows = []
    for i, fs in enumerate(factors):
        if residuals[i] > 1:
            fs.append(residuals[i])
        need(prod(fs) == lo + i, "factorization")
        if fs[0] > y and len(set(fs)) == len(fs):
            rows.append((lo + i, tuple(fs), (-1) ** len(fs)))

    def is_prime(n):
        if n < len(flags):
            return bool(flags[n])
        for p in primes:
            if p * p > n:
                return True
            if n % p == 0:
                return False
        raise ValueError("prime table exhausted")

    @lru_cache(maxsize=65536)
    def prime_count(a, b):
        a = max(2, a)
        if b < a:
            return 0
        if b < len(flags):
            return bisect_right(primes, b) - bisect_left(primes, a)
        if b - a < 128:
            return sum(is_prime(n) for n in range(a, b + 1))
        local = bytearray(b"\x01") * (b - a + 1)
        for p in primes:
            if p * p > b:
                break
            start = max(p * p, ((a + p - 1) // p) * p) - a
            if start < len(local):
                local[start::p] = bytes((len(local) - 1 - start) // p + 1)
        return sum(local)

    @lru_cache(maxsize=65536)
    def buchstab(a, b, p0):
        """Signed count on the closed integer interval, min prime strictly > p0."""
        if a > b:
            return 0
        value = int(a <= 1 <= b) - prime_count(max(a, p0 + 1), b)
        for i in range(bisect_right(primes, p0), bisect_right(primes, isqrt(b))):
            p = primes[i]
            low, high = max(p + 1, (a + p - 1) // p), b // p
            if low <= high:
                value -= buchstab(low, high, p)
        return value

    marks = primes[bisect_right(primes, y):bisect_right(primes, z)]
    capped = Counter()
    uncapped = Counter()
    angular = Counter()
    witnesses = {}
    for n, fs, sign in rows:
        small = [p for p in fs if p <= z]
        large = [p for p in fs if p > z]
        k = len(small)
        uncapped[k] += sign
        if prod(small) <= cap:
            capped[k] += sign
        if k < 2 and len(large) in (1, 2):
            # Fixed relative 3/10 < log p_1/log m < 49/100.
            if len(large) == 2:
                m = prod(large)
                if not (large[0]**10 > m**3 and large[0]**100 < m**49):
                    continue
            key = (k, len(large))
            angular[key] += 1
            witnesses.setdefault(key, [n, list(fs), sign])

    def signed_by_mark(d, k):
        a, b = (lo + d - 1) // d, hi // d
        return (-1) ** k * buchstab(a, b, z)

    recursive = Counter({0: signed_by_mark(1, 0)})
    for i, p in enumerate(marks):
        recursive[1] += signed_by_mark(p, 1)
        for q in marks[i + 1:]:
            if p * q <= cap:
                recursive[2] += signed_by_mark(p * q, 2)
    need(marks[0]**3 > cap and recursive == capped, "signed capped recursion")
    crossed = [(n, fs, s) for n, fs, s in rows if prod(p for p in fs if p <= z) > cap]
    need(crossed and sum(s for _, _, s in crossed) == sum(uncapped.values()) - sum(capped.values()),
         "actual labels outside product cap")
    all_charge = sum(sign for _, _, sign in rows)
    need(buchstab(lo, hi, y) == all_charge == sum(uncapped.values()), "full recursion")

    def angular_for_d(d):
        a, b = (lo + d - 1) // d, hi // d
        two = 0
        for i in range(bisect_right(primes, z), bisect_right(primes, isqrt(b))):
            p = primes[i]
            # For m=pq, the two strict shares become q^3 < p^7, q^49 > p^51.
            low = max(p + 1, (a + p - 1) // p)
            high = b // p
            if low > high:
                continue
            p7, p51 = p**7, p**51
            if low**3 >= p7 or high**49 <= p51:
                continue
            if high**3 < p7 and low**49 > p51:
                two += prime_count(low, high)
            else:
                two += sum(is_prime(q) and q**3 < p7 and q**49 > p51
                           for q in range(low, high + 1))
        return prime_count(max(z + 1, a), b), two

    cross = Counter()
    for d in [1, *marks]:
        one, two = angular_for_d(d)
        cross[(int(d != 1), 1)] += one
        cross[(int(d != 1), 2)] += two
    need(angular == cross and len(witnesses) == 4, "angular source replay")

    # Match every one-mark vertex, including all its unrestricted macro orders.
    one_mark = {n for n, fs, sign in rows if sum(p <= z for p in fs) == 1}
    target = {s: [n for n, fs, sign in rows if sign == s and n in one_mark]
              for s in (-1, 1)}
    rest = {s: [n for n, fs, sign in rows if sign == s and n not in one_mark]
            for s in (-1, 1)}
    pairs = []
    for sign in (-1, 1):
        need(len(rest[-sign]) >= len(target[sign]), "partner supply")
        pairs.extend(zip(target[sign], rest[-sign]))
    endpoints = {n for pair in pairs for n in pair}
    need(len(endpoints) == 2 * len(one_mark), "unique opposite partners")
    donated = endpoints - one_mark
    donor_charge = sum(s for n, fs, s in rows if n in donated)
    survivor_charge = sum(s for n, fs, s in rows if n not in endpoints)
    need(donor_charge == -uncapped[1] and survivor_charge == all_charge, "complete endpoint charge")
    angular_charge = sum((-1)**(k+r) * count for (k, r), count in angular.items())
    def in_angular_union(fs):
        a = [p for p in fs if p > z]
        if len(fs) - len(a) > 1:
            return False
        if len(a) == 1:
            return True
        return len(a) == 2 and a[0]**10 > prod(a)**3 and a[0]**100 < prod(a)**49

    chosen = {n for n, fs, s in rows if in_angular_union(fs)}
    complement = sum(s for n, fs, s in rows if n not in chosen)
    need(angular_charge + complement == all_charge, "angular plus actual complement")
    return {
        "source_head": "a6a001fd570cd7cf9b97fdad59e373760a3153ec",
        "source_tree": "f58c4c2b7870d54302cd3ae80f7d77c1eaa6784e",
        "native": {"X": X, "U": U, "y": y, "s": s, "H0": H0, "closed_node": [lo, hi],
                   "node_length": H, "weight": f"1/{U*(H0//H)}",
                   "scope": "Unclipped descendant in the retained part of one finite shell."},
        "auxiliary": {"mark_interval_open_closed": [y, z], "marked_cap": cap,
                      "mark_prime_count": len(marks), "log_share_strict": ["3/10","49/100"],
                      "scope": "Finite mark window, cofactor 1, two angular orders and local pairing. The asymptotic harmonic-mass-one and survivor selectors are separate."},
        "full": {"source_vertices": len(rows), "signed": all_charge,
                 "positive": sum(s > 0 for _, _, s in rows), "negative": sum(s < 0 for _, _, s in rows)},
        "signed_by_mark_count_uncapped": dict(sorted(uncapped.items())),
        "signed_by_mark_count_capped_replayed": dict(sorted(recursive.items())),
        "outside_cap": {"labels": len(crossed), "signed": sum(s for _, _, s in crossed),
                        "example_n_prime_factors_sign": crossed[0]},
        "angular": {"cells": [{"small_count": k,"large_count": r,"population": c,
                              "signed": (-1)**(k+r)*c,"example_n_prime_factors_sign": witnesses[k,r]}
                             for (k,r), c in sorted(angular.items())],
                    "signed_union": angular_charge, "signed_complete_complement": complement},
        "actual_finite_matching": {"target_count": len(one_mark), "signed_target": uncapped[1],
                                  "spent_count": len(donated), "signed_spent": donor_charge,
                                  "signed_surviving": survivor_charge, "first_three_pairs": pairs[:3],
                                  "all_pairs_sha256": hashlib.sha256(json.dumps(pairs,separators=(",",":")).encode()).hexdigest()},
        "status": "EXACT_FINITE_CONTROL",
    }


if __name__ == "__main__":
    replay("BUCHSTAB_TRANSPORT_CHECK.json", readout)
