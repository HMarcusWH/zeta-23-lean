"""Compare the primitive-direction expansion and the Euler product in the actual passband."""
import json
from math import isqrt, prod
from pathlib import Path
from flint import arb, ctx


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def directions(primes):
    # a and b have disjoint support. Omission includes all allowed common divisors.
    items = [(1, 1, arb(1))]
    for q in primes:
        local = -arb(q).sqrt() / (q + 1)
        items = (items + [(a * q, b, weight * local) for a, b, weight in items]
                 + [(a, b * q, weight * local) for a, b, weight in items])
    assert len(items) == 3 ** len(primes)
    assert sum(a * b == 1 for a, b, _ in items) == 1
    return items


def main():
    ctx.prec = 190
    primes = []
    q = 10**7
    while len(primes) < 8:
        q += 1
        if prime(q):
            primes.append(q)
    items = directions(primes)
    rows = []
    for shift in (0, 1, 2, 3, 5, 8, 13, 21):
        xi = arb(3 * 10**12) + arb(shift) / 16
        v = 2 * arb(10**6) / (1 + xi * xi)
        assert v < arb(227) / 10**21
        expanded = sum(w * (xi * (arb(a) / b).log()).cos() for a, b, w in items)
        factored = prod(1 - 2 * arb(q).sqrt() / (q + 1) * (xi * arb(q).log()).cos()
                        for q in primes)
        assert expanded.overlaps(factored) and factored > 0
        assert factored > 1 or factored < 1
        rows.append(dict(frequency="3000000000000+" + str(shift) + "/16",
                         multiplier=str(factored), expanded=str(expanded),
                         above_diagonal=bool(factored > 1)))
    assert {row["above_diagonal"] for row in rows} == {True, False}
    result = dict(qualification="Finite arithmetic checks of the exact prime-pattern multiplier. "
                  "The integral against the complete source spectrum and the signed residual "
                  "at cofinal orders are separate quantities.",
                  first_primes_above_fixed_cutoff=primes, ordered_primitive_directions=len(items),
                  precision_bits=ctx.prec, evaluations=rows)
    Path(__file__).with_name("PRIMITIVE_PATTERN_CHECK.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf8")
    print(primes, len(items), "directions;",
          sum(r["above_diagonal"] for r in rows), "above diagonal of", len(rows))


if __name__ == "__main__":
    main()
