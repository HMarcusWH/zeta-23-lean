"""Calculate the two sign marginals and their determinant on native rough cells."""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
HORIZONS = (131093, 221189, 1049155, 1656575)


def first_terminal(x):
    lo, hi = 1, x
    limit = x ** 99
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** 100 > limit:
            hi = mid
        else:
            lo = mid + 1
    return lo


def vertex_rows(x, cofactor_cap):
    """Segment factor the whole terminal interval, retaining squarefree signs."""
    lo = first_terminal(x)
    primes = bytearray([1]) * (isqrt(x) + 1)
    primes[:2] = bytes(2)
    for p in range(2, isqrt(len(primes) - 1) + 1):
        if primes[p]:
            primes[p*p::p] = bytes(len(primes[p*p::p]))
    rest = list(range(lo, x + 1))
    signs = [1] * len(rest)
    largest = [1] * len(rest)
    y = (x - 1).bit_length() ** 2
    for p, prime in enumerate(primes):
        if not prime:
            continue
        for i in range((-lo) % p, len(rest), p):
            rest[i] //= p
            signs[i] = -signs[i] if p > y and rest[i] % p else 0
            while rest[i] % p == 0:
                rest[i] //= p
            largest[i] = p
    for i, sign in enumerate(signs):
        if not sign:
            continue
        n = lo + i
        if rest[i] > 1:
            if rest[i] <= y:
                continue
            sign = -sign
            largest[i] = rest[i]
        cone = n // largest[i] <= cofactor_cap
        b = -1 if cone else 1
        yield n, sign, cone, sign * b, b


def measure(x, cofactor_cap):
    jx = x.bit_length() - 1
    s = isqrt(jx)
    s += s * s < jx
    nodes = {}
    labels = 0
    for n, sign, cone, a, b in vertex_rows(x, cofactor_cap):
        labels += 1
        j = n.bit_length() - 1
        for k in range(j - s + 1):
            h = 1 << (j - s - k)
            key = (j, k, n // h)
            bucket = nodes.setdefault(key, [0] * 7)
            bucket[(2 if a < 0 else 0) + (1 if b < 0 else 0)] += 1
            bucket[4] += sign
            bucket[5] += sign if cone else 0
            bucket[6] += cone
    positive_energy = Fraction(0)
    raw_det_energy = Fraction(0)
    largest = None
    for (j, k, index), (p, q, r, t, f, g, count) in sorted(nodes.items()):
        n = p + q + r + t
        a = p + q - r - t
        b = p - q + r - t
        det = p*t - q*r
        if n*f - a*b != 4*det or a != f-2*g or b != n-2*count:
            raise ValueError("contingency decomposition failed")
        if 4*det - 2*g*b != 2*count*f:
            raise ValueError("complete compensated identity failed")
        if 2*k >= j-s:
            continue
        w = Fraction(1, 1 << (j+k))
        positive_energy += w * max(f, 0)**2
        raw_det_energy += w * Fraction(max(4*det, 0)**2, n*n)
        if largest is None or abs(det) > abs(largest["determinant"]):
            h = 1 << (j-s-k)
            largest = dict(cell=[index*h, (index+1)*h], counts=[p,q,r,t],
                           charge=f, cone_charge=g, determinant=det)
    return dict(horizon=x, cofactor_cap=cofactor_cap, labels=labels,
                occupied_nodes=len(nodes), max_abs_coarse_determinant_example=largest,
                positive_charge_energy=str(positive_energy),
                positive_normalized_determinant_energy=str(raw_det_energy))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    graph = json.loads((HERE/"CONSTRAINT_GRAPH.json").read_bytes())
    required = {"CONE_MATCH","ONE_POLARITY","ROUGH_TREE","CONE_CONTINGENCY"}
    if not required.issubset(graph["nodes"]) or graph["Step4"] != "OPEN":
        raise ValueError("missing constraint inputs or incorrect Step 4 status")
    results = [measure(x, cap) for x in HORIZONS for cap in (1, 1024)]
    output = dict(schema="OPICA6_CONE_PARITY_PROBE_V1", nodes=sorted(required),
                  graph_sha256=sha256((HERE/"CONSTRAINT_GRAPH.json").read_bytes()).hexdigest(),
                  scope="Finite native terminal rows and weights including clips. At these horizons floor(X^(1/1000))=1; 1024 is a separate sensitivity control. Neither is an asymptotic certificate.",
                  results=results)
    data=(json.dumps(output,indent=2,sort_keys=True)+"\n").encode()
    path=HERE/"CONE_PARITY_RESULTS.json"
    if args.write:
        path.write_bytes(data)
    elif path.read_bytes()!=data:
        raise SystemExit("stale cone parity calculation")
    print(f"Verified {len(results)} horizon/cap cases")


if __name__ == "__main__":
    main()
