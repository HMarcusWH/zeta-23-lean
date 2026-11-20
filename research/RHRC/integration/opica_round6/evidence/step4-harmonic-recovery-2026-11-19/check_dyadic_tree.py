"""Exact terminal Möbius-tree energy and signed primitive covariance."""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path

from flint import fmpz


def root_floor(integer, exponent):
    value = int(fmpz(integer).root(exponent))
    if not value**exponent <= integer < (value + 1)**exponent:
        raise ArithmeticError("Incorrect exact root")
    return value


def native_input(x):
    first = root_floor(x**99, 100) + 1
    small_gcd = root_floor(x - 1, 100)
    j_max = x.bit_length() - 1
    s = isqrt(j_max)
    if s * s != j_max:
        s += 1
    shells = defaultdict(list)
    digest = sha256()
    counts = {"excluded_non_coprime_6": 0, "squareful_coprime_6": 0,
              "mobius_positive": 0, "mobius_negative": 0}
    for q in range(first, x + 1):
        sign = 0
        if gcd(q, 6) != 1:
            counts["excluded_non_coprime_6"] += 1
        else:
            factors = [(int(p), int(e)) for p, e in fmpz(q).factor()]
            if any(e > 1 for p, e in factors):
                counts["squareful_coprime_6"] += 1
            else:
                sign = (-1)**len(factors)
                counts["mobius_positive" if sign > 0 else "mobius_negative"] += 1
                divisors = [(1, 1)]
                for p, _ in factors:
                    divisors.extend([(d * p, -mu) for d, mu in divisors])
                shells[q.bit_length() - 1].append((q, sign, divisors))
            if sign != int(fmpz(q).moebius_mu()):
                raise ArithmeticError(f"Factor/sign mismatch at {q}")
        digest.update(bytes([sign + 1]))
    if sum(counts.values()) != x + 1 - first:
        raise ArithmeticError("Incomplete terminal inventory")
    return first, small_gcd, j_max, s, shells, counts, digest.hexdigest()


def inversion_coefficients(shells, cap):
    coefficients = {}
    for labels in shells.values():
        for _, _, divisors in labels:
            small = [(d, mu) for d, mu in divisors if d <= cap]
            for m, mu_m in divisors:
                if m not in coefficients:
                    # Each m divides a squarefree label, so mu(m/d)=mu(m)*mu(d).
                    coefficients[m] = mu_m * sum(mu for d, mu in small if m % d == 0)
    return coefficients


def tree_covariance(shells, s, denominator_shift, cap):
    coefficients = inversion_coefficients(shells, cap)
    total_energy = diagonal = primitive = unsigned_control = 0
    deep_primitive = deep_control = 0
    active_nodes = 0
    for j, labels in shells.items():
        depth = max(0, j - s)
        for k in range(depth + 1):
            previous_node = None
            signed_multiples = {}
            unsigned_multiples = {}
            node_sum = 0
            running_energy = running_primitive = running_control = 0
            for q, sign, divisors in labels:
                node = q >> (depth - k)
                if node != previous_node:
                    running_energy += node_sum**2
                    node_sum = 0
                    signed_multiples.clear()
                    unsigned_multiples.clear()
                    previous_node = node
                    active_nodes += 1
                node_sum += sign
                signed_prior = unsigned_prior = 0
                for m, _ in divisors:
                    c = coefficients[m]
                    if not c:
                        continue
                    signed_count = signed_multiples.get(m, 0)
                    count = unsigned_multiples.get(m, 0)
                    signed_prior += c * signed_count
                    unsigned_prior += c * count
                    signed_multiples[m] = signed_count + sign
                    unsigned_multiples[m] = count + 1
                running_primitive += 2 * sign * signed_prior
                running_control += 2 * unsigned_prior
            running_energy += node_sum**2
            shift = denominator_shift - j - k
            total_energy += running_energy << shift
            diagonal += len(labels) << shift
            primitive += running_primitive << shift
            unsigned_control += running_control << shift
            if 2 * k >= depth:
                deep_primitive += running_primitive << shift
                deep_control += running_control << shift
    return {
        "total_positive_energy": total_energy,
        "diagonal": diagonal,
        "strict_small_gcd_off_diagonal": primitive,
        "complement_gcd_off_diagonal": total_energy - diagonal - primitive,
        "absolute_label_control_small_gcd_off_diagonal": unsigned_control,
        "coarse_small_gcd_off_diagonal": primitive - deep_primitive,
        "deep_small_gcd_off_diagonal": deep_primitive,
        "deep_absolute_label_control_small_gcd_off_diagonal": deep_control,
    }, active_nodes


def direct_pairs(shells, s, denominator_shift, cap):
    """Independent common-ancestor computation, with gcd on each actual pair."""
    total = diagonal = primitive = control = 0
    deep_primitive = deep_control = 0
    for j, labels in shells.items():
        depth = max(0, j - s)
        for i, (q, mu, _) in enumerate(labels):
            diagonal += ((1 << (depth + 1)) - 1) << (denominator_shift - j - depth)
            for r, nu, _ in labels[i + 1:]:
                last_level = depth - (q ^ r).bit_length()
                if last_level < 0:
                    continue
                weight = ((1 << (last_level + 1)) - 1) << (denominator_shift - j - last_level)
                value = 2 * weight * mu * nu
                total += value
                if gcd(q, r) <= cap:
                    primitive += value
                    control += 2 * weight
                    first_deep_level = (depth + 1) // 2
                    if last_level >= first_deep_level:
                        num_levels = 1 + last_level - first_deep_level
                        deep_weight = ((1 << num_levels) - 1) << (denominator_shift - j - last_level)
                        deep_primitive += 2 * deep_weight * mu * nu
                        deep_control += 2 * deep_weight
    return {
        "total_positive_energy": total + diagonal,
        "diagonal": diagonal,
        "strict_small_gcd_off_diagonal": primitive,
        "complement_gcd_off_diagonal": total - primitive,
        "absolute_label_control_small_gcd_off_diagonal": control,
        "coarse_small_gcd_off_diagonal": primitive - deep_primitive,
        "deep_small_gcd_off_diagonal": deep_primitive,
        "deep_absolute_label_control_small_gcd_off_diagonal": deep_control,
    }


def evaluate(x, check_pairs=False):
    first, cap, j_max, s, shells, counts, digest = native_input(x)
    shift = j_max + max(0, j_max - s)
    numerators, nodes = tree_covariance(shells, s, shift, cap)
    if numerators["absolute_label_control_small_gcd_off_diagonal"] < abs(numerators["strict_small_gcd_off_diagonal"]):
        raise ArithmeticError("Absolute-label bound failed")
    pair_controls = []
    if check_pairs:
        for test_cap in (cap, 5, 19):
            observed, _ = tree_covariance(shells, s, shift, test_cap)
            expected = direct_pairs(shells, s, shift, test_cap)
            if observed != expected:
                raise ArithmeticError(f"Pair mismatch for X={x}, gcd cap {test_cap}")
            pair_controls.append({"largest_included_gcd": test_cap,
                                  "native": test_cap == cap, "exact_equality": True})
    return {
        "X": x, "first_terminal_q": first, "last_terminal_q": x,
        "ceil_sqrt_floor_log2_X": s, "largest_included_gcd": cap,
        "inventory": counts, "nonempty_nodes_counting_depths": nodes,
        "all_native_mu6_signed_labels_sha256_bytes_mu6_plus_one": digest,
        "common_denominator": 1 << shift, "integer_numerators": numerators,
        "reduced_rationals": {
            key: str(Fraction(n, 1 << shift)) for key, n in numerators.items()
        },
        "independent_direct_pair_controls": pair_controls,
    }


def main():
    receipt = {
        "scope": "Exact finite dyadic-tree energy and primitive signed covariance; no asymptotic or RH qualification",
        "terminal_condition": "q**100 > X**99 and q <= X",
        "primitive_condition": "gcd(q,r)**100 < X",
        "pair_weight_per_shared_node": "2/(2**j * 2**k) for unordered q<r, j shell and k within-base depth",
        "deep_level": "2*k >= max(0,j-s) inside each base",
        "false_source_control": "Replace every nonzero Mobius sign by +1; keep identical labels and primitive pair inventory",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "positive_sign_fixture_selection": "2424 was the first positive result in 2000,2053,...; it is a sign control, not an unbiased sample",
        "runs": [evaluate(2424, check_pairs=True), evaluate(2**12 + 7, check_pairs=True), evaluate(2**20)],
    }
    out = Path(__file__).with_name("DYADIC_TREE_CHECK.json")
    out.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    for row in receipt["runs"]:
        print(row["X"], row["reduced_rationals"]["strict_small_gcd_off_diagonal"])


if __name__ == "__main__":
    main()
