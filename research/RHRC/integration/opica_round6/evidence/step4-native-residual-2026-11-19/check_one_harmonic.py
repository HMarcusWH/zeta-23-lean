"""Evaluate the two conjugate native graph frequencies at one exact integer site."""

from array import array
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path

import flint
from flint import arb, ctx, fmpz


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = bytes((limit - start) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def mobius_segment(first, last, primes):
    remaining = array("I", range(first, last + 1))
    mu = array("b", [1]) * len(remaining)
    for p in primes:
        if p * p > last:
            break
        for i in range((-first) % p, len(remaining), p):
            remaining[i] //= p
            mu[i] = -mu[i] if remaining[i] % p else 0
    for i, cofactor in enumerate(remaining):
        if cofactor > 1:
            mu[i] = -mu[i]
    return mu


def main():
    cutoff = 2**26
    n = (21 * cutoff) // 20
    first = (24 * cutoff) // 25 + 1
    last = cutoff
    segment_length = 65536
    ctx.prec = 128
    width = int(fmpz(cutoff**5).root(6))
    upper_site = int(fmpz(cutoff**101).root(100))
    assert width**6 <= cutoff**5 < (width + 1)**6
    assert upper_site**100 <= cutoff**101 < (upper_site + 1)**100
    assert cutoff + width < n <= upper_site and cutoff < n <= 2 * cutoff
    assert last < n and 8 * n < 9 * first
    assert 2 * first > cutoff and 9 * first > 3 * cutoff
    calibration_count = (3 * cutoff) // 9 - (2 * cutoff) // 9
    assert calibration_count > 0

    primes = primes_through(isqrt(last))
    counts = {-1: 0, 0: 0, 1: 0}
    excluded = 0
    digest = sha256()
    positive = arb(0)
    negative = arb(0)
    direct_sum = arb(0)
    dyadic_scales = set()
    for start in range(first, last + 1, segment_length):
        end = min(last, start + segment_length - 1)
        signs = mobius_segment(start, end, primes)
        digest.update(signs.tobytes())
        for i, sign in enumerate(signs):
            q = start + i
            if gcd(q, 6) != 1:
                excluded += 1
                continue
            # Independently check every eligible sign, including every square divisor.
            if sign != int(fmpz(q).moebius_mu()):
                raise ArithmeticError(f"Incorrect Mobius coefficient for {q}")
            counts[sign] += 1
            denominator_scale = 1 << (q.bit_length() - 1)
            dyadic_scales.add(denominator_scale)
            if sign == 0:
                continue
            # Periodicity removes one exact turn. cos_pi and sin_pi enclose pi.
            cosine = (arb(2 * (n - q)) / q).cos_pi()
            sine = (arb(1) / q).sin_pi()
            weight = cosine / (2 * q * sine**2)
            if not weight > 0:
                raise ArithmeticError(f"Undecided sign of the native weight at {q}")
            if sign > 0:
                positive += weight
                direct_sum += weight
            else:
                negative += weight
                direct_sum -= weight

    for scale in dyadic_scales:
        assert scale**5 * cutoff > cutoff**5
        assert scale**4 * cutoff > cutoff**4
    eligible_expected = sum(
        (last - residue) // 6 - (first - 1 - residue) // 6 for residue in (1, 5)
    )
    assert sum(counts.values()) == eligible_expected
    assert eligible_expected + excluded == last - first + 1
    regrouped = positive - negative
    assert direct_sum.overlaps(regrouped)
    assert direct_sum.rel_accuracy_bits() > 65

    def ball(value):
        encoded = value.str(30, radius=True)
        if not arb(encoded).contains(value):
            raise ArithmeticError("Decimal ball failed outward-rounding check")
        return encoded

    data = {
        "scope": "Complete finite native h=1 and conjugate row on the specified denominators at one cutoff",
        "cutoff_L": cutoff,
        "site_floor_21L_over_20": n,
        "last_prepaid_site_L_plus_floor_L_to_5_over_6": cutoff + width,
        "last_native_site_floor_L_to_101_over_100": upper_site,
        "first_q_strictly_above_24L_over_25": first,
        "last_q": last,
        "site_dyadic_scale_N": cutoff,
        "unpaid_denominator_dyadic_scales": sorted(dyadic_scales),
        "number_of_allowed_R_divisible_by_9_in_2L_to_3L": calibration_count,
        "divisor_weight": "S_q=-mu(q)/q; q> L/2, gcd(q,6)=1 and 9q>3L exclude all corrections",
        "conjugate_pair": "mu(q)*cos(2*pi*n/q)/(2*q*sin(pi/q)^2)",
        "total_denominators_in_interval": last - first + 1,
        "excluded_non_coprime_to_6": excluded,
        "eligible_all_crosschecked_against_FLINT_moebius_mu": eligible_expected,
        "eligible_mu_plus_one": counts[1],
        "eligible_mu_minus_one": counts[-1],
        "eligible_mu_zero": counts[0],
        "eligible_summatory_mu": counts[1] - counts[-1],
        "positive_contribution": ball(positive),
        "negative_contribution_magnitude": ball(negative),
        "signed_row_direct_order": ball(direct_sum),
        "signed_row_after_positive_minus_negative": ball(regrouped),
        "absolute_contribution": ball(positive + negative),
        "signed_row_divided_by_L_to_3_over_2": ball(direct_sum / (arb(cutoff) * arb(cutoff).sqrt())),
        "interval_format": "python-flint Arb decimal ball with radius, outward enclosure checked by parsing",
        "arb_precision_bits": ctx.prec,
        "python_flint_version": flint.__version__,
        "max_segment_entries": segment_length,
        "all_mu_signed_bytes_sha256_in_ascending_q_order_including_excluded": digest.hexdigest(),
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "qualification": "Finite arithmetic calculation. The eventual one-sided bound, Step 4 and RH remain open.",
    }
    path = Path(__file__).with_name("ONE_HARMONIC_CHECK.json")
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(data["eligible_all_crosschecked_against_FLINT_moebius_mu"], data["signed_row_direct_order"])


if __name__ == "__main__":
    main()
