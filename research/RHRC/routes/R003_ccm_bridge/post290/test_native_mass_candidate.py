"""Finite rational candidate for the actual floor-kernel mass.

This validates the arithmetic certificate only. The measure substitution,
cell integration, infinite cell decomposition and tail comparison still need
Lean proofs; no whole-kernel mass theorem is exported by this script.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json


def reciprocal_root_bounds(n, places=24):
    assert type(n) is int and n > 0
    scale = 10**places
    k = isqrt(scale * scale // n)
    lo, hi = F(k, scale), F(k + 1, scale)
    assert n * lo * lo <= 1 < n * hi * hi
    return lo, hi


def candidate(maximum=128):
    bounds = [reciprocal_root_bounds(n) for n in range(1, maximum + 2)]
    # Exact finite-cell telescoping candidate:
    # H_N=(2/3)(2N/sqrt(N+1)-sum_{n=1}^N 1/sqrt(n)).
    head_upper = F(2, 3) * (2 * maximum * bounds[-1][1] - sum(p[0] for p in bounds[:-1]))
    head_lower = F(2, 3) * (2 * maximum * bounds[-1][0] - sum(p[1] for p in bounds[:-1]))
    # Each cell above N has integral at most 1/(2*n^(3/2)).
    # The decreasing-series integral comparison gives this proposed tail cap.
    tail_upper = (1 + F(1, 2 * (maximum + 1))) * bounds[-1][1]
    total_upper = head_upper + tail_upper
    target = F(605, 621)
    assert 0 < head_lower <= head_upper < total_upper < target < 1
    # A coarser already-proved exponential envelope does not pay this margin.
    coarse_upper = head_upper + 2 * bounds[-1][1]
    assert target < coarse_upper
    # Verify the telescoping identity as exact coefficients of inverse roots,
    # independently of their enclosures and without a numerical cancellation.
    coefficients = {n: F(0) for n in range(1, maximum + 2)}
    for n in range(1, maximum + 1):
        coefficients[n] += F(2, 3) * (1 - 2*n)
        coefficients[n+1] += F(4, 3) * n
    expected = {n: -F(2, 3) for n in range(1, maximum + 1)}
    expected[maximum+1] = F(4, 3) * maximum
    assert coefficients == expected
    # A dropped endpoint term or shifted final denominator breaks the identity.
    shifted = dict(coefficients)
    shifted[maximum+1] -= F(4, 3)*maximum
    shifted[maximum] += F(4, 3)*maximum
    assert shifted != expected
    # Check all signed endpoint bounds independently as well.
    cell_total_upper = sum(F(2, 3) * ((1 - 2*n)*bounds[n-1][0] + 2*n*bounds[n][1])
                           for n in range(1, maximum + 1))
    assert head_upper <= cell_total_upper
    # All square-root comparisons stay rational; no decimal is acceptance input.
    return {
        'execution_status': 'SUCCESS', 'integrity_status': 'PASS',
        'scientific_disposition': 'FINITE_RATIONAL_MASS_CANDIDATE',
        'authority': 'FINITE_ARITHMETIC_ONLY_ANALYTIC_BRIDGE_OPEN',
        'claim_cap': 'RH_OPEN', 'native_source_id': 'UNCHANGED_CAUSAL_FLOOR_COMPLETION',
        'finite_cells': maximum, 'root_enclosures_checked': maximum + 1,
        'exact_telescoping_coefficients_checked': maximum + 1,
        'head_lower': str(head_lower), 'head_upper': str(head_upper),
        'tail_candidate_upper': str(tail_upper), 'total_candidate_upper': str(total_upper),
        'target': str(target), 'target_gap': str(target-total_upper),
        'whole_kernel_mass_lean_proved': False,
        'required_analytic_obligations': [
            'exp/log measure substitution for actual native kernel',
            'actual cell integral and finite telescoping formula',
            'countable cell integral decomposition with seam null sets',
            'per-cell and decreasing-series tail integral comparison'],
    }


if __name__ == '__main__':
    result = candidate()
    output = Path(__file__).parent / 'evidence/native_mass_candidate.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
