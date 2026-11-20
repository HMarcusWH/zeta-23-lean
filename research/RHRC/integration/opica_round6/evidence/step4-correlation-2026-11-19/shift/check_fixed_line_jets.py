"""Check the scalar endpoints in FIXED_LINE_JETS.md using exact rationals."""

import hashlib
import json
from fractions import Fraction as Q
from math import factorial
from pathlib import Path


def exp_lower(x, order):
    return sum(x**j / factorial(j) for j in range(order + 1))


root = Path(__file__).resolve().parent
k_start, k_end = 50000, 115000
exponent = Q(937, 2000)
exp_floor = exp_lower(exponent, 8)
jet_margin = Q(53890) - exponent * (Q(k_end) + Q(1, 2))

assert exp_floor > Q(500, 313) and jet_margin > 0
assert (10**31 + 1)**2 < 10**63
# For k >= 50000, sqrt(k)/4 - 2 log(2k) - 1 increases since sqrt(k) > 16.
assert exp_lower(Q(12), 20) > 2 * k_start
assert (4 * (2 * 12 + 1))**2 < k_start
# log k > 8 and log 2 < 1, using 2 < e < 3.
assert 3**8 < k_start and 2 + 1 < Q(2, 5) * 8
# Chebyshev interval length bound, disjoint-window density and signed margin.
assert 4 * (2 * k_start + 1) <= 9 * k_start
assert Q(3, 4) * Q(5, 6) == Q(5, 8)
diag = Q(5, 96) * 10**72
assert diag > Q(10**72, 24) and diag - 10**63 > 10**70
first_bin = 1732050
assert exp_lower(Q(16), 19) > first_bin + 2
assert Q(first_bin, 1056) - 17 * 16 - Q(1, 33) > 0
assert Q(1, 1056) > Q(17, first_bin + 2)
assert 33 * exponent * (k_start + Q(1, 2)) < 16 * k_start
assert 33 * exponent < 16

parents = [root.parent / name for name in (
    'FIXED_SIEVE_SIGN.md', 'FIXED_SIEVE_CONSTANTS.json', 'ALL_HORIZON_DIAGONAL.md'
)]
receipt = {
    'status': 'EXACT_SCALAR_CHECKS_PASS',
    'scope': 'Rational endpoint arithmetic for the local paper proof, using the cited upstream bounds.',
    'all_time_squared_prime_field_derivative_orders_below_10_to_63': [0, k_end],
    'number_of_such_orders': k_end + 1,
    'signed_jet_orders_below_minus_10_to_70': [k_start, k_end],
    'number_of_signed_orders': k_end - k_start + 1,
    'exponential_tail_log_margin_at_largest_order': str(jet_margin),
    'comparison_taylor_sum_minus_500_over_313': str(exp_floor - Q(500, 313)),
    'diagonal_lower_all_integer_orders_from': k_start,
    'diagonal_lower_bound': str(diag),
    'contrary_sign_implies_one_zero_in_ordinate_range': '3e12 < |Im rho| < (16 k)^2',
    'supporting_file_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in parents},
    'cofinal_upper_proved': False,
}
print(json.dumps(receipt, indent=2))
if __name__ == '__main__':
    (root / 'FIXED_LINE_JET_CHECK.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
