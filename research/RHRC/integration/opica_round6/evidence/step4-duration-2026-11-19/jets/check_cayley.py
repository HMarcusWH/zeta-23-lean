"""Exact scalar checks and bounded Arb samples of the actual modulated coefficients."""

import json
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def sample(n):
    ctx.cap = n + 3
    tau = 1 / arb(n + 1).root(3)
    center = acb(1, tau)
    z = acb_series([center, 1])
    zeta = (z + arb(1) / 2).zeta()
    scale = 1 / arb(4096)
    # Variance of the sum of centered uniform boxes of halfwidth s/[m(m+1)].
    variance = scale**2 * (arb.pi()**2 / 3 - 3) / 3
    source_series = []
    for k in range(n + 1):
        midpoint = acb(0)
        for ell, moment in [(0, arb(1)), (2, variance)]:
            if ell >= k:
                midpoint += center**(ell - k) * moment / (factorial(k) * factorial(ell - k))
        r = max(0, 4 - k)
        # The actual even unit-mass seed is supported in [-s,s].
        # Its source Taylor coefficients through total order three are included above.
        error = (abs(center) * scale).exp() * scale**k * (abs(center) * scale)**r
        error /= factorial(k) * factorial(r)
        box = arb(0, error.upper())
        source_series.append(midpoint + acb(box, box))
    seed = acb_series(source_series)
    F = -((z*z - arb(1)/4)**2) * seed * zeta.derivative() / zeta
    answer = arb(2).sqrt() * sum((2**k * comb(n, k) * F[k] for k in range(n + 1)), acb(0))
    return answer


def main():
    ctx.prec = 160
    height = 3 * 10**12
    end = 648 * 10**27
    ceiling = Q(374, 1000)
    gain = 2 * ceiling * end / (height - 1)**2
    assert gain < 53857
    # 256*delta * (g/(g-1))^2 < 128 throughout the unverified range.
    assert 256 * ceiling * Q(height, height - 1)**2 < 128
    m = 1732050
    assert sum(Q(16)**k / factorial(k) for k in range(20)) > m + 2
    assert 15 * 16 < Q(m, 128) and Q(15, m + 2) < Q(1, 128)
    # The amplified bin sum costs < 2*9000*65*e^(-m/64) < 1.
    assert m // 64 > 22 and 2**22 > 2 * 9000 * 65
    # 1/2^19 * (2/2^20)^(-1/4) > 1/2^21 + 1/2^17 (compare fourth powers).
    a = Q(1, 2**20)
    assert Q(1, 2**19)**4 > 2*a*(a/2+Q(1, 2**17))**4
    assert sum(Q(20, 9)**k / factorial(k) for k in range(7)) > 8
    vals = [sample(n) for n in range(19)]
    rows = [{'order': n, 'real': v.real.str(14), 'imaginary': v.imag.str(14),
             'absolute_value': abs(v).str(14)} for n,v in enumerate(vals)]
    decreases = [n for n in range(1, len(vals)-1) if
                 (1+abs(vals[n+1]))/(n+1) < (1+abs(vals[n]))/n]
    assert decreases
    receipt = {
        'status': 'PASS_PAPER_SCALAR_ENDPOINTS_AND_ARB_SAMPLE',
        'method': 'Exact rational endpoint inequalities; 160-bit Arb Taylor series of the actual logarithmic derivative with a rigorous native seed moment remainder.',
        'inclusive_orders_with_finite_source_bound': [0, end],
        'number_of_orders': end + 1,
        'upper_bound_on_log_gain_at_endpoint': str(gain),
        'lower_bound_on_unspent_log_tail': str(53890 - gain),
        'samples': rows,
        'strict_adjacent_decrease_verified_at_n_for_full_coefficient': decreases,
        'closure': 'OPEN; no independent arithmetic upper at unbounded orders.'
    }
    Path(__file__).with_name('CAYLEY_CHECK.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
