"""Exact rational checks for the constants in BANDLIMITED_THETA.md.

The analytic identities, published zero sum and finite-height verification
are inputs. No zeta zeros or primes are certified by this constants check.
"""
from fractions import Fraction as F
from math import factorial


def main():
    height_min = 10**12
    cutoff_ratio = 1000
    tail_coefficient = 24
    lost_mass = F(2 * tail_coefficient * cutoff_ratio**3, 3 * height_min**3)
    inverse_mass = 1 / (1 - lost_mass)

    # exp(r) <= 1/(1-r), 0 <= r < 1.  Use |y/H| <= 1/1000.
    exp2 = 1 / (1 - F(2, 1000))
    exp15 = 1 / (1 - F(3, 2000))
    assert exp2 * inverse_mass < F(10021, 10000)
    assert exp15 < F(10016, 10000)
    assert F(64, 9) * F(22, 7) < tail_coefficient

    # Bound after cancelling the degree-two polynomial above cutoff height.
    tail_poly = (16 * cutoff_ratio**3 + 48 * cutoff_ratio**2 + 96 * cutoff_ratio)
    remainder_scale = F(8, 6) * exp2
    assert inverse_mass * (tail_poly + remainder_scale * 343) < 17_000_000_000
    assert inverse_mass * remainder_scale * 48 < 100

    # The total two-sided sum over 1/gamma^2 is < .04621.
    zero_sum = F(4621, 100000)
    low = zero_sum * F(10016, 10000)
    # log(H)/H decreases for H >= 10^12, and log(10^12) < 28.
    assert sum(F(28**k, factorial(k)) for k in range(60)) > height_min
    high_scale = F(17_000_000_000 + 100 * 28, height_min)
    power_bias = F(2, 3) * F(98, 100)
    finite_constants = F(900, 10**28)  # x >= 10^19
    assert 6 + power_bias * 121 * 11 < 900

    for sqrt_x_over_h2, margin in [(F(11, 90), F(2, 1000)), (F(1, 9), F(56, 1000))]:
        jensen = F(10021, 10000) * F(22, 7)**2 * sqrt_x_over_h2 / 2
        high = zero_sum * sqrt_x_over_h2 * high_scale
        available = power_bias - jensen - low - high - finite_constants
        assert available > margin
        print("sqrt(x)/H^2 <=", sqrt_x_over_h2, "certified margin >", margin)
    assert F(11, 90)**2 * (3 * 10**12)**4 == 121 * 10**46
    assert F(1, 9)**2 * (3 * 10**12)**4 == 10**48


if __name__ == "__main__":
    main()
