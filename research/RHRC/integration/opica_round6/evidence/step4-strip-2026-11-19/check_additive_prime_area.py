"""Certify uniform constants for the 64-fold additive prime-area comparison."""

import json
from pathlib import Path

import flint
from flint import arb, ctx


ctx.prec = 256


def ratio(numerator, denominator):
    return arb(numerator) / denominator


def main():
    start, stop = arb(10) ** 19, arb(10) ** 46
    height = 3 * arb(10) ** 12
    r = 64
    fourth_min = start.sqrt().sqrt()
    fourth_max = stop.sqrt().sqrt()
    relative_shift = ratio(2 * r, 5) / fourth_min
    expansion = 1 + relative_shift
    total_reciprocal = ratio(4621, 100000)

    # Brent--Platt--Trudgian, positive ordinates only in their formula.
    main_tail = ((height / (2 * arb.pi())).log() + 1) / (2 * arb.pi() * height)
    tail_error = (ratio(14, 100) + ratio(56, 100) * height.log()) / height**2
    tail = 2 * (main_tail + tail_error)
    frequency_ratio = 5 * fourth_max / height
    high = expansion ** (r + 2) * stop.sqrt() * frequency_ratio**r * tail

    # Subtracting the integrated explicit formula at 2 yields a bounded base
    # correction and a linear log(2*pi) term. This bound also covers width 2a.
    base = 4 * total_reciprocal + 1
    deterministic = (base / start + expansion * (2 * arb.pi()).log()) / start.sqrt()
    low = expansion * expansion.sqrt() * total_reciprocal
    smoothed_abs = high + low + deterministic
    variance = ratio(r, 75)
    psi_lower = -3 * smoothed_abs - variance
    psi_upper = smoothed_abs + variance / 2

    # Use Jensen for the negative power 3/2 coefficient after averaging.
    prime_power = ratio(49, 75)
    theta_upper = (
        total_reciprocal - prime_power + high + variance / 2
        + (base + prime_power * 1331) / (start * start.sqrt())
    )

    checks = {
        "support_of_double_width_is_above_121": start * (1 - relative_shift) > 121,
        "relative_shift_below_one_thousandth": relative_shift < ratio(1, 1000),
        "whole_tail_less_than_four_trillionths": tail < ratio(4, 10**12),
        "frequency_ratio_less_than_eight_fifteenths": frequency_ratio < ratio(8, 15),
        "high_zero_cost_less_than_one_thousandth": high < ratio(1, 1000),
        "absolute_smoothed_psi_cost_less_than_0_048": smoothed_abs < ratio(48, 1000),
        "raw_psi_area_above_minus_0_998": psi_lower > -ratio(998, 1000),
        "raw_psi_area_below_0_475": psi_upper < ratio(475, 1000),
        "raw_theta_area_below_minus_0_17": theta_upper < -ratio(17, 100),
    }
    if not all(checks.values()):
        raise ArithmeticError(str(checks))
    bounds = {
        "both_ordinates_tail": tail,
        "relative_support_radius_at_double_width": relative_shift,
        "largest_frequency_ratio": frequency_ratio,
        "normalized_high_zero_cost": high,
        "normalized_low_zero_cost": low,
        "normalized_absolute_deterministic_cost": deterministic,
        "normalized_smoothed_psi_absolute_bound": smoothed_abs,
        "normalized_raw_psi_lower_bound": psi_lower,
        "normalized_raw_psi_upper_bound": psi_upper,
        "normalized_raw_theta_upper_bound": theta_upper,
    }
    result = {
        "claim": "Uniform interval bounds for the constants in ADDITIVE_PRIME_AREA.md",
        "x_range_inclusive": ["10^19", "10^46"],
        "verified_zero_height_input": "3000000000000",
        "python_flint": flint.__version__,
        "precision_bits": ctx.prec,
        "checks": checks,
        "arb_parameter_enclosures": {name: str(value) for name, value in bounds.items()},
        "scope": "Analytic endpoint maximization plus interval arithmetic. The cited zero results and proper-power lower bound are inputs.",
    }
    path = Path(__file__).with_name("ADDITIVE_PRIME_AREA_CHECK.json")
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
