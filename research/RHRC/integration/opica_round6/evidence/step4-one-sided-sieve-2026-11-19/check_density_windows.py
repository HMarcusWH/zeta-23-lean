"""Bound the total log width of the positive zero cancelers at two fixed abscissas."""

from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx


def ball(value):
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def bound(abscissa, packet_factor):
    sigma = ball(abscissa)
    height = arb(3 * 10**12)
    logarithm = height.log()
    decay = (2 * sigma - 1) / (2 - sigma)
    log_power = (7 - 5 * sigma) / (2 - sigma)
    effective_decay = decay - log_power / logarithm
    if not effective_decay > 0:
        raise ArithmeticError("the log-power integral requires positive decay")
    if not (sigma >= ball("0.78125") and sigma <= ball("0.81250")):
        raise ValueError("abscissa is outside the cited table row")
    first = ball("17.21") * height ** (-decay) * logarithm ** log_power / effective_decay
    second = ball("6.826") * (logarithm**2 + 2 * logarithm + 2) / height
    third = ball("121.1") * (logarithm + 1) / height
    width_bound = arb.pi() * (first + second + third)
    period_bound = 2 * arb.pi() / height
    room = ball(packet_factor).log() - width_bound - period_bound
    if not room > ball("0.001"):
        raise ArithmeticError("insufficient room for the period, smoothing and margins")
    return {
        "abscissa": abscissa,
        "packet_factor": packet_factor,
        "upper_bound_on_canceler_width": str(width_bound),
        "upper_bound_on_single_period": str(period_bound),
        "remaining_log_width": str(room),
        "remaining_log_width_provably_exceeds": "0.001",
    }


if __name__ == "__main__":
    ctx.prec = 160
    receipt = {
        "scope": "Directed Arb bounds on the cited density integral only",
        "density_input": "https://arxiv.org/html/2507.15184v2#S1",
        "verified_height_input": "https://arxiv.org/abs/2004.09765",
        "height": 3000000000000,
        "precision_bits": ctx.prec,
        "results": [bound("0.79", "2"), bound("0.80", "7/5")],
    }
    path = Path(__file__).with_name("DENSITY_WINDOWS_CHECK.json")
    path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
