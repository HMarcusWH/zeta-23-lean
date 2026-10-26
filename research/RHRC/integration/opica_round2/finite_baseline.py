"""Independent exact finite arithmetic for the frozen four-column baseline.

The rational inequalities are checked here. Their analytic interpretation and
Lean instantiation must be established separately on the actual native source.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import math
from pathlib import Path
from typing import Any, Sequence

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, parse_rational, require
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, parse_rational, require

HERE = Path(__file__).resolve().parent
BASELINE_COMMIT = "416aec21d4d6634675639b5397cc300d1f826e34"
BASELINE_TREE = "0506bca8ffe613e9cd9ab844650a1141d4494f66"
COEFFICIENTS = (Fraction(1), Fraction(-1), Fraction(-1), Fraction(-2, 3))
FIXTURE_FIELDS = {"schema", "source_commit", "source_tree", "source", "filter", "coefficients",
                  "region", "tail_start", "upper_square", "lower_square", "authority", "RH"}


def _fractions(values: Sequence[Any]) -> tuple[Fraction, ...]:
    require(type(values) in (list, tuple) and 1 <= len(values) <= 16,
            "coefficient_count", "An exact finite coefficient list of length 1..16 is required")
    result = []
    for value in values:
        if type(value) is Fraction:
            result.append(value)
        elif type(value) is int:
            result.append(Fraction(value))
        else:
            result.append(parse_rational(value))
    return tuple(result)


def period_values(coefficients: Sequence[Any]) -> tuple[Fraction, ...]:
    """Actual floor residual on its complete period; zero pole moment is required."""
    coefficients = _fractions(coefficients)
    period = math.lcm(*range(1, len(coefficients) + 1))
    require(period <= 100_000, "period_limit", "Period exceeds finite resource limit")
    require(sum((x / n for n, x in enumerate(coefficients, 1)), Fraction()) == 0,
            "pole_moment", "The proposed coefficients have nonzero pole moment")
    return tuple(Fraction(1) - sum((x * (k // n) for n, x in enumerate(coefficients, 1)),
                                  Fraction()) for k in range(period))


def periodic_energy_upper(cells: Sequence[Any], tail_start: int) -> dict[str, Fraction | int]:
    """Exact finite head plus an Abel bound for the periodic square sequence."""
    cells = _fractions(cells)
    require(type(tail_start) is int and 1 <= tail_start <= 100_000,
            "tail_start", "Finite positive integer tail start required")
    squares = tuple(x * x for x in cells)
    mean = sum(squares, Fraction()) / len(squares)
    running = Fraction()
    prefix = []
    for offset in range(len(squares)):
        running += squares[(tail_start + offset) % len(squares)] - mean
        prefix.append(running)
    require(running == 0, "period_budget", "Periodic discrepancy did not close")
    cap = max(prefix)
    head = sum((squares[k % len(squares)] / (k * (k + 1))
                for k in range(1, tail_start)), Fraction())
    upper = head + mean / tail_start + cap / (tail_start * (tail_start + 1))
    return {"period": len(cells), "mean": mean, "prefix_cap": cap,
            "head": head, "tail_upper": upper - head, "upper_square": upper}


def _fixture_identity(obj: Any) -> tuple[Fraction, ...]:
    require(type(obj) is dict and set(obj) == FIXTURE_FIELDS, "fixture_fields", "Unknown or missing baseline field")
    exact = {"schema": "OPICA2_FIXED_BASELINE_V1", "source_commit": BASELINE_COMMIT,
             "source_tree": BASELINE_TREE, "source": "original-one-copy-Q; sigma=1/4096; delay=sigma",
             "filter": "(z+3/2)/(z+1/2)^5",
             "authority": "EXACT_FINITE_ARITHMETIC_NOT_ANALYTIC_OR_LEAN", "RH": "OPEN"}
    require(all(type(obj[k]) is type(v) and obj[k] == v for k, v in exact.items()),
            "fixture_identity", "Baseline source, filter, schema or authority was substituted")
    require(type(obj["coefficients"]) is list and len(obj["coefficients"]) == 4,
            "fixture_coefficients", "Four baseline coefficients required")
    values = tuple(parse_rational(x) for x in obj["coefficients"])
    require(values == COEFFICIENTS, "fixture_coefficients", "Different trial is not this fixed baseline")
    require(obj["region"] == {"delta": ["1/4", "3/8"], "abs_tau": ["1", "2"]},
            "fixture_region", "Different fixed region")
    require(type(obj["tail_start"]) is int and obj["tail_start"] == 48,
            "fixture_tail", "Abel tail starts at the exact integer 48")
    return values


def _lower_square() -> Fraction:
    margin = 1 - Fraction(3, 8) * Fraction(1, 2048) - 2 * Fraction(1, 2048)**2
    return Fraction(4) / (2 * (4 + Fraction(49, 64))**2) * margin**2


def check_filtered_baseline(obj: Any) -> dict[str, Any]:
    """Independent checker: reconstruct all floor cells and finite rational bounds.

    It does not call period_values or periodic_energy_upper, so a producer
    implementation mistake is not automatically duplicated by the checker.
    """
    x = _fixture_identity(obj)
    require(sum((x[n - 1] / n for n in (1, 2, 3, 4)), Fraction()) == 0,
            "pole_moment", "Pole moment changed")
    cells = []
    for k in range(12):
        cells.append(Fraction(1) - x[0] * k - x[1] * (k // 2)
                     - x[2] * (k // 3) - x[3] * (k // 4))
    expected = [Fraction(n, d) for n, d in
                [(1, 1), (0, 1), (0, 1), (0, 1), (2, 3), (-1, 3),
                 (2, 3), (-1, 3), (1, 3), (1, 3), (1, 3), (-2, 3)]]
    require(cells == expected, "period", "Full 12-cell residual was not reconstructed")
    require(12 * x[0] + 6 * x[1] + 4 * x[2] + 3 * x[3] == 0,
            "period_drift", "Residual is not periodic")
    average = sum((x * x for x in cells), Fraction()) / 12
    discrepancy = Fraction()
    cap = Fraction()
    for cell in cells:
        discrepancy += cell * cell - average
        cap = max(cap, discrepancy)
    require(average == Fraction(13, 54) and cap == Fraction(41, 54) and discrepancy == 0,
            "abel_budget", "Mean or cumulative Abel budget changed")
    upper = Fraction()
    for k in range(1, 48):
        upper += cells[k % 12]**2 * (Fraction(1, k) - Fraction(1, k + 1))
    upper += Fraction(13, 54 * 48) + Fraction(41, 54 * 48 * 49)
    lower = _lower_square()
    require(parse_rational(obj["upper_square"], nonnegative=True) == upper
            and parse_rational(obj["lower_square"], nonnegative=True) == lower,
            "forged_bound", "Bounds do not equal independent rational reconstruction")
    require(upper < Fraction(17, 250) < Fraction(2, 25) < lower,
            "strict_margin", "The claimed strict finite comparison failed")
    raw = 12 * Fraction(511, 512) * 2048**3 / ((1 + 23) * (1 + 89))
    require(2047 == 23 * 89 and raw > 6900**2, "squarefree", "Squarefree arithmetic control failed")
    h = Fraction(1, 1000)
    minor = 4 * h**4 - Fraction(1, 6) * h**3
    require(minor == Fraction(-61, 375_000_000_000) < 0,
            "native_minor_budget", "Rational minor budget failed")
    return {"status": "PASS_EXACT_FINITE_ARITHMETIC", "authority": "EXACT_FINITE_ARITHMETIC",
            "fixture_source_commit": BASELINE_COMMIT, "fixture_source_tree": BASELINE_TREE,
            "fixture_sha256": canonical_sha256(obj), "upper_square": str(upper),
            "lower_square": str(lower), "gap": str(lower - upper), "mean": str(average),
            "prefix_cap": str(cap), "raw_lower_square": str(raw),
            "native_gain_minor_upper": str(minor), "analytic_dependencies_verified_here": False,
            "Lean_compiled_here": False, "full_core_accepted": False,
            "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}


def verify_filtered_baseline(obj: Any) -> dict[str, Any]:
    values = _fixture_identity(obj)
    producer = periodic_energy_upper(period_values(values), 48)
    require(producer["mean"] == Fraction(13, 54) and producer["prefix_cap"] == Fraction(41, 54),
            "producer_budget", "Producer period budget differs")
    checked = check_filtered_baseline(obj)
    require(str(producer["upper_square"]) == checked["upper_square"],
            "producer_checker", "Independent producer/checker disagreement")
    return checked


def verify_native_jump_minor(obj: Any) -> dict[str, Any]:
    expected = {"schema": "OPICA2_NATIVE_GAIN_MINOR_V1", "h": "1/1000",
                "smooth_upper_coefficient": "2", "smooth_lower_coefficient": "1/2",
                "prime_two_lower": "1/3", "computed_upper": "-61/375000000000",
                "authority": "RATIONAL_BUDGET_ONLY_NATIVE_ANALYTIC_BRIDGE_REQUIRED", "RH": "OPEN"}
    require(type(obj) is dict and obj == expected, "minor_fixture", "Wrong native minor fixture")
    h = parse_rational(obj["h"])
    upper = (parse_rational(obj["smooth_upper_coefficient"]) * h**2)**2 - (
        parse_rational(obj["smooth_lower_coefficient"]) * h**2 *
        parse_rational(obj["prime_two_lower"]) * h)
    require(upper == parse_rational(obj["computed_upper"]) < 0, "minor_bound", "Minor bound failed")
    return {"status": "PASS_EXACT_FINITE_ARITHMETIC", "minor_upper": str(upper),
            "analytic_bridge_verified": False, "RH": "OPEN", "Step4": "OPEN"}


def main() -> int:
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=HERE / "fixtures" / "filtered_four_column.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = verify_filtered_baseline(load_strict_json(args.fixture, 65_536))
        result["implementation_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    except (OSError, ValueError, TypeError) as exc:
        result = failure_envelope("finite_baseline", exc)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result.get("status") == "PASS_EXACT_FINITE_ARITHMETIC" else 1


if __name__ == "__main__":
    raise SystemExit(main())

