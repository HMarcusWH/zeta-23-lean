"""Small exact-rational illustrations for docs/EXAMPLES.md.

Run from any working directory with Python 3.10 or newer. No optional packages,
Lean objects, native-source integrations, or generated research state are used.
These finite checks illustrate statements; they do not replace their proofs.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json


def require(condition: bool, message: str) -> None:
    """Keep checks active under python -O as well as ordinary Python."""
    if not condition:
        raise ArithmeticError(message)


def dot(x, y):
    require(len(x) == len(y), "vector dimensions differ")
    return sum((a * b for a, b in zip(x, y)), Q())


def quad(matrix, vector):
    require(len(matrix) == len(vector), "matrix/vector dimensions differ")
    return dot(vector, [dot(row, vector) for row in matrix])


def gram_witness():
    x, y, c = [Q(1), Q(0)], [Q(1), Q(1)], Q(2)
    xx, xy, yy = dot(x, x), dot(x, y), dot(y, y)
    determinant = xx * yy - xy * xy
    witness = [xx * b - xy * a for a, b in zip(x, y)]
    pair = [[c * (x[i] * x[j] - y[i] * y[j]) for j in range(2)]
            for i in range(2)]
    full = [[pair[i][j] + (5 if i == j else 0) for j in range(2)]
            for i in range(2)]
    require(determinant == 1 and quad(pair, witness) == -c * determinant ** 2,
            "denominator-free negative-witness identity failed")
    full_determinant = full[0][0] * full[1][1] - full[0][1] * full[1][0]
    require(full[0][0] > 0 and full_determinant > 0,
            "positive-background control is not positive definite")
    require(quad(full, witness) == 3, "background did not mask this witness")
    return {"pair_matrix": pair, "gram_determinant": determinant,
            "witness": witness, "pair_energy": quad(pair, witness),
            "background": "5 I", "full_matrix": full,
            "full_determinant": full_determinant,
            "full_energy_at_same_witness": quad(full, witness)}


def singular_schur():
    # Coordinates are (old range coordinate, old kernel coordinate, new shell).
    regular = [[Q(1), Q(0), Q(1)], [Q(0), Q(0), Q(0)],
               [Q(1), Q(0), Q(2)]]
    negative = [[Q(1), Q(0), Q(1)], [Q(0), Q(0), Q(0)],
                [Q(1), Q(0), Q(0)]]
    resonant = [[Q(1), Q(0), Q(0)], [Q(0), Q(0), Q(1)],
                [Q(0), Q(1), Q(2)]]
    regular_witness, resonant_witness = [Q(-1), Q(0), Q(1)], [Q(0), Q(-2), Q(1)]
    require(quad(regular, regular_witness) == 1, "regular Schur identity failed")
    require(quad(negative, regular_witness) == -1, "negative regular control failed")
    require(quad(resonant, resonant_witness) == -2, "kernel coupling was lost")
    return {"predecessor": [[1, 0], [0, 0]],
            "regular": {"coupling": [1, 0], "response_in_kernel_perp": [1, 0],
                        "new_diagonal": 2, "schur_scalar": 1,
                        "completed_square": "(x + t)^2 + t^2"},
            "regular_negative_control": {"new_diagonal": 0,
                                         "witness": regular_witness, "energy": -1},
            "resonant": {"coupling": [0, 1], "coupling_in_range": False,
                         "matrix": resonant, "witness": resonant_witness, "energy": -2}}


def positivity_certificate():
    matrix = [[Q(9, 4), Q(1)], [Q(1), Q(2)]]
    factor = [[Q(1)], [Q(1)]]
    shift = Q(1)
    residual = [[matrix[i][j] - (shift if i == j else 0) - dot(factor[i], factor[j])
                 for j in range(2)] for i in range(2)]
    frobenius_squared = sum((entry ** 2 for row in residual for entry in row), Q())
    require(shift > 0 and frobenius_squared == Q(1, 16) < shift ** 2,
            "shifted-factor certificate failed")
    # Removing the positive-shift requirement would accept the negative matrix [-1].
    bad_matrix, bad_shift = [[Q(-1)]], Q(-1)
    bad_residual_squared = (bad_matrix[0][0] - bad_shift) ** 2
    require(bad_residual_squared < bad_shift ** 2 and quad(bad_matrix, [Q(1)]) < 0,
            "negative-shift control failed")
    return {"matrix": matrix, "factor": factor, "shift": shift,
            "residual": residual, "residual_frobenius_squared": frobenius_squared,
            "shift_squared": shift ** 2, "certificate": "POSITIVE_EXACT_QUADRATIC_FORM",
            "negative_shift_control": {"matrix": bad_matrix, "shift": bad_shift,
                                       "residual_squared": bad_residual_squared,
                                       "energy_at_1": -1,
                                       "accepted_with_required_positive_shift": False}}


@dataclass(frozen=True)
class Observation:
    cost: int
    children: tuple[Observation, Observation] | None = None


def stopping_value(node: Observation, delay: int) -> int:
    if node.children is None:
        return node.cost
    children = max(stopping_value(child, max(delay - 1, 0)) for child in node.children)
    return children if delay else min(node.cost, children)


def cover(node: Observation, limit: int, delay: int, path="root"):
    if (delay == 0 or node.children is None) and node.cost <= limit:
        return [{"node": path, "cost": node.cost}]
    if node.children is None:
        return None
    left = cover(node.children[0], limit, max(delay - 1, 0), path + ".L")
    right = cover(node.children[1], limit, max(delay - 1, 0), path + ".R")
    return None if left is None or right is None else left + right


def high_path(node: Observation, limit: int, delay: int, path="root"):
    if (delay == 0 or node.children is None) and node.cost <= limit:
        return None
    current = {"node": path, "cost": node.cost, "eligible": delay == 0 or node.children is None}
    if node.children is None:
        return [current]
    for label, child in zip(("L", "R"), node.children):
        branch = high_path(child, limit, max(delay - 1, 0), path + "." + label)
        if branch is not None:
            return [current] + branch
    return None


def stopping_tree():
    tree = Observation(9, (Observation(3, (Observation(2), Observation(8))),
                           Observation(7, (Observation(4), Observation(5)))))
    values = [stopping_value(tree, delay) for delay in range(3)]
    require(values == [5, 5, 8], "delayed stopping values differ")
    rows = []
    for delay, limit in ((0, 5), (0, 4), (2, 5), (2, 8)):
        cut, branch = cover(tree, limit, delay), high_path(tree, limit, delay)
        require((cut is not None) == (stopping_value(tree, delay) <= limit), "incomplete cover")
        require((branch is not None) == (stopping_value(tree, delay) > limit), "missing high path")
        rows.append({"delay": delay, "limit": limit, "complete_cover": cut, "high_path": branch})
    return {"tree": {"root": 9, "L": 3, "R": 7, "LL": 2, "LR": 8, "RL": 4, "RR": 5},
            "values_at_delays_0_1_2": values, "cases": rows}


def raw_filtered():
    coefficients = [Q(1), Q(-1), Q(-1), Q(-2, 3)]
    # baselineCellResidual(n) = 1 - sum_k a_k floor(n/k), n = 0,...,11.
    period = [Q(1) - sum((a * (n // k) for k, a in enumerate(coefficients, 1)), Q())
              for n in range(12)]
    require(sum((a / n for n, a in enumerate(coefficients, 1)), Q()) == 0,
            "pole moment differs from zero")
    mean = sum((value ** 2 for value in period), Q()) / 12
    centered = [sum((period[n] ** 2 - mean for n in range(r)), Q()) for r in range(13)]
    require(mean == Q(13, 54) and max(centered) == Q(41, 54) and centered[-1] == 0,
            "periodic Abel constants differ")
    upper = sum((period[n % 12] ** 2 * (Q(1, n) - Q(1, n + 1))
                 for n in range(1, 48)), Q()) + mean / 48 + Q(41, 54) / (48 * 49)
    margin = 1 - Q(3, 8) / 2048 - Q(2, 2048 ** 2)
    witness_lower = Q(8192, 93025) * margin ** 2
    threshold = Q(17, 250)
    require(upper == Q(315384568453197375401, 4648566756368995059600), "Abel upper differs")
    require(witness_lower == Q(4396431852289, 49942416588800), "witness lower differs")
    require(upper < threshold < witness_lower, "strict filtered separation failed")
    defects = [Q(k == 1) - sum((a for n, a in enumerate(coefficients, 1) if k % n == 0), Q())
               for k in range(1, 13)]
    defect_energy = sum((d ** 2 / k for k, d in enumerate(defects, 1)), Q())
    raw_lower = 102877888512 * defect_energy
    require(defect_energy == Q(41521, 41580), "twelve-cell defect energy differs")
    require(raw_lower == Q(50852295344128, 495) > 320518 ** 2, "raw rational lower differs")
    require(upper / raw_lower < Q(6605, 10 ** 16), "same-vector ratio comparison failed")
    return {"coefficients": coefficients, "source_scale": Q(1, 4096),
            "period_square_mean": mean, "centered_prefix_max": max(centered),
            "filtered_upper": upper, "separation_threshold": threshold,
            "hypothetical_zero_filtered_lower": witness_lower,
            "first_twelve_defects": defects, "weighted_defect_energy": defect_energy,
            "raw_rational_lower": raw_lower, "raw_lower_minus_320518_squared": raw_lower - 320518 ** 2,
            "squared_norm_ratio_upper": upper / raw_lower,
            "ratio_decimal_upper": "0.0000000000006605",
            "scope": "Exact arithmetic only; analytic transport is in cited Lean source and manuscript proofs."}


EXAMPLES = {"gram-witness": gram_witness, "singular-schur": singular_schur,
            "positivity-certificate": positivity_certificate, "stopping-tree": stopping_tree,
            "raw-filtered": raw_filtered}


def encode(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(f"Unsupported JSON value: {type(value).__name__}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--example", choices=["all", *EXAMPLES], default="all")
    args = parser.parse_args()
    selected = EXAMPLES if args.example == "all" else {args.example: EXAMPLES[args.example]}
    result = {name: function() for name, function in selected.items()}
    print(json.dumps({"scope": "DOCUMENTATION_EXACT_FINITE_ILLUSTRATIONS", "results": result},
                     indent=2, default=encode))


if __name__ == "__main__":
    main()
