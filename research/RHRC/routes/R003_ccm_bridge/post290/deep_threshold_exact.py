"""Exact bottom-only threshold selector for finite controls.

Input spectra are controls, not source-generated detector or zeta output.
The empty predecessor is represented by None and never given a fake bottom.
"""
from __future__ import annotations

from fractions import Fraction as F


def select_bottom_threshold(even: list[F], odd: list[F], depth: F) -> dict:
    if len(even) != len(odd) or not even or depth <= 0:
        raise ValueError("equal nonempty bottom lists and positive depth required")
    for values in (even, odd):
        if any(x < y for x, y in zip(values, values[1:])):
            raise ValueError("each nested-carrier bottom list must be nonincreasing")
    global_bottoms = [min(x, y) for x, y in zip(even, odd)]
    if global_bottoms[-1] > -depth:
        raise ValueError("terminal global depth is not retained")
    marks = sorted({depth / 3, depth / 2} |
                   {-v for v in global_bottoms if depth / 3 < -v < depth / 2})
    left, right = max(zip(marks, marks[1:]), key=lambda pair: pair[1] - pair[0])
    eta = (left + right) / 2
    Kd = len(global_bottoms) + 2
    gap = depth / (12 * (Kd - 1))
    index = next(i for i, value in enumerate(global_bottoms) if value < -eta)
    lam = global_bottoms[index]
    predecessor = None if index == 0 else {"even": even[index - 1], "odd": odd[index - 1]}
    branch = "STRICT_EVEN" if even[index] < odd[index] else (
        "STRICT_ODD" if odd[index] < even[index] else "TIE")
    return {"Kd": Kd, "eta": eta, "gap": gap, "selected_K": index + 3,
            "lambda": lam, "global_bottoms": global_bottoms, "predecessor": predecessor,
            "branch": branch, "inverse_budget": 6 * F(Kd - 1) / depth}
