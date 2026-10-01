from __future__ import annotations

import sympy as sp

from feature_registry import active_feature_ids


def parse_expr(value: str) -> sp.Expr:
    return sp.sympify(value.replace("^", "**"), locals={"pi": sp.pi})


def relation_matrix(registry: dict, relations: list[dict]) -> sp.Matrix:
    features = active_feature_ids(registry)
    rows = []
    for relation in relations:
        coeffs = relation["row"]
        rows.append([parse_expr(coeffs.get(feature, "0")) for feature in features])
    if not rows:
        return sp.zeros(0, len(features))
    return sp.Matrix(rows)


def exact_rank(registry: dict, relations: list[dict]) -> int:
    return int(relation_matrix(registry, relations).rank())


def nullspace_matrix(registry: dict, relations: list[dict]) -> sp.Matrix:
    matrix = relation_matrix(registry, relations)
    basis = matrix.nullspace()
    if not basis:
        return sp.zeros(matrix.cols, 0)
    return sp.Matrix.hstack(*basis)


def quotient_dual(nullspace: sp.Matrix) -> sp.Matrix:
    """Return a diagnostic left inverse D with D*H = I when H has columns."""
    if nullspace.cols == 0:
        return sp.zeros(0, nullspace.rows)
    gram = sp.simplify(nullspace.T * nullspace)
    return sp.simplify(gram.inv() * nullspace.T)


def matrix_to_strings(matrix: sp.Matrix) -> list[list[str]]:
    return [
        [str(sp.simplify(matrix[i, j])) for j in range(matrix.cols)]
        for i in range(matrix.rows)
    ]
