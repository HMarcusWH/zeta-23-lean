#!/usr/bin/env python3
"""Independent implementation checks for post-#214 kernel dual geometry."""
from __future__ import annotations

import json

import sympy as sp
from flint import arb

from canonical_source_arb import set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post214_fb05_kernel_dual_geometry import (
    TARGET_K,
    displacement_gram_exact,
    even_boundary_flat_basis_exact,
    exact_geometry_invariants,
    geometry_record_arb,
    moment_four_covector_exact,
    quadratic_normal_exact,
)
from probe_post214_fb05_kernel_dual_geometry_scope import kernel_dual_geometry_schedule

HERE_FIXTURE = "research/RHRC/routes/R003_ccm_bridge/fixtures/post214_fb05_kernel_dual_geometry_v1.json"


def _check_exact_boundary_flat_geometry() -> dict:
    B = even_boundary_flat_basis_exact(TARGET_K)
    idx = list(range(-TARGET_K, TARGET_K + 1))
    assert B.cols == 2
    for c in range(B.cols):
        col = [sp.Integer(B[r, c]) for r in range(B.rows)]
        for k in range(3):
            assert sum(sp.Integer(d) ** k * col[r] for r, d in enumerate(idx)) == 0
        for r in range(B.rows):
            assert col[r] == col[B.rows - 1 - r]

    n2 = quadratic_normal_exact(TARGET_K)
    assert n2.T * B == sp.zeros(1, B.cols)
    G = displacement_gram_exact(B, TARGET_K)
    assert G.det() > 0

    g = moment_four_covector_exact(B, TARGET_K)
    assert g != sp.zeros(1, B.cols)
    return exact_geometry_invariants(TARGET_K)


def _check_symbolic_det_identity() -> None:
    f0, f1, g0, g1 = sp.symbols("f0 f1 g0 g1", real=True)
    wedge = f0 * g1 - f1 * g0
    H = sp.Matrix([
        [f0 * g0, (f0 * g1 + g0 * f1) / 2],
        [(f0 * g1 + g0 * f1) / 2, f1 * g1],
    ])
    assert sp.simplify(H.det() + wedge**2 / 4) == 0


def main() -> None:
    fixture = json.loads(open(HERE_FIXTURE, encoding="utf-8").read())
    schedule = kernel_dual_geometry_schedule(fixture)
    set_precision(int(fixture["implementation_check_precision_bits"]))

    invariants = _check_exact_boundary_flat_geometry()
    _check_symbolic_det_identity()

    rows = []
    for center in schedule["centers"]:
        t = arb(int(center["center_num"])) / int(center["den"])
        L = cell_coordinate_L_arb(int(center["Q"]), t)
        rec = geometry_record_arb(L, int(center["Q"]), TARGET_K)
        assert rec["matrix_reconstruction_overlap"]
        assert rec["covector_reconstruction_overlap"]
        assert rec["det_equals_neg_wedge_sq_over_four_overlap"]
        assert rec["scalar_identity_annihilation_exact"] == ["0", "0"]
        assert rec["generalized_R_min"] is not None
        assert rec["generalized_R_max"] is not None
        rows.append({
            "label": center["label"],
            "Q": center["Q"],
            "classification": rec["classification"],
            "wedge_excludes_zero": rec["wedge_excludes_zero"],
            "full_space_sign_indefinite_certified": rec["full_space_sign_indefinite_certified"],
        })

    print(json.dumps({
        "status": "PASS",
        "exact_geometry": invariants,
        "symbolic_det_identity": True,
        "rows": rows,
        "precision_bits": int(fixture["implementation_check_precision_bits"]),
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
