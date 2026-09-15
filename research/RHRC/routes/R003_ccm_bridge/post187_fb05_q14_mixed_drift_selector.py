#!/usr/bin/env python3
"""Target-firewalled selector primitives for the post-#186 mixed drift barrier.

This module intentionally does NOT import the post-#185 remainder-drift target
module.  It only consumes the already validated value/derivative state and
constructs predeclared normalization-safe diagnostics.  Target labels are joined
later by the certifier.

Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from flint import acb, arb, arb_mat

from canonical_source_arb import (
    _regularized_c_correction_integrand,
    definitely_nonzero,
    definitely_positive,
)
from post166_fb05_cell_interval import _arb_matrix_from_sympy
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR, TARGET_N, scalar_geometry
from post177_fb05_q13_fixed_unit_derivative import (
    direct_arch_component_prime,
    fixed_unit_primitive_derivative_caches,
    pole_component_prime,
    prime_component_prime,
)
from post179_fb05_q13_correlation_preserving_derivative import overlap, point_record_from_box


def c_correction_prime(L: arb) -> arb:
    """Endpoint derivative of cCorrection(L)=integral_0^L f(z) dz."""
    z = _regularized_c_correction_integrand(acb(L))
    if not z.imag.contains(0):
        raise ArithmeticError("cCorrection derivative acquired non-real enclosure")
    return z.real


def four_way_channel_derivative_matrices(L: arb, N: int, Q: int) -> dict[str, arb_mat]:
    """Differentiate the existing four-way research channel convention.

    canonical = pole + arch_signed + prime_signed + scalar_shift,
    where arch_signed=-legacy_arch, prime_signed=-prime and
    scalar_shift=2*cCorrection(L) I.
    """
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    derivs = fixed_unit_primitive_derivative_caches(L, N)
    cc_prime = c_correction_prime(L)
    dim = len(idx)
    pole_rows = [[arb(0) for _ in idx] for _ in idx]
    arch_rows = [[arb(0) for _ in idx] for _ in idx]
    prime_rows = [[arb(0) for _ in idx] for _ in idx]
    scalar_rows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, dim):
            m = idx[c]
            pole = pole_component_prime(n, m, L)
            arch_direct = direct_arch_component_prime(
                n, m, derivs["alpha"], derivs["beta"], derivs["gamma"]
            )
            prime = prime_component_prime(n, m, L, Q)
            scalar = 2 * cc_prime if n == m else arb(0)
            arch_signed = -arch_direct - scalar
            prime_signed = -prime
            pole_rows[r][c] = pole_rows[c][r] = pole
            arch_rows[r][c] = arch_rows[c][r] = arch_signed
            prime_rows[r][c] = prime_rows[c][r] = prime_signed
            scalar_rows[r][c] = scalar_rows[c][r] = scalar

    return {
        "pole": arb_mat(pole_rows),
        "arch_signed": arb_mat(arch_rows),
        "prime_signed": arb_mat(prime_rows),
        "scalar_shift": arb_mat(scalar_rows),
    }


def _matrix_all_entries_overlap(A: arb_mat, B: arb_mat) -> bool:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        return False
    return all(
        overlap(A[r, c], B[r, c])
        for r in range(A.nrows())
        for c in range(A.ncols())
    )


def _channel_triplet(D: arb_mat) -> dict[str, arb]:
    geom = one_step_geometry(TARGET_N, "even")
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * D * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected channel restriction dimension")
    return {"a": H[0, 0], "b": H[0, 1], "d": H[1, 1]}


def _build_primitives(box: dict) -> dict:
    point = point_record_from_box(box)
    rec = point["record"]
    even = rec["even"]
    L = point["L"]
    if not definitely_positive(L):
        raise AssertionError("selector audit requires L>0")

    even_norms = scalar_geometry("even")
    odd_norms = scalar_geometry("odd")
    channels = four_way_channel_derivative_matrices(L, TARGET_KSTAR, int(box["Q"]))
    rebuilt = (
        channels["pole"]
        + channels["arch_signed"]
        + channels["prime_signed"]
        + channels["scalar_shift"]
    )
    channel_triplets = {name: _channel_triplet(D) for name, D in channels.items()}

    return {
        "L": L,
        "a": even["a"],
        "b": even["b"],
        "d": even["d"],
        "a_prime": even["a_prime"],
        "b_prime": even["b_prime"],
        "d_prime": even["d_prime"],
        "w2": arb(even_norms.W_norm_sq),
        "c2": arb(even_norms.c_norm_sq),
        "odd_a": rec["odd_N2_predecessor"],
        "odd_a_prime": rec["odd_N2_predecessor_prime"],
        "odd_w2": arb(odd_norms.W_norm_sq),
        "channels": channel_triplets,
        "channel_matrix_reconstruction_overlap": _matrix_all_entries_overlap(
            rebuilt, rec["matrix_prime"]
        ),
    }


def _directional_from_triplet(triplet: dict[str, arb], x: arb) -> arb:
    return triplet["d"] - 2 * x * triplet["b"] + x * x * triplet["a"]


def _selector_values_from_primitives(p: dict) -> dict:
    a = p["a"]
    if not definitely_positive(a):
        return {"scope": "OUT_OF_CERTIFIED_H1_SCOPE", "candidates": {}, "diagnostics": {}}

    L = p["L"]
    b = p["b"]
    d = p["d"]
    ap = p["a_prime"]
    bp = p["b_prime"]
    dp = p["d_prime"]
    w2 = p["w2"]
    c2 = p["c2"]
    x = b / a
    envelope = c2 + x * x * w2
    if not definitely_positive(envelope):
        raise AssertionError("selector envelope failed positivity")

    normalized_predecessor = a / w2
    normalized_offdiag_sq = b * b / (w2 * c2)
    normalized_shell = d / c2
    coupling_ratio = x * x * w2 / c2
    unit_pivot = (d - b * x) / c2

    aR_prime = ap + w2 / L
    bR_prime = bp
    dR_prime = dp + c2 / L
    remainder_a_component = L * x * x * aR_prime / envelope
    remainder_b_component = -2 * L * x * bR_prime / envelope
    remainder_d_component = L * dR_prime / envelope
    mechanism_sum = remainder_a_component + remainder_b_component + remainder_d_component

    parity_predecessor_ratio = None
    parity_log_slope_gap = None
    if definitely_positive(p["odd_a"]):
        even_level = a / w2
        odd_level = p["odd_a"] / p["odd_w2"]
        parity_predecessor_ratio = odd_level / even_level
        parity_log_slope_gap = L * p["odd_a_prime"] / p["odd_a"] - L * ap / a

    chis = {
        name: L * _directional_from_triplet(triplet, x) / envelope
        for name, triplet in p["channels"].items()
    }
    smooth = chis["pole"] + chis["arch_signed"] + chis["scalar_shift"]
    prime_vs_smooth_sq_ratio = None
    if definitely_nonzero(smooth):
        prime_vs_smooth_sq_ratio = chis["prime_signed"] ** 2 / smooth ** 2

    direct_full_ratio = L * (dp - 2 * x * bp + x * x * ap) / envelope
    channel_sum = sum(chis.values(), arb(0))

    candidates = {
        "coupling_ratio": coupling_ratio,
        "remainder_a_component": remainder_a_component,
        "remainder_b_component": remainder_b_component,
        "remainder_d_component": remainder_d_component,
        "parity_predecessor_ratio": parity_predecessor_ratio,
        "parity_log_slope_gap": parity_log_slope_gap,
        "chi_prime_signed": chis["prime_signed"],
        "chi_arch_signed": chis["arch_signed"],
        "chi_pole": chis["pole"],
        "prime_vs_smooth_sq_ratio": prime_vs_smooth_sq_ratio,
    }
    diagnostics = {
        "normalized_predecessor": normalized_predecessor,
        "normalized_offdiag_sq": normalized_offdiag_sq,
        "normalized_shell": normalized_shell,
        "unit_pivot": unit_pivot,
        "unit_pivot_sq": unit_pivot * unit_pivot,
        "chi_scalar_shift": chis["scalar_shift"],
        "mechanism_sum": mechanism_sum,
        "channel_sum": channel_sum,
        "direct_full_ratio": direct_full_ratio,
    }
    return {
        "scope": "CERTIFIED_H1_SCOPE",
        "candidates": candidates,
        "diagnostics": diagnostics,
        "checks": {
            "channel_matrix_reconstruction_overlap": bool(
                p["channel_matrix_reconstruction_overlap"]
            ),
            "channel_directional_sum_overlap": overlap(channel_sum, direct_full_ratio),
        },
    }


def selector_record_from_box(box: dict) -> dict:
    p = _build_primitives(box)
    values = _selector_values_from_primitives(p)
    return {
        "label": box["label"],
        "Q": int(box["Q"]),
        "role": box["role"],
        "primary": bool(box["primary"]),
        "side": box.get("side"),
        "offset_bit": box.get("offset_bit"),
        "scope": values["scope"],
        "candidates": values.get("candidates", {}),
        "diagnostics": values.get("diagnostics", {}),
        "checks": values.get("checks", {}),
    }


def _rescale_primitives(p: dict, alpha: int, beta: int, gamma: int) -> dict:
    if alpha == 0 or beta == 0 or gamma == 0:
        raise ValueError("normalization rescalings must be nonzero")
    aa = arb(alpha * alpha)
    bb = arb(beta * beta)
    ab = arb(alpha * beta)
    gg = arb(gamma * gamma)
    return {
        "L": p["L"],
        "a": p["a"] * aa,
        "b": p["b"] * ab,
        "d": p["d"] * bb,
        "a_prime": p["a_prime"] * aa,
        "b_prime": p["b_prime"] * ab,
        "d_prime": p["d_prime"] * bb,
        "w2": p["w2"] * aa,
        "c2": p["c2"] * bb,
        "odd_a": p["odd_a"] * gg,
        "odd_a_prime": p["odd_a_prime"] * gg,
        "odd_w2": p["odd_w2"] * gg,
        "channels": {
            name: {
                "a": triplet["a"] * aa,
                "b": triplet["b"] * ab,
                "d": triplet["d"] * bb,
            }
            for name, triplet in p["channels"].items()
        },
        "channel_matrix_reconstruction_overlap": p["channel_matrix_reconstruction_overlap"],
    }


def normalization_invariance_record(box: dict, rescalings: list[dict]) -> dict:
    base_p = _build_primitives(box)
    base = _selector_values_from_primitives(base_p)
    if base["scope"] != "CERTIFIED_H1_SCOPE":
        return {"scope": base["scope"], "all_overlap": True, "rescalings": []}

    rows = []
    all_ok = True
    for scale in rescalings:
        p = _rescale_primitives(
            base_p,
            int(scale["even_predecessor"]),
            int(scale["shell"]),
            int(scale["odd_predecessor"]),
        )
        got = _selector_values_from_primitives(p)
        field_checks = {}
        for field, original in base["candidates"].items():
            transformed = got["candidates"].get(field)
            if original is None or transformed is None:
                ok = original is None and transformed is None
            else:
                ok = overlap(original, transformed)
            field_checks[field] = bool(ok)
            all_ok = all_ok and bool(ok)
        rows.append({
            "scale": scale,
            "field_overlaps": field_checks,
            "all_overlap": all(field_checks.values()),
        })
    return {
        "scope": "CERTIFIED_H1_SCOPE",
        "all_overlap": bool(all_ok),
        "rescalings": rows,
    }
