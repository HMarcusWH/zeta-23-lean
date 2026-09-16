#!/usr/bin/env python3
"""Post-#190 FB-05 canonical-realizability audit.

This module starts from the exact abstract reflected twin certified by PR #190
and progressively adds production constraints without silently jumping ahead in
the layer hierarchy.

Research/audit tooling only.  No result here is Lean theorem authority.
FB-05, negative-root exclusion, and RH remain OPEN.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

from flint import arb, arb_mat

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR
from post177_fb05_q13_fixed_unit_derivative import (
    direct_arch_component_prime,
    fixed_unit_primitive_derivative_caches,
)
from post187_fb05_q14_mixed_drift_selector import (
    c_correction_prime,
    four_way_channel_derivative_matrices,
    selector_record_from_box,
)
from post188_fb05_q14_mixed_drift_selector_independence import derived_state, sign_name
from post189_fb05_joint_selector_separability import (
    EXACT_VECTOR_CLASSIFICATION,
    THRESHOLD_SIGNATURE_CLASSIFICATION,
    joint_witness_result,
)

EXACT_TWIN_SURVIVES = "EXACT_TWIN_SURVIVES"
EXACT_TWIN_EXCLUDED_BY_IDENTITY = "EXACT_TWIN_EXCLUDED_BY_IDENTITY"
UNRESOLVED = "UNRESOLVED"

EVIDENCE_EXACT_RATIONAL = "EXACT_RATIONAL"
EVIDENCE_EXACT_SYMBOLIC = "EXACT_SYMBOLIC"
EVIDENCE_ARB_POINT = "ARB_POINT"
EVIDENCE_BOUNDED_SEARCH = "BOUNDED_SEARCH"

LAYER_IDS = (
    "L0_AMBIENT_NORMALIZED",
    "L1_SOURCE_CHANNEL_COUPLING",
    "L2_SCALAR_APERTURE",
    "L3_COMMON_ARCH_APERTURE",
    "L4_COMMON_SCHUR_GEOMETRY",
    "L5_CANONICAL_PRODUCTION",
)


def _fraction(value) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value, 1)
    return Fraction(str(value))


def _primary_boxes(schedule: dict) -> list[dict]:
    return [box for box in schedule["boxes"] if bool(box["primary"])]


def _box_center_L(box: dict) -> arb:
    den = int(box["den"])
    if den <= 0:
        raise ValueError("box denominator must be positive")
    t = arb(int(box["center_num"])) / den
    return cell_coordinate_L_arb(int(box["Q"]), t)


def _direct_arch_derivative_matrix(L: arb, N: int) -> arb_mat:
    idx = list(range(-N, N + 1))
    derivs = fixed_unit_primitive_derivative_caches(L, N)
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = direct_arch_component_prime(
                n,
                m,
                derivs["alpha"],
                derivs["beta"],
                derivs["gamma"],
            )
            rows[r][c] = rows[c][r] = value
    return arb_mat(rows)


def _matrix_overlap(A: arb_mat, B: arb_mat) -> bool:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        return False
    return all(
        bool((A[r, c] - B[r, c]).contains(0))
        for r in range(A.nrows())
        for c in range(A.ncols())
    )


def _arb_nonzero(x: arb) -> bool:
    return not bool(x.contains(0))


def _arb_same_sign(x: arb, y: arb) -> bool:
    return (definitely_positive(x) and definitely_positive(y)) or (
        definitely_negative(x) and definitely_negative(y)
    )


def _arb_opposite_sign(x: arb, y: arb) -> bool:
    return (definitely_positive(x) and definitely_negative(y)) or (
        definitely_negative(x) and definitely_positive(y)
    )


def _arb_overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def _selector_ball_snapshot(record: dict) -> dict:
    candidates = record.get("candidates", {})
    diagnostics = record.get("diagnostics", {})
    keep_candidates = (
        "coupling_ratio",
        "parity_predecessor_ratio",
        "parity_log_slope_gap",
        "chi_prime_signed",
        "chi_arch_signed",
        "chi_pole",
        "prime_vs_smooth_sq_ratio",
    )
    return {
        "label": record["label"],
        "Q": record["Q"],
        "scope": record["scope"],
        "strong": {
            key: None if candidates.get(key) is None else ball_record(candidates[key])
            for key in keep_candidates
        },
        "chi_scalar_shift": (
            None if diagnostics.get("chi_scalar_shift") is None else ball_record(diagnostics["chi_scalar_shift"])
        ),
        "channel_sum": None if diagnostics.get("channel_sum") is None else ball_record(diagnostics["channel_sum"]),
        "checks": record.get("checks", {}),
    }


def layer0_ambient_replay(selector_fixture: dict, post190_fixture: dict) -> dict:
    joint = joint_witness_result(selector_fixture, post190_fixture["joint_witness"])
    decisive = (
        joint["exact_vector_classification"] == EXACT_VECTOR_CLASSIFICATION
        and joint["threshold_signature_classification"] == THRESHOLD_SIGNATURE_CLASSIFICATION
        and joint["target_sign_flip"]
        and joint["same_exact_strong_vector"]
    )
    return {
        "layer": LAYER_IDS[0],
        "classification": EXACT_TWIN_SURVIVES if decisive else UNRESOLVED,
        "scope": "SPECIFIC_POST190_WITNESS",
        "evidence_class": EVIDENCE_EXACT_RATIONAL,
        "same_exact_strong_vector": joint["same_exact_strong_vector"],
        "same_nonboundary_threshold_signature": joint["same_nonboundary_threshold_signature"],
        "target_sign_flip": joint["target_sign_flip"],
        "left_target_margin": joint["left_target_margin"],
        "right_target_margin": joint["right_target_margin"],
    }


def layer1_source_channel_coupling(post190_fixture: dict) -> dict:
    raw = post190_fixture["joint_witness"]
    rows = []
    all_exact = True
    for side in ("left", "right"):
        state = derived_state(raw[side])
        arch = state["chi_arch_signed"]
        scalar = state["chi_scalar_shift"]
        arch_direct = -(arch + scalar)
        residual = arch + scalar + arch_direct
        all_exact = all_exact and residual == 0
        rows.append({
            "side": side,
            "chi_arch_signed": str(arch),
            "chi_scalar_shift": str(scalar),
            "implied_chi_arch_direct": str(arch_direct),
            "coupling_residual": str(residual),
        })
    return {
        "layer": LAYER_IDS[1],
        "classification": EXACT_TWIN_SURVIVES if all_exact else UNRESOLVED,
        "scope": "SPECIFIC_POST190_WITNESS",
        "evidence_class": EVIDENCE_EXACT_RATIONAL,
        "interpretation": (
            "The matrix-level source-channel coupling alone does not exclude the #190 twin; "
            "each side can be extended by a different hidden direct-arch coordinate."
        ),
        "rows": rows,
    }


def scalar_chi_at_aperture(L: arb) -> arb:
    if not definitely_positive(L):
        raise ValueError("scalar production law requires L>0")
    return 2 * L * c_correction_prime(L)


def _positive_scalar_reflection_control() -> dict:
    # Use two actual scalar-aperture values.  The remaining ambient coordinates
    # are then defined algebraically from them.  This shows that the scalar law
    # alone does not kill the general reflection mechanism.
    L1 = arb(1)
    L2 = arb(2)
    s1 = scalar_chi_at_aperture(L1)
    s2 = scalar_chi_at_aperture(L2)
    if not definitely_positive(s1) or not definitely_positive(s2):
        raise AssertionError("scalar-aperture control lost positivity")
    if not _arb_nonzero(s1 - s2):
        raise AssertionError("scalar-aperture control values are not rigorously distinct")

    # Orient u>0 without changing the algebraic construction.
    if definitely_positive(s1 - s2):
        hi, lo = s1, s2
        L_hi, L_lo = L1, L2
    elif definitely_positive(s2 - s1):
        hi, lo = s2, s1
        L_hi, L_lo = L2, L1
    else:
        raise AssertionError("could not orient distinct scalar-aperture values")

    u = (hi - lo) / 2
    A = -(hi + lo) / 2
    prime = u / 2
    smooth_hi = A + hi
    smooth_lo = A + lo
    target_hi = -(prime + smooth_hi)
    target_lo = -(prime + smooth_lo)

    if not definitely_positive(u):
        raise AssertionError("reflection control u is not positive")
    if not _arb_overlap(smooth_hi, u) or not _arb_overlap(smooth_lo, -u):
        raise AssertionError("reflection control smooth-channel identities failed")
    if not _arb_opposite_sign(target_hi, target_lo):
        raise AssertionError("reflection control target signs did not flip")

    # The exact symbolic identity is C4=(u/2)^2/u^2=1/4 on both sides.
    return {
        "classification": EXACT_TWIN_SURVIVES,
        "scope": "GENERAL_REFLECTION_MECHANISM_UNDER_SCALAR_LAW_ONLY",
        "evidence_class": EVIDENCE_EXACT_SYMBOLIC,
        "actual_scalar_samples": {
            "higher": {"L": ball_record(L_hi), "chi_scalar": ball_record(hi)},
            "lower": {"L": ball_record(L_lo), "chi_scalar": ball_record(lo)},
        },
        "symbolic_identities": {
            "A": "-(s_hi+s_lo)/2",
            "u": "(s_hi-s_lo)/2 > 0",
            "prime": "u/2",
            "smooth_hi": "u",
            "smooth_lo": "-u",
            "C4_both": "1/4",
            "target_hi": "-3*u/2",
            "target_lo": "u/2",
        },
        "interpretation": (
            "Two distinct positive scalar-law values still admit an abstract exact reflection after the "
            "other ambient channels are chosen algebraically.  Scalar positivity/range information alone "
            "therefore does not eliminate the general reflection mechanism."
        ),
    }


def layer2_scalar_aperture(post190_fixture: dict) -> dict:
    witness = post190_fixture["joint_witness"]
    scalars = {
        side: derived_state(witness[side])["chi_scalar_shift"]
        for side in ("left", "right")
    }
    specific_excluded = all(value < 0 for value in scalars.values())
    if not specific_excluded:
        raise AssertionError("post-#190 witness no longer has both negative scalar coordinates")
    control = _positive_scalar_reflection_control()
    return {
        "layer": LAYER_IDS[2],
        "classification": EXACT_TWIN_EXCLUDED_BY_IDENTITY,
        "scope": "SPECIFIC_POST190_WITNESS",
        "evidence_class": EVIDENCE_EXACT_SYMBOLIC,
        "specific_witness": {
            "left_chi_scalar_shift": str(scalars["left"]),
            "right_chi_scalar_shift": str(scalars["right"]),
            "production_law": "chi_scalar(L)=2*L*cCorrection'(L)>0 for L>0",
            "excluded": True,
        },
        "general_reflection_control": control,
    }


def layer3_common_arch_aperture(schedule: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    rows = []
    all_coupling_overlap = True
    for box in _primary_boxes(schedule):
        L = _box_center_L(box)
        Q = int(box["Q"])
        channels = four_way_channel_derivative_matrices(L, TARGET_KSTAR, Q)
        arch_direct = _direct_arch_derivative_matrix(L, TARGET_KSTAR)
        coupled = channels["arch_signed"] + channels["scalar_shift"]
        identity_ok = _matrix_overlap(coupled, -arch_direct)
        all_coupling_overlap = all_coupling_overlap and identity_ok
        rows.append({
            "label": box["label"],
            "Q": Q,
            "L": ball_record(L),
            "matrix_level_arch_scalar_coupling_overlap": identity_ok,
            "scalar_chi_positive": definitely_positive(scalar_chi_at_aperture(L)),
        })
    return {
        "layer": LAYER_IDS[3],
        "classification": UNRESOLVED,
        "scope": "BOUNDED_CANONICAL_SCHEDULE",
        "evidence_class": EVIDENCE_ARB_POINT,
        "primary_state_count": len(rows),
        "all_matrix_level_arch_scalar_couplings_overlap": all_coupling_overlap,
        "interpretation": (
            "Actual direct-arch and scalar derivatives are now tied to the same aperture on the frozen "
            "Q14 centers.  This finite replay verifies the production coupling but does not prove or disprove "
            "existence of an exact opposite-target twin."
        ),
        "rows": rows,
    }


def _strong_balls(record: dict) -> list[arb] | None:
    if record["scope"] != "CERTIFIED_H1_SCOPE":
        return None
    candidates = record["candidates"]
    fields = (
        "coupling_ratio",
        "parity_predecessor_ratio",
        "parity_log_slope_gap",
        "chi_prime_signed",
        "chi_arch_signed",
        "chi_pole",
        "prime_vs_smooth_sq_ratio",
    )
    values = [candidates.get(field) for field in fields]
    if any(value is None for value in values):
        return None
    return values


def layer4_common_schur_geometry(schedule: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    records = [selector_record_from_box(box) for box in _primary_boxes(schedule)]
    pair_rows = []
    overlap_pair_count = 0
    opposite_target_overlap_pair_count = 0
    for left, right in combinations(records, 2):
        lv = _strong_balls(left)
        rv = _strong_balls(right)
        if lv is None or rv is None:
            continue
        vector_overlap = all(_arb_overlap(a, b) for a, b in zip(lv, rv))
        if vector_overlap:
            overlap_pair_count += 1
        lt = -left["diagnostics"]["channel_sum"]
        rt = -right["diagnostics"]["channel_sum"]
        opposite_target = _arb_opposite_sign(lt, rt)
        if vector_overlap and opposite_target:
            opposite_target_overlap_pair_count += 1
        pair_rows.append({
            "left": left["label"],
            "right": right["label"],
            "strong_vector_balls_all_overlap": vector_overlap,
            "opposite_certified_target_signs": opposite_target,
        })
    return {
        "layer": LAYER_IDS[4],
        "classification": UNRESOLVED,
        "scope": "BOUNDED_CANONICAL_SCHEDULE",
        "evidence_class": EVIDENCE_BOUNDED_SEARCH,
        "primary_state_count": len(records),
        "primary_records": [_selector_ball_snapshot(record) for record in records],
        "pair_count": len(pair_rows),
        "strong_vector_overlap_pair_count": overlap_pair_count,
        "strong_vector_overlap_and_opposite_target_pair_count": opposite_target_overlap_pair_count,
        "interpretation": (
            "The Schur direction x=b/a and envelope are now taken from the same actual production state. "
            "Arb overlap can nominate candidates but cannot certify exact vector equality; absence of a pair "
            "therefore remains UNRESOLVED."
        ),
        "pairs": pair_rows,
    }


def layer5_canonical_production(schedule: dict, *, precision_bits: int) -> dict:
    set_precision(precision_bits)
    records = [selector_record_from_box(box) for box in schedule["boxes"]]
    in_scope = [record for record in records if record["scope"] == "CERTIFIED_H1_SCOPE"]
    reconstruction_ok = all(
        bool(record.get("checks", {}).get("channel_matrix_reconstruction_overlap"))
        and bool(record.get("checks", {}).get("channel_directional_sum_overlap"))
        for record in in_scope
    )
    primary = [record for record in records if record["label"] in {b["label"] for b in _primary_boxes(schedule)}]
    return {
        "layer": LAYER_IDS[5],
        "classification": UNRESOLVED,
        "scope": "BOUNDED_CANONICAL_SCHEDULE",
        "evidence_class": EVIDENCE_ARB_POINT,
        "state_count": len(records),
        "certified_h1_state_count": len(in_scope),
        "primary_state_count": len(primary),
        "all_in_scope_channel_reconstructions_overlap": reconstruction_ok,
        "interpretation": (
            "Every reported coordinate is regenerated from the existing canonical production evaluator on "
            "the inherited same-L/same-Q/same-parity schedule.  This is still finite research evidence: no "
            "exact canonical twin is proved to exist or not exist."
        ),
        "records": [_selector_ball_snapshot(record) for record in records],
    }


def audit_all_layers(
    selector_fixture: dict,
    post190_fixture: dict,
    schedule: dict,
    *,
    precision_bits: int,
) -> dict:
    set_precision(precision_bits)
    layers = [
        layer0_ambient_replay(selector_fixture, post190_fixture),
        layer1_source_channel_coupling(post190_fixture),
        layer2_scalar_aperture(post190_fixture),
        layer3_common_arch_aperture(schedule, precision_bits=precision_bits),
        layer4_common_schur_geometry(schedule, precision_bits=precision_bits),
        layer5_canonical_production(schedule, precision_bits=precision_bits),
    ]
    return {
        "schema_version": "POST190_FB05_CANONICAL_REALIZABILITY_RESULT_v1",
        "status": "PASS",
        "layers": layers,
        "first_specific_witness_exclusion_layer": LAYER_IDS[2],
        "general_reflection_excluded": False,
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
