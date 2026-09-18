#!/usr/bin/env python3
"""Rigorous bounded certificate for post-#214 kernel dual geometry."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post214_fb05_kernel_dual_geometry import TARGET_K, exact_geometry_invariants, geometry_record_arb

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post214_fb05_kernel_dual_geometry_v1.json"


def certify(fixture: dict, schedule: dict) -> dict:
    if schedule["schema_version"] != "POST214_FB05_KERNEL_DUAL_GEOMETRY_SCHEDULE_v1":
        raise AssertionError("unexpected schedule schema")
    if schedule["base_main_sha"] != fixture["base_main_sha"]:
        raise AssertionError("schedule/base SHA drift")
    if schedule["base_main_tree"] != fixture["base_main_tree"]:
        raise AssertionError("schedule/base tree drift")
    if schedule["selected_target"] != fixture["selected_target"]:
        raise AssertionError("selected target drift")
    if int(schedule["arb_precision_bits"]) != int(fixture["arb_precision_bits"]):
        raise AssertionError("precision drift")

    set_precision(int(fixture["arb_precision_bits"]))
    rows = []
    for center in schedule["centers"]:
        t = arb(int(center["center_num"])) / int(center["den"])
        L = cell_coordinate_L_arb(int(center["Q"]), t)
        rec = geometry_record_arb(L, int(center["Q"]), TARGET_K)
        if rec["classification"] not in fixture["permitted_classifications"]:
            raise AssertionError("unregistered dual-geometry classification")
        if not rec["matrix_reconstruction_overlap"]:
            raise AssertionError("canonical matrix reconstruction failed")
        if not rec["covector_reconstruction_overlap"]:
            raise AssertionError("kernel covector reconstruction failed")
        if not rec["det_equals_neg_wedge_sq_over_four_overlap"]:
            raise AssertionError("wedge/determinant identity lost")
        if rec["scalar_identity_annihilation_exact"] != ["0", "0"]:
            raise AssertionError("quadratic normal stopped annihilating scalar identity")
        if rec["generalized_R_min"] is None or rec["generalized_R_max"] is None:
            raise AssertionError("generalized extrema were not separated")

        rows.append({
            "label": center["label"],
            "Q": int(center["Q"]),
            "primary": bool(center["primary"]),
            "role": center["role"],
            "center_num": int(center["center_num"]),
            "den": int(center["den"]),
            "L": ball_record(L),
            **rec,
        })

    primary = [row for row in rows if row["primary"]]
    controls = [row for row in rows if not row["primary"]]
    if len(primary) != 1:
        raise AssertionError("expected exactly one primary center")
    p = primary[0]

    classification = p["classification"]
    if classification == "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED":
        if not p["full_space_sign_indefinite_certified"]:
            raise AssertionError("dual independence was certified without sign indefiniteness")
        sign_route = "FULL_SPACE_SIGN_INDEFINITE_CERTIFIED"
    else:
        sign_route = "FULL_SPACE_SIGN_ROUTE_UNRESOLVED"

    if classification == "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED":
        if controls and all(row["classification"] == classification for row in controls):
            control_transfer = "DUAL_INDEPENDENCE_SURVIVES_Q13_Q15_CONTROLS"
        else:
            control_transfer = "Q14_LOCAL_DUAL_INDEPENDENCE"
    else:
        control_transfer = "NO_PRIMARY_DUAL_INDEPENDENCE_CERTIFICATE"

    return {
        "schema_version": "POST214_FB05_KERNEL_DUAL_GEOMETRY_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "classification": classification,
        "sign_route_classification": sign_route,
        "control_transfer_status": control_transfer,
        "exact_geometry": exact_geometry_invariants(TARGET_K),
        "rows": rows,
        "interpretation": {
            "source_functional": "explicitCanonicalSourceMoment = #213 source-coordinate kernel",
            "local_functional": "M4 with #163 h^(7)(0) = -2*(2*pi)^6*M4",
            "primary_classifier": "2D covector wedge f1*g2-f2*g1",
            "sign_identity": "det((f*g^T+g*f^T)/2) = -wedge^2/4",
            "magnitude_diagnostic": "generalized extrema relative to ||Dv||^2",
            "retained_state_implication": "NOT_TESTED",
        },
        "policy_replay": fixture["policy"],
        "theorem_promotion": False,
        "obs_059i_closed": False,
        "simultaneous_odd_bad_excluded": False,
        "odd_selected_closed": False,
        "negative_root_exclusion": False,
        "finite_to_infinite_closure": False,
        "rh_claim": False,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST214_FB05_KERNEL_DUAL_GEOMETRY_CERTIFICATE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    out = certify(fixture, schedule)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": out["status"],
        "classification": out["classification"],
        "sign_route_classification": out["sign_route_classification"],
        "control_transfer_status": out["control_transfer_status"],
        "primary_wedge": next(row["wedge"] for row in out["rows"] if row["primary"]),
        "primary_R_min": next(row["generalized_R_min"] for row in out["rows"] if row["primary"]),
        "primary_R_max": next(row["generalized_R_max"] for row in out["rows"] if row["primary"]),
        "obs_059i_closed": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
