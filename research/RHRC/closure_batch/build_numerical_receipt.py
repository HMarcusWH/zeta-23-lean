from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from interval_codec import DyadicInterval, canonical_json

PROGRAM_FILES = (
    "research/RHRC/closure_batch/small_aperture_arb_audit.py",
    "research/RHRC/closure_batch/canonical_schur_arb.py",
    "research/RHRC/closure_batch/canonical_characteristic_scout.py",
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_digest(obj: Any) -> str:
    return sha256_bytes(canonical_json(obj).encode())


def program_digest(repo_root: Path) -> str:
    h = hashlib.sha256()
    for rel in PROGRAM_FILES:
        path = repo_root / rel
        h.update(rel.encode())
        h.update(b"\0")
        h.update(path.read_bytes())
        h.update(b"\0")
    return h.hexdigest()


def interval_from_ball(ball: dict, bits: int) -> dict[str, int]:
    return DyadicInterval.from_decimal_bounds(
        str(ball["lower"]), str(ball["upper"]), bits=bits
    ).to_json()


def add_case(cases: list[dict], *, case_id: str, track: str, observable: str,
             params: dict, ball: dict, bits: int) -> None:
    interval = DyadicInterval.from_json(interval_from_ball(ball, bits))
    cases.append({
        "id": case_id,
        "track": track,
        "observable": observable,
        "params": params,
        "precision_bits": bits,
        "source_bounds": {
            "lower": str(ball["lower"]),
            "upper": str(ball["upper"]),
        },
        "interval": interval.to_json(),
        "claimed_sign": interval.sign(),
    })


def build_receipt(
    results: Path,
    plan: dict,
    source_commit: str,
    source_tree: str,
    repo_root: Path,
) -> dict:
    scope = plan["numerical_receipt_scope"]
    research_scope = plan["research_scope"]
    cases: list[dict] = []

    a_bits = int(scope["tracks"]["A"]["precision_bits"])
    a = json.loads((results / scope["tracks"]["A"]["source"]).read_text())
    for row in a["rows"]:
        add_case(
            cases,
            case_id=f"A_L_{a['L'].replace('/', '_')}_K_{row['K']}_LAMBDA_MIN",
            track="A",
            observable="lambda_min",
            params={"L": a["L"], "K": int(row["K"])},
            ball=row["lambda_min"],
            bits=a_bits,
        )

    b_bits = int(scope["tracks"]["B"]["precision_bits"])
    b = json.loads((results / scope["tracks"]["B"]["source"]).read_text())
    for row in b["rows"]:
        seg = row["segment"]
        stem = (
            f"B_Q{row['Q']}_K{row['Kstar']}_{row['parity'].upper()}_"
            f"S{seg['lo']}_{seg['hi']}_{seg['den']}"
        )
        params = {
            "Q": int(row["Q"]),
            "K": int(row["Kstar"]),
            "N": int(row["N"]),
            "parity": row["parity"],
            "segment": {
                "lo": int(seg["lo"]), "hi": int(seg["hi"]), "den": int(seg["den"])
            },
        }
        add_case(
            cases,
            case_id=stem + "_SHELL",
            track="B",
            observable="shell_energy",
            params=params,
            ball=row["shell_energy"],
            bits=b_bits,
        )
        for i, minor in enumerate(row.get("schur_form_leading_minors", [])):
            add_case(
                cases,
                case_id=stem + f"_MINOR_{i}",
                track="B",
                observable="schur_form_leading_minor",
                params={**params, "minor_index": i},
                ball=minor,
                bits=b_bits,
            )

    c_bits = int(scope["tracks"]["C"]["precision_bits"])
    c = json.loads((results / scope["tracks"]["C"]["source"]).read_text())
    for row in c.get("successive_K_deltas", []):
        add_case(
            cases,
            case_id=(
                f"C_L{row['L']}_K{row['K_from']}_{row['K_to']}_"
                f"Z{row['z_index']}_KDELTA"
            ),
            track="C",
            observable="successive_K_delta_abs",
            params={
                "L": int(row["L"]),
                "K_from": int(row["K_from"]),
                "K_to": int(row["K_to"]),
                "z_index": int(row["z_index"]),
            },
            ball=row["abs_delta"],
            bits=c_bits,
        )
    for row in c.get("successive_L_deltas", []):
        add_case(
            cases,
            case_id=(
                f"C_L{row['L_from']}_{row['L_to']}_K{row['K']}_"
                f"Z{row['z_index']}_LDELTA"
            ),
            track="C",
            observable="successive_L_delta_abs",
            params={
                "L_from": int(row["L_from"]),
                "L_to": int(row["L_to"]),
                "K": int(row["K"]),
                "z_index": int(row["z_index"]),
            },
            ball=row["abs_delta"],
            bits=c_bits,
        )

    signs = {"POSITIVE": 0, "NEGATIVE": 0, "ZERO_ONLY": 0, "CONTAINS_ZERO": 0}
    for case in cases:
        signs[case["claimed_sign"]] += 1

    return {
        "schema_version": "RHRC-CLOSURE-NUMERICAL-RECEIPT-1.0",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "BOUNDED_NUMERICAL_INTERVALS_ONLY",
        "terminal_claim": "RH_OPEN",
        "source": {"commit": source_commit, "tree": source_tree},
        "plan_sha256": canonical_digest(plan),
        "scope_sha256": canonical_digest(scope),
        "fixture_sha256": canonical_digest(research_scope),
        "program_sha256": program_digest(repo_root),
        "precision_bits": {
            track: int(spec["precision_bits"])
            for track, spec in scope["tracks"].items()
        },
        "cases": cases,
        "summary": {"case_count": len(cases), "sign_counts": signs},
    }
