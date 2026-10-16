#!/usr/bin/env python3
"""Compare actual frozen native observations with their independent replay.

Finite probes, symbolic Step123 objects and hypothetical-zero generated
outputs are different representation classes.  This program compares exact
source/probe identities and proven finite enclosures only; it cannot
numerically instantiate a noncomputable zero-indexed theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from evaluate_native_output import APERTURES, CARRIERS, CUTOFFS


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def panel_pair_key(record):
    return record.get("aperture"), record.get("K")


def consistency_points(value, label, problems):
    if isinstance(value, dict) and "contains_zero" in value:
        if type(value["contains_zero"]) is not bool:
            problems.append(label + ": non-Boolean zero-containment evidence")
        elif not value["contains_zero"]:
            problems.append(label + ": claimed identity misses zero")
    elif isinstance(value, list):
        for i, item in enumerate(value):
            consistency_points(item, label + "[" + str(i) + "]", problems)
    elif isinstance(value, dict):
        for name, item in value.items():
            consistency_points(item, label + "." + name, problems)


def compare(panel, checker, *, panel_path=None, checker_path=None):
    if panel.get("schema") != "post290.native-observation-panel.v1":
        raise ValueError("unexpected native panel schema")
    if checker.get("schema") != "post290.native-observation-checker.v1":
        raise ValueError("unexpected independent checker schema")
    if panel.get("terminal_claim") != "RH_OPEN" or checker.get("terminal_claim") != "RH_OPEN":
        raise ValueError("invalid claim firewall")
    identity = panel.get("source_identity")
    if not isinstance(identity, dict) or not isinstance(identity.get("source_raw_sha256"), str):
        raise ValueError("missing real source identity")
    if checker.get("source_sha256") != identity.get("source_raw_sha256"):
        raise ValueError("native panel/checker source mismatch")
    if panel_path is not None and checker.get("panel_sha256") != digest(panel_path):
        raise ValueError("independent checker did not read these panel bytes")
    if checker_path is not None and checker.get("precision_bits") != 1024:
        raise ValueError("final native checker is not at 1024 bits")
    expected = set(itertools.product(APERTURES, CUTOFFS))
    pairs = panel.get("pairs")
    if not isinstance(pairs, list):
        raise ValueError("missing native pairs")
    seen, errors, unresolved, consistent = set(), [], [], []
    receipts = checker.get("receipts", [])
    if not isinstance(receipts, list):
        raise ValueError("invalid fresh checker receipts")
    receipt_map = {}
    for receipt in receipts:
        key = panel_pair_key(receipt)
        if key in receipt_map:
            raise ValueError("duplicate independent checker pair: " + repr(key))
        receipt_map[key] = receipt
    for record in pairs:
        key = panel_pair_key(record)
        if key in seen:
            raise ValueError("duplicate evaluated pair: " + repr(key))
        if key not in expected:
            raise ValueError("unknown aperture/cutoff pair: " + repr(key))
        seen.add(key)
        rows = record.get("rows", [])
        carriers = [row.get("carrier") for row in rows]
        if len(rows) != 4 or set(carriers) != set(CARRIERS) or len(set(carriers)) != 4:
            errors.append("invalid carrier coverage: " + repr(key))
            continue
        received = receipt_map.get(key, {})
        if record.get("status") != "EVALUATED_NATIVE_PROBE":
            unresolved.append({"pair": list(key), "reason": record.get("status", "UNRESOLVED")})
            continue
        if received.get("status") != "FRESH_1024BIT_CONSISTENT":
            unresolved.append({"pair": list(key), "reason": "fresh independent replay not accepted"})
            continue
        problems = []
        for row in rows:
            if row.get("is_hypothetical_zero_generated_detector") is not False:
                problems.append("invalid generator/probe identity")
            if row.get("status") != "EVALUATED_NATIVE_PROBE":
                problems.append("unevaluated carrier " + str(row.get("carrier")))
            consistency_points(row.get("consistency", {}), str(row.get("carrier")), problems)
        if problems:
            errors.append({"pair": list(key), "problems": problems})
        else:
            consistent.append(list(key))
    missing = sorted(expected - seen)
    if missing:
        unresolved.append({"reason": "missing frozen pair indices", "pairs": [list(k) for k in missing]})
    extra = set(receipt_map) - seen
    if extra:
        errors.append({"reason": "checker data for nonexistent pair", "pairs": [list(k) for k in sorted(extra)]})
    if panel.get("pair_count") != len(pairs) or panel.get("row_count") != 4 * len(pairs):
        errors.append("unfaithful panel pair/row counts")
    if checker.get("verified_pairs") != sum(r.get("status") == "FRESH_1024BIT_CONSISTENT" for r in receipts):
        errors.append("unfaithful fresh-replay count")
    complete = not errors and not unresolved and len(seen) == 44 and len(consistent) == 44
    return {
        "schema": "post290.representation-comparison.v1",
        "claim_cap": "RH_OPEN",
        "source_identity": identity,
        "panel_sha256": digest(panel_path) if panel_path else None,
        "checker_sha256": digest(checker_path) if checker_path else None,
        "representation_classes": ["FINITE_FIXED_NATIVE_PROBE", "SYMBOLIC_CONDITIONAL_STEP123"],
        "prohibited_identification": "finite native probe is not a hypothetical-zero-generated original detector",
        "scope": "44 frozen aperture/cutoff pairs, 176 real-carrier rows; zero comparisons are finite numerical consistency only",
        "consistent_pairs": consistent,
        "consistent_pair_count": len(consistent),
        "unresolved": unresolved,
        "discrepancies": errors,
        "finite_panel_reproduced": complete,
        "source_specific_step4_upper_law": "OPEN",
        "independent_rh_theorem_authority": False,
        "scientific_disposition": "FINITE_PANEL_REPRODUCED_RH_OPEN" if complete else "UNRESOLVED_RH_OPEN",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--panel", type=Path, required=True)
    p.add_argument("--checker", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    result = compare(read(args.panel), read(args.checker),
                     panel_path=args.panel, checker_path=args.checker)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"consistent_pairs": result["consistent_pair_count"],
                      "discrepancies": len(result["discrepancies"]),
                      "unresolved": len(result["unresolved"])}))
    if result["discrepancies"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
