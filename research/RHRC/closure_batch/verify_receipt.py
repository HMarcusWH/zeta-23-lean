from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any

from interval_codec import DyadicInterval, canonical_json


class ReceiptError(ValueError):
    pass


HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def digest(obj: Any) -> str:
    return hashlib.sha256(canonical_json(obj).encode()).hexdigest()


def plan_digest(plan: dict[str, Any]) -> str:
    return digest(plan)


def _segment_key(seg: dict) -> tuple[int, int, int]:
    return int(seg["lo"]), int(seg["hi"]), int(seg["den"])


def verify_receipt(receipt: dict[str, Any], plan: dict[str, Any]) -> dict[str, Any]:
    if receipt.get("schema_version") != "RHRC-CLOSURE-NUMERICAL-RECEIPT-1.0":
        raise ReceiptError("wrong receipt schema")
    if receipt.get("execution_status") != "SUCCESS":
        raise ReceiptError("execution did not succeed")
    if receipt.get("integrity_status") != "PASS":
        raise ReceiptError("integrity did not pass")
    if receipt.get("research_disposition") == "CONTROL_FAILURE":
        raise ReceiptError("control failure cannot be integrity PASS")
    if receipt.get("terminal_claim") != "RH_OPEN":
        raise ReceiptError("closure campaign receipt may not promote RH")

    source = receipt.get("source") or {}
    if not HEX40.fullmatch(str(source.get("commit", ""))):
        raise ReceiptError("invalid source commit")
    if not HEX40.fullmatch(str(source.get("tree", ""))):
        raise ReceiptError("invalid source tree")

    scope = plan.get("numerical_receipt_scope") or {}
    research_scope = plan.get("research_scope") or {}
    if not scope.get("tracks"):
        raise ReceiptError("empty numerical receipt scope")
    if receipt.get("plan_sha256") != digest(plan):
        raise ReceiptError("plan digest mismatch")
    if receipt.get("scope_sha256") != digest(scope):
        raise ReceiptError("scope digest mismatch")
    if receipt.get("fixture_sha256") != digest(research_scope):
        raise ReceiptError("fixture digest mismatch")
    if not HEX64.fullmatch(str(receipt.get("program_sha256", ""))):
        raise ReceiptError("invalid program digest")

    expected_precision = {
        track: int(spec["precision_bits"])
        for track, spec in scope["tracks"].items()
    }
    if receipt.get("precision_bits") != expected_precision:
        raise ReceiptError("precision schedule mismatch")

    cases = receipt.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ReceiptError("empty receipt cases")
    ids = [str(c.get("id")) for c in cases]
    if len(ids) != len(set(ids)):
        raise ReceiptError("duplicate case id")

    signs = {"POSITIVE": 0, "NEGATIVE": 0, "ZERO_ONLY": 0, "CONTAINS_ZERO": 0}
    seen_a = set()
    seen_b_shell = set()
    seen_ck = set()
    seen_cl = set()

    for case in cases:
        track = case.get("track")
        observable = case.get("observable")
        if track not in expected_precision:
            raise ReceiptError(f"unsupported receipt track {track}")
        if int(case.get("precision_bits", -1)) != expected_precision[track]:
            raise ReceiptError(f"{case.get('id')}: precision mismatch")

        interval = DyadicInterval.from_json(case["interval"])
        sign = interval.sign()
        if case.get("claimed_sign") != sign:
            raise ReceiptError(f"forged sign for {case.get('id')}")
        signs[sign] += 1
        p = case.get("params") or {}

        if track == "A":
            if observable != "lambda_min":
                raise ReceiptError("unsupported A observable")
            seen_a.add((str(p.get("L")), int(p.get("K"))))
        elif track == "B":
            seg = _segment_key(p.get("segment") or {})
            key = (int(p.get("Q")), int(p.get("K")), str(p.get("parity")), seg)
            if observable == "shell_energy":
                seen_b_shell.add(key)
            elif observable == "schur_form_leading_minor":
                if int(p.get("minor_index", -1)) < 0:
                    raise ReceiptError("invalid B minor index")
            else:
                raise ReceiptError("unsupported B observable")
        elif track == "C":
            if observable == "successive_K_delta_abs":
                seen_ck.add((
                    int(p.get("L")), int(p.get("K_from")),
                    int(p.get("K_to")), int(p.get("z_index")),
                ))
            elif observable == "successive_L_delta_abs":
                seen_cl.add((
                    int(p.get("L_from")), int(p.get("L_to")),
                    int(p.get("K")), int(p.get("z_index")),
                ))
            else:
                raise ReceiptError("unsupported C observable")

    rs = research_scope
    expected_a = {(str(rs["A"]["L"]), int(k)) for k in rs["A"]["K"]}
    if seen_a != expected_a:
        raise ReceiptError("A interval coverage mismatch")

    den = int(rs["B"]["segments_per_cell"])
    expected_b = {
        (int(Q), int(K), str(parity), (lo, lo + 1, den))
        for Q in rs["B"]["physical_Q"]
        for K in rs["B"]["successor_K"]
        for parity in rs["B"]["parities"]
        for lo in range(den)
    }
    if seen_b_shell != expected_b:
        raise ReceiptError("B shell interval coverage mismatch")

    z_count = len(rs["C"]["z"])
    expected_ck = {
        (int(L), int(ka), int(kb), zi)
        for L in rs["C"]["L"]
        for ka, kb in zip(rs["C"]["K"], rs["C"]["K"][1:])
        for zi in range(z_count)
    }
    expected_cl = {
        (int(la), int(lb), int(K), zi)
        for la, lb in zip(rs["C"]["L"], rs["C"]["L"][1:])
        for K in rs["C"]["K"]
        for zi in range(z_count)
    }
    if seen_ck != expected_ck:
        raise ReceiptError("C K-delta coverage mismatch")
    if seen_cl != expected_cl:
        raise ReceiptError("C L-delta coverage mismatch")

    expected_summary = {"case_count": len(cases), "sign_counts": signs}
    if receipt.get("summary") != expected_summary:
        raise ReceiptError("summary does not reconstruct from cases")

    return {
        "status": "PASS",
        "case_count": len(cases),
        "sign_counts": signs,
        "terminal_claim": "RH_OPEN",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", required=True)
    ap.add_argument("--receipt", required=True)
    args = ap.parse_args()
    plan = json.loads(Path(args.plan).read_text())
    receipt = json.loads(Path(args.receipt).read_text())
    print(json.dumps(verify_receipt(receipt, plan), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
