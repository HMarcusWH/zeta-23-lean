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


def plan_digest(plan: dict[str, Any]) -> str:
    return hashlib.sha256(canonical_json(plan).encode()).hexdigest()


def verify_receipt(receipt: dict[str, Any], plan: dict[str, Any]) -> dict[str, Any]:
    if receipt.get("schema_version") != "RHRC-CLOSURE-RECEIPT-1.0":
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
    if receipt.get("plan_sha256") != plan_digest(plan):
        raise ReceiptError("plan digest mismatch")

    required = list(plan.get("receipt_scope", {}).get("required_case_ids", []))
    if not required:
        raise ReceiptError("empty plan scope")

    cases = receipt.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ReceiptError("empty receipt cases")
    ids = [str(c.get("id")) for c in cases]
    if len(ids) != len(set(ids)):
        raise ReceiptError("duplicate case id")
    if sorted(ids) != sorted(required):
        raise ReceiptError("case coverage mismatch")

    signs = {"POSITIVE": 0, "NEGATIVE": 0, "ZERO_ONLY": 0, "CONTAINS_ZERO": 0}
    for case in cases:
        interval = DyadicInterval.from_json(case["interval"])
        sign = interval.sign()
        if case.get("claimed_sign") != sign:
            raise ReceiptError(f"forged sign for {case.get('id')}")
        signs[sign] += 1

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
