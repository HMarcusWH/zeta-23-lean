#!/usr/bin/env python3
"""Fail-closed disposition firewall for the post-284 source campaign.

Checks (no network, standard library only):

* the falsifier-suite JSON (when given) reports every assertion held, keeps
  RH_OPEN, and never labels itself theorem authority;
* the post-284 integration ledgers keep RH_OPEN and keep every non-compiled
  obligation OPEN (in particular F04, OBS-060O, the general-omega Andreief
  inertia lemma, M10, and RH);
* every PROVED root in PROOF_ROOTS.json names a Lean file that exists and
  contains the declaration name and a matching ``#print axioms`` line;
* the attached SymPy falsifier is stored verbatim (SHA-256 pin).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
LEDGER = REPO / "research" / "RHRC" / "integration" / "post284"
ATTACHED = HERE / "POST284_SOURCE_INERTIA_EXACT_FALSIFIER_2026-10-10.py"
ATTACHED_SHA256 = "81008d9f87ef852e6238cb98a3115263cdb859d0851411318e26260edc3e81af"

MUST_STAY_OPEN = {
    "F04_PRODUCTION_DERIVATIVE_AUTHORITY",
    "OBS060O_STATIONARY_SATURATION_EXCLUSION",
    "M17_GENERAL_OMEGA_ANDREIEF_INERTIA",
    "M10_NINTH_ORDER_OPTIMIZED_SCHUR_JUMP",
    "RH",
}


def fail(msg: str) -> None:
    raise SystemExit("check_post284_dispositions: FAIL: " + msg)


def check_suite(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("overall") != "ALL_ASSERTIONS_HELD":
        fail("falsifier suite did not report ALL_ASSERTIONS_HELD")
    if data.get("terminal_claim") != "RH_OPEN":
        fail("falsifier suite terminal claim drift")
    if "NOT LEAN THEOREM AUTHORITY" not in data.get("authority", ""):
        fail("falsifier suite must disclaim theorem authority")
    for key, block in data.items():
        if isinstance(block, dict) and "disposition" in block:
            if "PROVED" in block["disposition"].upper().replace("NOT_LEAN", ""):
                fail(f"{key} disposition must not claim PROVED")


def check_ledgers() -> None:
    for name in ("BASELINE.json", "SOURCE_CLOSURE_AUDIT.json", "PROOF_ROOTS.json",
                 "OPEN_OBLIGATIONS.json", "CLAIM_MIGRATION_MATRIX.json",
                 "EXPERIMENT_DISPOSITIONS.json", "WORKFLOW_HARVEST.json"):
        if not (LEDGER / name).is_file():
            fail(f"missing ledger {name}")
    for name in ("BASELINE.json", "OPEN_OBLIGATIONS.json", "PROOF_ROOTS.json",
                 "CLAIM_MIGRATION_MATRIX.json", "EXPERIMENT_DISPOSITIONS.json"):
        data = json.loads((LEDGER / name).read_text(encoding="utf-8"))
        if data.get("terminal_claim") != "RH_OPEN":
            fail(f"{name} must keep terminal_claim RH_OPEN")
    obligations = json.loads((LEDGER / "OPEN_OBLIGATIONS.json").read_text(encoding="utf-8"))
    by_id = {row["id"]: row for row in obligations["obligations"]}
    for oid in MUST_STAY_OPEN:
        if by_id.get(oid, {}).get("status") != "OPEN":
            fail(f"{oid} must remain OPEN")
    audit = json.loads((LEDGER / "SOURCE_CLOSURE_AUDIT.json").read_text(encoding="utf-8"))
    if audit.get("decision") != "PROVENANCE_ONLY_FALLBACK" or audit["adapter"]["created"]:
        fail("external 7/8 theorem must remain provenance-only until locally compiled")
    roots = json.loads((LEDGER / "PROOF_ROOTS.json").read_text(encoding="utf-8"))
    for row in roots["roots"]:
        src = REPO / row["source"]
        if not src.is_file():
            fail(f"missing source {row['source']}")
        text = src.read_text(encoding="utf-8")
        short = row["declaration"].split("Zeta23.CCM.", 1)[-1]
        if not re.search(rf"(?m)^(theorem|lemma)\s+{re.escape(short)}\b", text):
            fail(f"{row['declaration']} not declared in {row['source']}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(row['declaration'])}\s*$", text):
            fail(f"{row['declaration']} has no #print axioms receipt line")
        if row.get("status") not in {"PROVED_PENDING_CI", "PROVED", "CONDITIONAL_PROVED_PENDING_CI"}:
            fail(f"{row['declaration']} has unexpected status {row.get('status')!r}")
        if row.get("status", "").startswith("CONDITIONAL") and not row.get("premises"):
            fail(f"{row['declaration']} is conditional but lists no premises")


def check_attached() -> None:
    digest = hashlib.sha256(ATTACHED.read_bytes()).hexdigest()
    if digest != ATTACHED_SHA256:
        fail("attached falsifier is not the verbatim handoff receipt")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", type=Path, default=None)
    args = ap.parse_args()
    check_attached()
    check_ledgers()
    if args.suite is not None:
        check_suite(args.suite)
    print("check_post284_dispositions: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
