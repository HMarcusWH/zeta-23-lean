"""Disposition firewall for the post-285 ledgers (Steps 108-120, M70-M77).

Fails if the ledgers are stale relative to build_post285_ledgers.py, if any
ledger drops terminal_claim RH_OPEN, if a must-stay-open obligation is marked
otherwise, or if a proof root is not declared with a `#print axioms` receipt in
its source file.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]

MUST_STAY_OPEN = {
    "M65_PRIME_FREE_F04",
    "F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY",
    "M76_ARITHMETIC_COMPOSITION",
    "OBS060O_STATIONARY_SATURATION_EXCLUSION",
    "M14_BRANCH_EXCLUSION",
    "M28_OVERLAP_POSITIVITY",
    "RH",
}
ROOT_STATUSES = {"PROVED_PENDING_CI", "PROVED"}


def fail(msg: str) -> None:
    raise SystemExit(f"POST285 LEDGER CHECK: FAIL\n{msg}")


def main() -> int:
    r = subprocess.run([sys.executable, str(HERE / "build_post285_ledgers.py"), "--check"])
    if r.returncode != 0:
        fail("ledgers are stale; run build_post285_ledgers.py --write")
    for name in ("PROOF_ROOTS.json", "OPEN_OBLIGATIONS.json", "STEP_STATUS_MATRIX.json",
                 "EXPERIMENT_DISPOSITIONS.json"):
        data = json.loads((HERE / name).read_text(encoding="utf-8"))
        if data.get("terminal_claim") != "RH_OPEN":
            fail(f"{name} must keep terminal_claim RH_OPEN")
    obligations = json.loads((HERE / "OPEN_OBLIGATIONS.json").read_text(encoding="utf-8"))
    by_id = {row["id"]: row for row in obligations["obligations"]}
    for oid in MUST_STAY_OPEN:
        if by_id.get(oid, {}).get("status") != "OPEN":
            fail(f"{oid} must remain OPEN")
    roots = json.loads((HERE / "PROOF_ROOTS.json").read_text(encoding="utf-8"))
    if not roots["roots"]:
        fail("no proof roots")
    for row in roots["roots"]:
        src = REPO / row["source"]
        text = src.read_text(encoding="utf-8")
        short = row["declaration"].split("Zeta23.CCM.", 1)[-1]
        if not re.search(rf"(?m)^(theorem|lemma)\s+{re.escape(short)}\b", text):
            fail(f"{row['declaration']} not declared as a theorem in {row['source']}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(row['declaration'])}\s*$", text):
            fail(f"{row['declaration']} has no #print axioms receipt line")
        if row["status"] not in ROOT_STATUSES or row["premises"]:
            fail(f"{row['declaration']} has unexpected status/premises")
    matrix = json.loads((HERE / "STEP_STATUS_MATRIX.json").read_text(encoding="utf-8"))
    steps = [row["step"] for row in matrix["steps"]]
    if steps != list(range(18, 121)):
        fail("step matrix must list Steps 18..120 exactly once")
    print(f"POST285 LEDGER CHECK: PASS ({len(roots['roots'])} roots, {len(steps)} steps)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
