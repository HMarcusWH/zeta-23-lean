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
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]

MUST_STAY_OPEN = {
    "M76_ARITHMETIC_COMPOSITION",
    "OBS060O_STATIONARY_SATURATION_EXCLUSION",
    "M14_BRANCH_EXCLUSION",
    "M32_CANONICAL_GRONWALL_COEFFICIENT",
    "M51_K2_EXACT_LOG16_ENDPOINT",
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
    legacy_domain = {
        "lower_rational": [1, 400],
        "upper_rational": [2772588722239781, 10 ** 15],
        "endpoints_included": True,
        "exact_log16_endpoint_covered": False,
    }
    # log 16 = 8 * sum_{k>=0} 1/((2k+1)*3^(2k+1)); all omitted terms
    # are positive. Exact rational arithmetic proves the legacy cutoff falls
    # below even this finite lower bound, without a numerical evaluator.
    legacy_upper = Fraction(*legacy_domain["upper_rational"])
    log16_lower = 8 * sum(Fraction(1, (2*k+1)*3**(2*k+1)) for k in range(17))
    if not legacy_upper < log16_lower:
        fail("legacy rational upper bound must be strictly below log 16")
    m51 = by_id.get("M51_K2_EVEN_BOTTOM_CERTIFICATE", {})
    dispositions = json.loads((HERE / "EXPERIMENT_DISPOSITIONS.json").read_text(encoding="utf-8"))
    experiment = next((r for r in dispositions["experiments"]
                       if r["id"] == "X285_M51_K2_EVEN_BOTTOM"), {})
    for row in (m51, experiment):
        if (row.get("covered_domain") != legacy_domain or
                row.get("endpoint_obligation") != "M51_K2_EXACT_LOG16_ENDPOINT"):
            fail("legacy M51 evidence must retain its exact rational domain and OPEN endpoint gap")
    endpoint = by_id["M51_K2_EXACT_LOG16_ENDPOINT"]
    if endpoint.get("remaining_domain") != {
        "lower_rational": legacy_domain["upper_rational"], "lower_included": False,
        "upper_symbolic": "log 16", "upper_included": True,
    }:
        fail("legacy M51 remaining domain must be (U, log 16]")
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
