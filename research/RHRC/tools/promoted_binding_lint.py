from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
CLAIMS = ROOT / "CLAIM_REGISTRY.json"
MANIFEST = ROOT / "R003_PROMOTED_BINDINGS.json"
LEAN = REPO / "Zeta23" / "CCM" / "ClaimBindings.lean"


def fail(message: str) -> None:
    raise SystemExit("promoted_binding_lint: " + message)


def main() -> int:
    registry = json.loads(CLAIMS.read_text(encoding="utf-8"))
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    lean = LEAN.read_text(encoding="utf-8")
    expected = {
        c["id"]: c["theorem"]
        for c in registry["claims"]
        if c.get("route") == "R003_ccm_bridge"
        and c.get("status") == "PROVED_UNCONDITIONAL"
        and c.get("theorem")
    }
    actual = {row["id"]: row["theorem"] for row in manifest["bindings"]}
    candidate_expected = {
        c["id"]: c["theorem"]
        for c in registry["claims"]
        if c.get("route") == "R003_ccm_bridge"
        and c.get("status") == "OPEN"
        and c.get("candidate_binding") is True
        and c.get("theorem")
    }
    candidate_rule = manifest.get("candidate_rule")
    if not isinstance(candidate_rule, str) or "not promoted theorem authority" not in candidate_rule:
        fail("candidate binding rule missing fail-closed non-promotion language")
    candidate_rows = manifest.get("candidate_bindings", [])
    candidate_actual = {row["id"]: row for row in candidate_rows}
    if len(candidate_actual) != len(candidate_rows):
        fail("duplicate candidate claim IDs in R003 candidate bindings")
    if set(candidate_expected) != set(candidate_actual):
        missing = sorted(set(candidate_expected) - set(candidate_actual))
        extra = sorted(set(candidate_actual) - set(candidate_expected))
        fail(f"candidate manifest/registry ID drift; missing={missing}, extra={extra}")
    for claim_id, theorem in candidate_expected.items():
        row = candidate_actual[claim_id]
        if row.get("theorem") != theorem:
            fail(f"{claim_id} candidate theorem mismatch: registry={theorem!r}, manifest={row.get('theorem')!r}")
        if row.get("status") != "OPEN_PENDING_CI":
            fail(f"{claim_id} candidate binding must remain OPEN_PENDING_CI before promotion")
        if not re.search(rf"(?m)^#check\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing candidate #check for {theorem}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing candidate #print axioms for {theorem}")
    if set(expected) != set(actual):
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        fail(f"manifest/registry ID drift; missing={missing}, extra={extra}")
    for claim_id, theorem in expected.items():
        if actual[claim_id] != theorem:
            fail(f"{claim_id} theorem mismatch: registry={theorem!r}, manifest={actual[claim_id]!r}")
        if not re.search(rf"(?m)^#check\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing exact #check for {theorem}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing exact #print axioms for {theorem}")
    print(
        "promoted_binding_lint: PASS "
        f"({len(expected)} PROVED_UNCONDITIONAL R003 bindings; "
        f"{len(candidate_expected)} OPEN candidate bindings audited)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
