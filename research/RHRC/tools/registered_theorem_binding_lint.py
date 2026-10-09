from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
CLAIMS = ROOT / "CLAIM_REGISTRY.json"
MANIFEST = ROOT / "REGISTERED_THEOREM_BINDINGS.json"
LEAN = REPO / "Zeta23" / "RHRC" / "RegisteredClaimBindings.lean"

EXPECTED_OPEN = {
    "C_RH",
    "R001_PRIME_UPPER",
    "R002_WINDOWED_VISIBILITY",
    "R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES",
    "R003_COMPRESSED_PRODUCTION_C2",
    "R003_WEIGHTED_PRODUCTION_PAIR_BALANCE",
    "R003_INHERITED_FIRST_VARIATION_RESTRICTION",
    "R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER",
}


def fail(message: str) -> None:
    raise SystemExit("registered_theorem_binding_lint: " + message)


def module_from_source(path: str) -> str:
    if path == "Zeta23.lean":
        return "Zeta23"
    if path.startswith("Zeta23/") and path.endswith(".lean"):
        return path[:-5].replace("/", ".")
    if path.startswith("comparator/") and path.endswith(".lean"):
        return path[len("comparator/"):-5].replace("/", ".")
    fail(f"unsupported theorem source path {path!r}")
    raise AssertionError("unreachable")


def main() -> int:
    registry = json.loads(CLAIMS.read_text(encoding="utf-8"))
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    lean = LEAN.read_text(encoding="utf-8")

    claims = registry["claims"]
    proved = {
        c["id"]: c
        for c in claims
        if c.get("status") == "PROVED_UNCONDITIONAL"
    }
    open_ids = {c["id"] for c in claims if c.get("status") == "OPEN"}

    if open_ids != EXPECTED_OPEN:
        fail(
            "OPEN-claim set drift; "
            f"expected={sorted(EXPECTED_OPEN)}, actual={sorted(open_ids)}"
        )

    for claim_id, claim in proved.items():
        if not claim.get("theorem"):
            fail(f"{claim_id} is PROVED_UNCONDITIONAL but has no theorem")
        if not claim.get("source"):
            fail(f"{claim_id} is PROVED_UNCONDITIONAL but has no source")

    if manifest.get("scope") != "ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS":
        fail(f"unexpected manifest scope {manifest.get('scope')!r}")
    if manifest.get("terminal_claim") != "RH_OPEN":
        fail("manifest does not preserve RH_OPEN")
    if manifest.get("candidate_scope") != "OPEN_CANDIDATE_BINDINGS_AUDIT_ONLY_NOT_PROVED_AUTHORITY":
        fail(f"unexpected candidate scope {manifest.get('candidate_scope')!r}")

    rows = manifest["bindings"]
    actual = {row["id"]: row for row in rows}
    candidate_claims = {
        c["id"]: c
        for c in claims
        if c.get("status") == "OPEN"
        and c.get("candidate_binding") is True
        and c.get("theorem")
        and c.get("source")
    }
    candidate_rows = manifest.get("candidate_bindings", [])
    candidate_actual = {row["id"]: row for row in candidate_rows}
    if len(candidate_actual) != len(candidate_rows):
        fail("duplicate claim IDs in registered candidate theorem manifest")
    if set(candidate_actual) != set(candidate_claims):
        fail(
            "candidate manifest/registry drift; "
            f"missing={sorted(set(candidate_claims) - set(candidate_actual))}, "
            f"extra={sorted(set(candidate_actual) - set(candidate_claims))}"
        )
    if len(actual) != len(rows):
        fail("duplicate claim IDs in registered theorem manifest")

    if set(actual) != set(proved):
        fail(
            "manifest/registry proved-claim drift; "
            f"missing={sorted(set(proved) - set(actual))}, "
            f"extra={sorted(set(actual) - set(proved))}"
        )

    expected_modules: set[str] = set()
    for claim_id, claim in proved.items():
        row = actual[claim_id]
        expected = {
            "id": claim_id,
            "theorem": claim["theorem"],
            "source": claim["source"],
        }
        if claim.get("route"):
            expected["route"] = claim["route"]
        if row != expected:
            fail(f"{claim_id} manifest row drift: expected={expected!r}, actual={row!r}")

        theorem = claim["theorem"]
        if not re.search(rf"(?m)^#check\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing exact #check for {theorem}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing exact #print axioms for {theorem}")
        expected_modules.add(module_from_source(claim["source"]))

    for claim_id, claim in candidate_claims.items():
        row = candidate_actual[claim_id]
        expected = {
            "id": claim_id,
            "theorem": claim["theorem"],
            "source": claim["source"],
        }
        if claim.get("route"):
            expected["route"] = claim["route"]
        expected["status"] = "OPEN_PENDING_CI"
        if row != expected:
            fail(
                f"{claim_id} candidate manifest row drift: "
                f"expected={expected!r}, actual={row!r}"
            )
        theorem = claim["theorem"]
        if not re.search(rf"(?m)^#check\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing candidate #check for {theorem}")
        if not re.search(rf"(?m)^#print\s+axioms\s+{re.escape(theorem)}\s*$", lean):
            fail(f"{claim_id} missing candidate #print axioms for {theorem}")
        expected_modules.add(module_from_source(claim["source"]))

    actual_modules = set(re.findall(r"(?m)^import\s+(\S+)\s*$", lean))
    if actual_modules != expected_modules:
        fail(
            "audit import surface drift; "
            f"missing={sorted(expected_modules - actual_modules)}, "
            f"extra={sorted(actual_modules - expected_modules)}"
        )

    for claim_id in EXPECTED_OPEN:
        if claim_id in actual:
            fail(f"OPEN claim was bound as proved: {claim_id}")

    print(
        "registered_theorem_binding_lint: PASS "
        f"({len(proved)} proved bindings; {len(candidate_claims)} OPEN candidate bindings audited; "
        f"{len(open_ids) - len(candidate_claims)} OPEN claims intentionally unbound)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
