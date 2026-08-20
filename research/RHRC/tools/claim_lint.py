from __future__ import annotations

import json
from pathlib import Path

try:
    from .route_closure import Claim, RouteError, dependency_closure
except ImportError:
    from route_closure import Claim, RouteError, dependency_closure

ALLOWED = {
    "PROVED_UNCONDITIONAL", "PROVED_CONDITIONAL", "NUMERICAL", "SYNTHETIC",
    "HEURISTIC", "CONJECTURE", "OPEN", "REFUTED"
}


def load_registry(path: Path) -> list[dict]:
    data = json.loads(path.read_text())
    claims = data.get("claims")
    if not isinstance(claims, list):
        raise ValueError("registry must contain a claims list")
    return claims


def lint(path: Path) -> list[str]:
    raw = load_registry(path)
    errors: list[str] = []
    seen: set[str] = set()
    claims: list[Claim] = []
    caps: dict[str, str] = {}
    by_id: dict[str, dict] = {}

    for item in raw:
        cid = item.get("id")
        status = item.get("status")
        deps = item.get("dependencies", [])
        cap = item.get("promotion_cap")
        if not cid or cid in seen:
            errors.append(f"invalid/duplicate id: {cid!r}")
            continue
        seen.add(cid)
        by_id[cid] = item
        if status not in ALLOWED:
            errors.append(f"{cid}: invalid status {status!r}")
        if cap not in ALLOWED:
            errors.append(f"{cid}: invalid promotion_cap {cap!r}")
        if not isinstance(deps, list) or not all(isinstance(d, str) for d in deps):
            errors.append(f"{cid}: dependencies must be strings")
            deps = []
        claims.append(Claim(cid, status, tuple(deps)))
        caps[cid] = cap

    for c in claims:
        try:
            closure = dependency_closure(c.id, claims)
        except RouteError as exc:
            errors.append(str(exc))
            continue

        ancestors = [x for x in closure if x.id != c.id]
        item = by_id[c.id]

        if c.status == "PROVED_UNCONDITIONAL":
            bad = [x.id for x in ancestors if x.status != "PROVED_UNCONDITIONAL"]
            if bad:
                errors.append(f"{c.id}: unconditional claim depends on non-unconditional {bad}")

            source = item.get("source")
            theorem = item.get("theorem")
            if not isinstance(source, str) or not source:
                errors.append(f"{c.id}: unconditional claim requires a Lean source path")
            elif source.startswith("research/") or not source.endswith(".lean"):
                errors.append(f"{c.id}: unconditional theorem source must be a non-research .lean file")
            if not isinstance(theorem, str) or not theorem:
                errors.append(f"{c.id}: unconditional claim requires a Lean theorem identifier")

        if caps[c.id] == "PROVED_UNCONDITIONAL" and c.status != "PROVED_UNCONDITIONAL":
            errors.append(f"{c.id}: unconditional promotion cap requires unconditional current status")

        if c.id == "C_RH" and c.status != "OPEN":
            bad = [x.id for x in ancestors if x.status != "PROVED_UNCONDITIONAL"]
            if bad:
                errors.append(f"C_RH: cannot leave OPEN while dependencies are not unconditional: {bad}")

    return errors


def main() -> int:
    path = Path(__file__).resolve().parents[1] / "CLAIM_REGISTRY.json"
    errors = lint(path)
    if errors:
        print("RHRC CLAIM LINT: FAIL")
        for e in errors:
            print(" -", e)
        return 1
    print("RHRC CLAIM LINT: PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
