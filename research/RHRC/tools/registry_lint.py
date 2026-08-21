from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def _load(path: Path) -> dict:
    return json.loads(path.read_text())


def lint() -> list[str]:
    errors: list[str] = []
    claim_data = _load(ROOT / "CLAIM_REGISTRY.json")
    route_data = _load(ROOT / "routes" / "ROUTE_REGISTRY.json")

    claims = claim_data.get("claims", [])
    routes = route_data.get("routes", [])

    claim_by_id: dict[str, dict] = {}
    for claim in claims:
        cid = claim.get("id")
        if isinstance(cid, str):
            claim_by_id[cid] = claim

    route_by_id: dict[str, dict] = {}
    for route in routes:
        rid = route.get("route_id")
        if not isinstance(rid, str) or not rid:
            errors.append(f"invalid route_id: {rid!r}")
            continue
        if rid in route_by_id:
            errors.append(f"duplicate route_id: {rid}")
            continue
        route_by_id[rid] = route

        route_dir = ROOT / "routes" / rid
        if not route_dir.is_dir():
            errors.append(f"{rid}: registered route directory does not exist: {route_dir.relative_to(REPO)}")

        ids = route.get("claim_ids", [])
        if not isinstance(ids, list) or not all(isinstance(x, str) for x in ids):
            errors.append(f"{rid}: claim_ids must be a list of strings")
            continue
        for cid in ids:
            if cid not in claim_by_id:
                errors.append(f"{rid}: unknown claim_id {cid}")

    for cid, claim in claim_by_id.items():
        rid = claim.get("route")
        if rid is not None:
            if rid not in route_by_id:
                errors.append(f"{cid}: claim route {rid!r} is not registered")
            else:
                listed = route_by_id[rid].get("claim_ids", [])
                if cid not in listed:
                    errors.append(f"{cid}: missing from ROUTE_REGISTRY claim_ids for {rid}")

        if claim.get("status") == "PROVED_UNCONDITIONAL":
            source = claim.get("source")
            if isinstance(source, str) and source and not (REPO / source).is_file():
                errors.append(f"{cid}: Lean source path does not exist: {source}")

    for rid, route in route_by_id.items():
        for cid in route.get("claim_ids", []):
            claim = claim_by_id.get(cid)
            if claim is not None and claim.get("route") != rid:
                errors.append(
                    f"{rid}: claim {cid} declares route {claim.get('route')!r} instead"
                )

    return errors


def main() -> int:
    errors = lint()
    if errors:
        print("RHRC REGISTRY LINT: FAIL")
        for error in errors:
            print(" -", error)
        return 1
    print("RHRC REGISTRY LINT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
