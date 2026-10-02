from __future__ import annotations

from feature_registry import active_feature_ids, load_registry


def audit_feature_closure() -> dict:
    data = load_registry()
    feature_ids = set(active_feature_ids(data))
    by_relation = {row["id"]: row for row in data["relations"]}
    rows = []

    for operation in data.get("operation_closure", []):
        rid = operation["relation_id"]
        relation = by_relation.get(rid)
        if relation is None:
            raise AssertionError(f"operation {operation['id']} references missing relation {rid}")
        required = set(operation["required_features"])
        missing_active = sorted(required - feature_ids)
        if missing_active:
            raise AssertionError(
                f"operation {operation['id']} leaves active feature chart: {missing_active}"
            )
        row_features = set(relation["row"])
        missing_row = sorted(required - row_features)
        if missing_row:
            raise AssertionError(
                f"operation {operation['id']} relation omits declared features: {missing_row}"
            )
        rows.append(
            {
                "operation": operation["id"],
                "relation_id": rid,
                "authority": relation["authority"],
                "scope": operation["scope"],
                "required_features": sorted(required),
                "status": "CLOSED_ON_REGISTERED_FEATURE_SURFACE",
            }
        )

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-FEATURE-CLOSURE-1.0",
        "status": "PASS",
        "claim_cap": "CURRENT_REGISTERED_OPERATION_CLOSURE_ONLY",
        "global_basis_completeness": False,
        "operation_count": len(rows),
        "operations": rows,
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "warning": (
            "This certifies only that the declared current operation families stay "
            "inside the registered active feature chart. It does not prove that the "
            "chart is globally complete under all future source/contact operations."
        ),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(audit_feature_closure(), indent=2, sort_keys=True))
