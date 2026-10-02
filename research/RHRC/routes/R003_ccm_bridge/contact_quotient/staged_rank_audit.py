from __future__ import annotations

from feature_registry import active_feature_ids, active_relations, load_registry
from symbolic_elimination import exact_rank


def staged_audit(*, canonical: bool) -> dict:
    registry = load_registry()
    features = active_feature_ids(registry)
    eligible = active_relations(registry, canonical=canonical)
    selected: list[dict] = []
    stages = []

    for stage in registry["stage_order"]:
        selected.extend(row for row in eligible if row["stage"] == stage)
        rank = exact_rank(registry, selected)
        previous = stages[-1]["rank"] if stages else 0
        stages.append({
            "stage": stage,
            "rows": len(selected),
            "rank": rank,
            "nullity": len(features) - rank,
            "incremental_rank_gain": rank - previous,
            "relation_ids": [row["id"] for row in selected],
        })

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-RANK-1.0",
        "scope": "CANONICAL_RELATION_SPACE" if canonical else "GENERIC_SYNTHETIC_RELATION_SPACE",
        "rank_semantics": "EXACT_SYMBOLIC_RELATION_RANK_NOT_POINTWISE_CONTACT_EXCLUSION",
        "feature_count": len(features),
        "features": features,
        "stages": stages,
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(staged_audit(canonical=True), indent=2, sort_keys=True))
