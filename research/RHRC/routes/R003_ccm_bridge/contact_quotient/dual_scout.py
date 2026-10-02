from __future__ import annotations

from feature_registry import active_feature_ids, active_relations, load_registry
from symbolic_elimination import matrix_to_strings, nullspace_matrix, quotient_dual


def scout() -> dict:
    registry = load_registry()
    relations = active_relations(registry, canonical=True)
    nullspace = nullspace_matrix(registry, relations)
    dual = quotient_dual(nullspace)
    product = dual * nullspace

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-DUAL-SCOUT-1.0",
        "claim_cap": "DIAGNOSTIC_ONLY",
        "source_derived": False,
        "theorem_authority": False,
        "features": active_feature_ids(registry),
        "relation_ids": [row["id"] for row in relations],
        "nullity": nullspace.cols,
        "nullspace_basis": matrix_to_strings(nullspace),
        "diagnostic_left_inverse": matrix_to_strings(dual),
        "dual_times_nullspace": matrix_to_strings(product),
        "warning": (
            "The left inverse is a coordinate diagnostic analogous to an ESET STEP27 "
            "quotient dual. It is not a source-derived arithmetic theorem."
        ),
        "terminal_claim": "RH_OPEN",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(scout(), indent=2, sort_keys=True))
