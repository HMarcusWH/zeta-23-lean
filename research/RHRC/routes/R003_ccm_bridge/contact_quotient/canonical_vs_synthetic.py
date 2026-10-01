from __future__ import annotations

from staged_rank_audit import staged_audit


def compare() -> dict:
    canonical = staged_audit(canonical=True)
    synthetic = staged_audit(canonical=False)
    synthetic_by_stage = {row["stage"]: row for row in synthetic["stages"]}
    rows = []

    for crow in canonical["stages"]:
        srow = synthetic_by_stage[crow["stage"]]
        rows.append({
            "stage": crow["stage"],
            "canonical_rank": crow["rank"],
            "synthetic_rank": srow["rank"],
            "canonical_minus_synthetic_rank": crow["rank"] - srow["rank"],
            "canonical_nullity": crow["nullity"],
            "synthetic_nullity": srow["nullity"],
        })

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-COMPARISON-1.0",
        "scope": "RELATION_SPACE_ONLY",
        "interpretation": (
            "This comparison identifies exact registered source relations that add "
            "linear independence beyond the generic structural relation family. "
            "It does not show that any instantiated canonical contact state is excluded."
        ),
        "stages": rows,
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(compare(), indent=2, sort_keys=True))
