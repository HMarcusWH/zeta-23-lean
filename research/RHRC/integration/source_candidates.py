from __future__ import annotations

from collections import Counter

THEOREM_SOURCE_KINDS = {"THEOREM", "LEMMA"}


def select_rh_core_theorem_sources(rows: list[dict]) -> list[dict]:
    return sorted(
        (
            row
            for row in rows
            if row.get("trust_zone") == "RH_FORMAL_CORE"
            and row.get("command_kind") in THEOREM_SOURCE_KINDS
        ),
        key=lambda row: (
            row["module"],
            int(row.get("line", 0)),
            row["declared_name"],
            row["id"],
        ),
    )


def classify_visibility(
    compiler_result: dict,
    compiler_closure_by_name: dict[str, dict],
) -> tuple[str, str | None]:
    status = compiler_result["resolution_status"]
    if status == "AMBIGUOUS_COMPILER_MATCH":
        return "AMBIGUOUS_SOURCE_IDENTITY", None
    if status == "NO_COMPILER_MATCH":
        return "UNRESOLVED_SOURCE_IDENTITY", None
    if status == "KIND_MISMATCH":
        return "KIND_MISMATCH", None
    if status == "RESOLVED_PRIVATE_OR_INTERNAL":
        return "PRIVATE_OR_INTERNAL_SOURCE_OBJECT", None
    if status != "RESOLVED_UNIQUE":
        raise ValueError(f"unknown candidate resolution status: {status}")

    name = compiler_result["resolved_full_name"]
    row = compiler_closure_by_name.get(name)
    if row is None:
        return "SOURCE_ONLY_PUBLIC_THEOREM", None
    if row["graph_role"] == "REGISTERED_CLAIM_ROOT":
        return "ALREADY_REGISTERED_ROOT", row.get("registered_claim_id")
    return "ALREADY_IN_REGISTERED_DEPENDENCY_CLOSURE", None


def summarize(receipts: list[dict]) -> dict:
    visibility = Counter(row["visibility_class"] for row in receipts)
    resolution = Counter(row["resolution_status"] for row in receipts)
    return {
        "schema_version": "RHRC-source-candidate-summary-1.0",
        "scope": "RH_FORMAL_CORE_THEOREM_AND_LEMMA_SOURCE_SURFACE",
        "candidate_count": len(receipts),
        "visibility_counts": dict(sorted(visibility.items())),
        "resolution_counts": dict(sorted(resolution.items())),
        "source_only_public_theorem_count": visibility.get(
            "SOURCE_ONLY_PUBLIC_THEOREM", 0
        ),
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "interpretation": (
            "Compiler identity exactification of source-discovery candidates only; "
            "source-only status does not imply mathematical independence or relevance."
        ),
    }
