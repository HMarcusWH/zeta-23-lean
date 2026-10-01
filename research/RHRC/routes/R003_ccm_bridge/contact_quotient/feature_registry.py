from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REGISTRY = HERE / "feature_registry.json"

VALID_AUTHORITIES = {"PROVED_LEAN", "PAPER_DERIVED_NOT_LEAN", "DIAGNOSTIC_ONLY"}
VALID_SCOPES = {"GENERIC_SHARED", "CANONICAL_ONLY"}


def load_registry(path: Path = REGISTRY) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    validate_registry(data)
    return data


def validate_registry(data: dict) -> None:
    if data.get("terminal_claim") != "RH_OPEN":
        raise ValueError("contact quotient registry must preserve RH_OPEN")
    if data.get("theorem_promotion") is not False:
        raise ValueError("contact quotient registry may not promote theorems")

    features = data.get("features", [])
    ids = [row["id"] for row in features]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate feature id")
    feature_ids = set(ids)

    stage_order = data.get("stage_order", [])
    if len(stage_order) != len(set(stage_order)):
        raise ValueError("duplicate stage")

    relation_ids: set[str] = set()
    for relation in data.get("relations", []):
        rid = relation["id"]
        if rid in relation_ids:
            raise ValueError(f"duplicate relation id: {rid}")
        relation_ids.add(rid)
        if relation.get("authority") not in VALID_AUTHORITIES:
            raise ValueError(f"invalid authority on {rid}")
        if relation.get("scope") not in VALID_SCOPES:
            raise ValueError(f"invalid scope on {rid}")
        if relation.get("stage") not in stage_order:
            raise ValueError(f"unknown stage on {rid}")
        unknown = sorted(set(relation.get("row", {})) - feature_ids)
        if unknown:
            raise ValueError(f"unknown features on {rid}: {unknown}")

    for relation in data.get("paper_relations", []):
        if relation.get("authority") != "PAPER_DERIVED_NOT_LEAN":
            raise ValueError("paper relation attempted authority upgrade")


def active_feature_ids(data: dict) -> list[str]:
    return [row["id"] for row in data["features"] if row.get("default_active") is True]


def active_relations(data: dict, *, canonical: bool) -> list[dict]:
    out = []
    for row in data["relations"]:
        if row["authority"] != "PROVED_LEAN":
            continue
        if not canonical and row["scope"] != "GENERIC_SHARED":
            continue
        out.append(row)
    return out
