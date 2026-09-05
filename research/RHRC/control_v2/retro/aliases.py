from __future__ import annotations

import json
from pathlib import Path


def load_alias_map(path: Path) -> dict[str, list[str]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return {str(k): [str(x) for x in v] for k, v in data.items()}


def expanded_terms(concept_id: str, aliases: dict[str, list[str]]) -> tuple[str, ...]:
    values = [concept_id, *aliases.get(concept_id, [])]
    # Stable case-insensitive deduplication while preserving the canonical spelling.
    seen: set[str] = set()
    out: list[str] = []
    for value in values:
        key = value.casefold()
        if key not in seen:
            seen.add(key)
            out.append(value)
    return tuple(out)
