from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class RevivalRecord:
    dead_route_id: str
    proposed_route_id: str
    original_blocker: str
    changed_premise: str
    evidence_for_change: tuple[str, ...]

    def validate(self) -> None:
        if not all((self.dead_route_id, self.proposed_route_id, self.original_blocker, self.changed_premise)):
            raise ValueError("revival record fields must be explicit")
        if not self.evidence_for_change:
            raise ValueError("revival requires evidence that the blocking premise changed")


def require_revival_records(dead_route_ids: tuple[str, ...], records: tuple[RevivalRecord, ...]) -> None:
    covered: set[str] = set()
    for record in records:
        record.validate()
        covered.add(record.dead_route_id)
    missing = set(dead_route_ids) - covered
    if missing:
        raise RuntimeError("dead-route resurrection without RevivalRecord: " + ",".join(sorted(missing)))
