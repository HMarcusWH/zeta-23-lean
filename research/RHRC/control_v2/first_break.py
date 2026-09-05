from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class FirstBreak:
    break_id: str
    route_id: str
    statement: str
    test_id: str
    estimated_cost: float
    decisive_if_failed: bool
    decisive_if_passed: bool = False


def rank_first_breaks(candidates: list[FirstBreak]) -> list[FirstBreak]:
    """Prefer cheap tests which can decisively kill a route."""
    return sorted(
        candidates,
        key=lambda item: (
            not item.decisive_if_failed,
            item.estimated_cost,
            item.break_id,
        ),
    )
