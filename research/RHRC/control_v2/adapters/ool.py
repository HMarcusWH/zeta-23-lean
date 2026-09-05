from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path


@dataclass(frozen=True)
class OoLControlSnapshot:
    kernel_version: str
    registered_route_count: int
    route_states: tuple[tuple[str, str], ...]


def load_ool_snapshot(rhrc_root: Path) -> OoLControlSnapshot:
    reference = json.loads((rhrc_root / "ool" / "OOL_REFERENCE.json").read_text(encoding="utf-8"))
    routes = json.loads((rhrc_root / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
    kernel_version = str(reference.get("kernel_version") or reference.get("version") or "UNKNOWN")
    states: list[tuple[str, str]] = []
    for route in routes.get("routes", []):
        rid = str(route.get("route_id", "UNKNOWN"))
        state = str(route.get("status") or route.get("phase") or "UNKNOWN")
        states.append((rid, state))
    return OoLControlSnapshot(kernel_version, len(states), tuple(sorted(states)))
