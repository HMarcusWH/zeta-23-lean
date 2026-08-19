from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Set

UNCONDITIONAL = "PROVED_UNCONDITIONAL"
CONDITIONAL = {"PROVED_CONDITIONAL", "CONJECTURE"}
DIAGNOSTIC = {"NUMERICAL", "SYNTHETIC", "HEURISTIC"}

@dataclass(frozen=True)
class Claim:
    id: str
    status: str
    dependencies: tuple[str, ...] = ()

class RouteError(ValueError):
    pass

def _index(claims: Iterable[Claim]) -> Dict[str, Claim]:
    out: Dict[str, Claim] = {}
    for c in claims:
        if c.id in out:
            raise RouteError(f"duplicate claim id: {c.id}")
        out[c.id] = c
    return out

def dependency_closure(claim_id: str, claims: Iterable[Claim]) -> List[Claim]:
    idx = _index(claims)
    if claim_id not in idx:
        raise RouteError(f"unknown claim: {claim_id}")
    visiting: Set[str] = set()
    seen: Set[str] = set()
    order: List[Claim] = []

    def visit(cid: str) -> None:
        if cid in visiting:
            raise RouteError(f"dependency cycle involving {cid}")
        if cid in seen:
            return
        if cid not in idx:
            raise RouteError(f"unknown dependency: {cid}")
        visiting.add(cid)
        claim = idx[cid]
        for dep in claim.dependencies:
            visit(dep)
        visiting.remove(cid)
        seen.add(cid)
        order.append(claim)

    visit(claim_id)
    return order

def contamination(claim_id: str, claims: Iterable[Claim]) -> dict:
    closure = dependency_closure(claim_id, claims)
    conditional = [c.id for c in closure if c.status in CONDITIONAL]
    diagnostic = [c.id for c in closure if c.status in DIAGNOSTIC]
    open_or_refuted = [c.id for c in closure if c.status in {"OPEN", "REFUTED"}]
    return {
        "conditional": conditional,
        "diagnostic": diagnostic,
        "open_or_refuted": open_or_refuted,
        "unconditionally_closed": all(c.status == UNCONDITIONAL for c in closure),
    }
