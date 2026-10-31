"""Checked application interfaces over the preserved OoL operational semantics."""
from __future__ import annotations
from research.RHRC.integration.opica_composition.canonical import require, digest_text, closed_keys

def verify_interfaces(expected: list[dict], received: list[dict], replay) -> tuple[str, ...]:
    require(type(expected) is list and bool(expected) and callable(replay), "expected interfaces and replay required")
    require(type(received) is list, "interface inventory required")
    ids = [r["id"] for r in expected]; got = [r["id"] for r in received]
    require(len(ids) == len(set(ids)) and len(got) == len(set(got)), "duplicate interface")
    require(set(ids) == set(got), "missing or unexpected interface")
    supplied = {r["id"]: r for r in received}
    for wanted in expected:
        row = supplied[wanted["id"]]
        closed_keys(wanted, {"id", "source", "context", "producer", "consumer", "witness", "phase"})
        closed_keys(row, {"id", "source", "context", "producer", "consumer", "witness", "phase", "observed_phase", "receipt", "transport"})
        for field in ("source", "context", "producer", "consumer", "witness", "phase"):
            require(field in wanted and row.get(field) == wanted[field], "interface substitution: " + field)
        require(row.get("phase") == row.get("observed_phase"), "observed phase differs")
        require(bool(row.get("receipt")), "checked binding receipt required")
        if row["producer"] != row["consumer"]:
            require(bool(row.get("transport")), "different objects require a proved transport")
        require(replay(wanted, row) is True, "independent binding replay rejected")
    return tuple(sorted(ids))

def check_context(authorized, used, open_obligations) -> tuple[str, ...]:
    a, u, o = tuple(authorized), tuple(used), tuple(open_obligations)
    for values in (a, u, o):
        require(len(values) == len(set(values)), "duplicate scoped context identity")
        for value in values: digest_text(value)
    require(set(u) <= set(a), "unauthorized premise")
    require(not set(u) & set(o), "open premise used as discharged proof")
    return tuple(sorted(u))

def check_phase(expected: str, observed: str) -> None:
    require(expected in {"DISCOVERY", "CONFIRMATORY_FROZEN"} and observed == expected,
            "observed phase differs from frozen phase")

def validate_route(nodes: list[dict], expected_ids: frozenset[str]) -> None:
    ids = [n["id"] for n in nodes]
    require(len(ids) == len(set(ids)) and set(ids) == set(expected_ids), "route node inventory differs")
    incoming = {n["id"]: tuple(n["inputs"]) for n in nodes}
    require(all(x in incoming for values in incoming.values() for x in values), "dangling route port")
    seen, active = set(), set()
    def visit(node):
        require(node not in active, "circular mathematical justification")
        if node in seen: return
        active.add(node)
        for parent in incoming[node]: visit(parent)
        active.remove(node); seen.add(node)
    for node in incoming: visit(node)

def search_disposition(*, complete: bool, exhausted: bool, proved: bool) -> str:
    require(all(type(v) is bool for v in (complete, exhausted, proved)), "boolean search flags required")
    if proved: return "PROVED_CONDITIONAL"
    if exhausted: return "RESOURCE_EXHAUSTED"
    return "NO_MATCH_IN_GRAMMAR" if complete else "UNRESOLVED_INVENTORY"
