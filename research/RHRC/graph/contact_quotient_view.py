from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
CONFIG = RHRC / "graph" / "CONTACT_QUOTIENT_CONFIG.json"
REGISTERED = RHRC / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
SOURCE_ONLY = RHRC / "integration" / "generated" / "SOURCE_ONLY_CANDIDATE_DEPENDENCIES.jsonl"
OUTPUT = RHRC / "graph" / "generated" / "CONTACT_QUOTIENT_VIEW.json"
PROJECTION = "THEOREM_VALUE_ERASED_SUPPORT"


def fail(message: str) -> None:
    raise SystemExit("contact_quotient_view: " + message)


def load_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def merge_index(*row_sets: list[dict]) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for rows in row_sets:
        for row in rows:
            name = row["declaration"]
            prior = out.get(name)
            if prior is None:
                out[name] = row
                continue
            merged = dict(prior)
            deps = {d["constant"]: d for d in prior.get("dependencies", [])}
            for dep in row.get("dependencies", []):
                if dep["constant"] not in deps:
                    deps[dep["constant"]] = dep
                else:
                    old = deps[dep["constant"]]
                    deps[dep["constant"]] = {
                        "constant": dep["constant"],
                        "used_in_type": old.get("used_in_type", False) or dep.get("used_in_type", False),
                        "used_in_value": old.get("used_in_value", False) or dep.get("used_in_value", False),
                        "used_in_structure": old.get("used_in_structure", False) or dep.get("used_in_structure", False),
                    }
            merged["dependencies"] = sorted(deps.values(), key=lambda x: x["constant"])
            out[name] = merged
    return out


def dependency_closure(index: dict[str, dict], roots: list[str]) -> set[str]:
    pending = list(roots)
    seen: set[str] = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        row = index.get(name)
        if row is None:
            continue
        seen.add(name)
        for dep in row.get("dependencies", []):
            allowed = (
                dep.get("used_in_type")
                or dep.get("used_in_structure")
                or (
                    row.get("declaration_kind") != "THEOREM"
                    and dep.get("used_in_value")
                )
            )
            if allowed and dep["constant"] not in seen:
                pending.append(dep["constant"])
    return seen


def local_only(index: dict[str, dict], names: set[str]) -> set[str]:
    return {
        name
        for name in names
        if name in index and index[name].get("repository_scope") == "LOCAL"
    }


def compact(names: set[str], limit: int = 20) -> dict:
    ordered = sorted(names)
    digest = hashlib.sha256("".join(x + "\n" for x in ordered).encode()).hexdigest()
    return {
        "count": len(ordered),
        "sha256": digest,
        "examples": ordered[:limit],
        "truncated": len(ordered) > limit,
    }


def build() -> dict:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    if config.get("terminal_claim") != "RH_OPEN" or config.get("theorem_promotion") is not False:
        fail("authority firewall drift")
    if config.get("projection") != PROJECTION:
        fail("projection drift")

    registered_rows = load_jsonl(REGISTERED)
    source_rows = load_jsonl(SOURCE_ONLY)
    index = merge_index(registered_rows, source_rows)

    family_supports: dict[str, set[str]] = {}
    for family in config["interface_families"]:
        missing = [name for name in family["anchors"] if name not in index]
        if missing:
            fail(f"missing exact interface anchors for {family['id']}: {missing}")
        family_supports[family["id"]] = local_only(
            index, dependency_closure(index, family["anchors"])
        )

    memberships: Counter[str] = Counter()
    for support in family_supports.values():
        memberships.update(support)
    distinctive = {
        family: {name for name in support if memberships[name] == 1}
        for family, support in family_supports.items()
    }

    roots = [row for row in source_rows if row.get("graph_role") == "SOURCE_ONLY_ROOT"]
    contacts = []
    cross = 0
    for root in sorted(roots, key=lambda row: row["declaration"]):
        declaration = root["declaration"]
        support = local_only(index, dependency_closure(index, [declaration]))
        hits = {
            family: support & family_support
            for family, family_support in distinctive.items()
        }
        active = sorted(family for family, values in hits.items() if values)
        if len(active) >= 2:
            cross += 1
        if active:
            contacts.append({
                "declaration": declaration,
                "module": root.get("module"),
                "active_interfaces": active,
                "contacts": {
                    family: compact(values)
                    for family, values in hits.items()
                    if values
                },
            })

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-VIEW-1.0",
        "status": "RESEARCH_CONTROL_ONLY",
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "projection": PROJECTION,
        "interpretation": (
            "Compiler-dependency contact view only. Cross-interface contact does not "
            "establish theorem composition, independence, mathematical relevance, or RH evidence."
        ),
        "interface_families": {
            family: {
                "support": compact(family_supports[family]),
                "distinctive_support": compact(distinctive[family]),
            }
            for family in sorted(family_supports)
        },
        "source_only_root_count": len(roots),
        "contacting_root_count": len(contacts),
        "cross_interface_root_count": cross,
        "contacts": contacts,
    }


def render(data: dict) -> bytes:
    return (json.dumps(data, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = render(build())

    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_bytes(payload)
        print("contact_quotient_view: WROTE")
        return 0

    current = OUTPUT.read_bytes() if OUTPUT.exists() else None
    if current != payload:
        fail("checked-in/generated contact quotient view is stale or missing")
    print("contact_quotient_view: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
