from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
CONFIG = RHRC / "ool" / "configs" / "rhkg_phase_atlas_v2.json"
SOURCE_ONLY = RHRC / "integration" / "generated" / "RH_CORE_SOURCE_ONLY_THEOREMS.jsonl"
SOURCE_DEPS = RHRC / "integration" / "generated" / "SOURCE_ONLY_CANDIDATE_DEPENDENCIES.jsonl"
REGISTERED_DEPS = RHRC / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
REGISTERED_BINDINGS = RHRC / "REGISTERED_THEOREM_BINDINGS.json"
FFBBP = RHRC / "ffbbp" / "generated" / "RHKG_CANDIDATE_REDUCTION_ASSURANCE.json"
FRONTIERS = RHRC / "graph" / "generated" / "DEPENDENCY_PROJECTION_FRONTIERS.json"
CONTACTS = RHRC / "ool" / "generated" / "RHKG_OOL_ROUTE_CONTACTS.jsonl"
REPORT = RHRC / "ool" / "generated" / "RHKG_OOL_PHASE_ATLAS.json"

CONTACT_SCHEMA = "RHRC-OOL-RHKG-route-contact-1.0"
REPORT_SCHEMA = "RHRC-OOL-RHKG-phase-atlas-report-2.0"
PROJECTION = "THEOREM_VALUE_ERASED_SUPPORT"


def fail(message: str) -> None:
    raise SystemExit("rhkg_phase_atlas: " + message)


def load_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def digest_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_names(names: set[str] | list[str]) -> str:
    payload = "".join(name + "\n" for name in sorted(names)).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def index_receipt(rows: list[dict]) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for row in rows:
        name = row["declaration"]
        if name in out:
            fail(f"duplicate compiler declaration in receipt: {name}")
        out[name] = row
    return out


def dependency_closure(
    index: dict[str, dict],
    roots: list[str] | tuple[str, ...],
    projection: str,
) -> set[str]:
    if projection not in {"ANY", PROJECTION}:
        raise ValueError(f"unsupported projection: {projection}")
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
            if projection == "ANY":
                allowed = (
                    dep.get("used_in_type")
                    or dep.get("used_in_value")
                    or dep.get("used_in_structure")
                )
            else:
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


def distinctive_supports(family_supports: dict[str, set[str]]) -> dict[str, set[str]]:
    memberships: Counter[str] = Counter()
    for support in family_supports.values():
        memberships.update(support)
    return {
        family: {name for name in support if memberships[name] == 1}
        for family, support in family_supports.items()
    }


def classify_disposition(
    projected_contacts: dict[str, set[str]],
    proof_body_only_contacts: dict[str, set[str]],
    frontier_hits: set[str],
) -> str:
    if frontier_hits:
        return "THEOREM_VALUE_ERASED_FRONTIER_CONTACT"
    projected_families = [name for name, hits in projected_contacts.items() if hits]
    if len(projected_families) >= 2:
        return "CROSS_INTERFACE_PROJECTED_CONTACT"
    if len(projected_families) == 1:
        return "SINGLE_INTERFACE_PROJECTED_CONTACT"
    if any(proof_body_only_contacts.values()):
        return "PROOF_BODY_ONLY_CONTACT"
    return "NO_ACTIVE_INTERFACE_CONTACT"


def compact_set(names: set[str], limit: int = 20) -> dict:
    ordered = sorted(names)
    return {
        "count": len(ordered),
        "sha256": digest_names(names),
        "examples": ordered[:limit],
        "truncated": len(ordered) > limit,
    }


def find_frontier_probe(data: dict, config: dict) -> tuple[set[str], dict]:
    projection = next(
        (row for row in data.get("projections", []) if row.get("projection") == PROJECTION),
        None,
    )
    if projection is None:
        fail("theorem-value-erased frontier projection missing")
    probe = projection.get("pair_probe")
    if not isinstance(probe, dict):
        fail("theorem-value-erased pair probe missing")
    expected = config["theorem_value_erased_frontier_probe"]
    if probe.get("left_claim_id") != expected["left_claim_id"]:
        fail("frontier left claim drift")
    if probe.get("right_claim_id") != expected["right_claim_id"]:
        fail("frontier right claim drift")
    declarations: set[str] = set()
    for edge in probe.get("cross_region_edges", []):
        if edge.get("bridge_candidate_eligible") is True:
            declarations.add(edge["source"])
            declarations.add(edge["target"])
    return declarations, probe


def build() -> tuple[list[dict], dict]:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    if config.get("terminal_claim") != "RH_OPEN" or config.get("theorem_promotion") is not False:
        fail("config authority firewall drift")
    if config.get("projection") != PROJECTION:
        fail("atlas projection drift")
    families = config.get("interface_families", [])
    family_ids = [row["id"] for row in families]
    if len(family_ids) != len(set(family_ids)):
        fail("duplicate interface-family id")
    claim_ids = [cid for family in families for cid in family["claim_ids"]]
    if len(claim_ids) != len(set(claim_ids)):
        fail("interface families must use disjoint anchor claim IDs")

    candidates = load_jsonl(SOURCE_ONLY)
    by_candidate_name = {row["resolved_full_name"]: row for row in candidates}
    if len(by_candidate_name) != len(candidates):
        fail("source-only candidate identity drift")

    ffbbp = json.loads(FFBBP.read_text(encoding="utf-8"))
    required_ffbbp = config["ffbbp"]
    if ffbbp.get("selected_reduction") != required_ffbbp["required_selected_reduction"]:
        fail("FFBBP selected reduction drift")
    if ffbbp["reductions"][ffbbp["selected_reduction"]]["assurance_gate"]["passed"] is not True:
        fail("FFBBP selected reduction is not assured")

    candidate_dep_rows = load_jsonl(SOURCE_DEPS)
    candidate_index = index_receipt(candidate_dep_rows)
    root_rows = [row for row in candidate_dep_rows if row.get("graph_role") == "SOURCE_ONLY_ROOT"]
    if len(root_rows) != len(candidates):
        fail("source-only dependency-root count drift")
    root_names = {row["declaration"] for row in root_rows}
    if root_names != set(by_candidate_name):
        fail("source-only dependency roots do not match exactified candidate identities")

    registered_rows = load_jsonl(REGISTERED_DEPS)
    registered_index = index_receipt(registered_rows)
    bindings = json.loads(REGISTERED_BINDINGS.read_text(encoding="utf-8"))["bindings"]
    theorem_by_claim = {row["id"]: row["theorem"] for row in bindings}
    missing_claims = sorted(set(claim_ids) - set(theorem_by_claim))
    if missing_claims:
        fail(f"interface anchor claims are not registered: {missing_claims}")

    family_supports: dict[str, set[str]] = {}
    for family in families:
        roots = [theorem_by_claim[cid] for cid in family["claim_ids"]]
        closure = dependency_closure(registered_index, roots, PROJECTION)
        family_supports[family["id"]] = local_only(registered_index, closure)
    distinctive = distinctive_supports(family_supports)

    frontier_data = json.loads(FRONTIERS.read_text(encoding="utf-8"))
    frontier_declarations, frontier_probe = find_frontier_probe(frontier_data, config)

    contacts: list[dict] = []
    disposition_counts: Counter[str] = Counter()
    interface_counts: Counter[str] = Counter()
    frontier_count = 0

    for declaration in sorted(root_names):
        candidate = by_candidate_name[declaration]
        projected = local_only(
            candidate_index,
            dependency_closure(candidate_index, [declaration], PROJECTION),
        )
        any_support = local_only(
            candidate_index,
            dependency_closure(candidate_index, [declaration], "ANY"),
        )

        projected_contacts = {
            family: projected & support
            for family, support in distinctive.items()
        }
        proof_body_only_contacts = {
            family: (any_support & support) - projected_contacts[family]
            for family, support in distinctive.items()
        }
        frontier_hits = projected & frontier_declarations
        disposition = classify_disposition(
            projected_contacts,
            proof_body_only_contacts,
            frontier_hits,
        )
        disposition_counts[disposition] += 1
        if frontier_hits:
            frontier_count += 1
        for family, hits in projected_contacts.items():
            if hits:
                interface_counts[family] += 1

        contacts.append(
            {
                "schema_version": CONTACT_SCHEMA,
                "terminal_claim": "RH_OPEN",
                "theorem_promotion": False,
                "claim_cap": "DISCOVERY_ONLY",
                "projection": PROJECTION,
                "candidate": {
                    "source_declaration_id": candidate["source_declaration_id"],
                    "declaration": declaration,
                    "module": candidate["module"],
                    "path": candidate["path"],
                    "line": candidate["line"],
                    "compiler_type_sha256": candidate["compiler_type_sha256"],
                    "ffbbp_cohort_key": [
                        candidate["module"],
                        candidate["visibility_class"],
                    ],
                },
                "disposition": disposition,
                "projected_local_support": compact_set(projected),
                "interface_contacts": {
                    family: {
                        "projected": compact_set(projected_contacts[family]),
                        "proof_body_only": compact_set(proof_body_only_contacts[family]),
                    }
                    for family in sorted(distinctive)
                },
                "theorem_value_erased_frontier_contact": compact_set(frontier_hits),
            }
        )

    report = {
        "schema_version": REPORT_SCHEMA,
        "status": "RESEARCH_CONTROL_ONLY",
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
        "ool_kernel_version": config["ool_kernel_version"],
        "mode": config["mode"],
        "claim_cap": config["claim_cap"],
        "projection": PROJECTION,
        "interpretation": (
            f"Exact compiler-support contact atlas over {len(candidates)} source-only public theorem/lemma roots. "
            "Contacts are discovery-only and do not establish theorem composition, mathematical implication, relevance ranking, or RH evidence."
        ),
        "input_snapshot": {
            "source_only_candidate_count": len(candidates),
            "ffbbp_selected_reduction": ffbbp["selected_reduction"],
            "ffbbp_source_only_module_cohort_count": ffbbp["source_only_module_cohort_count"],
            "source_only_candidate_sha256": digest_path(SOURCE_ONLY),
            "source_only_dependency_sha256": digest_path(SOURCE_DEPS),
            "registered_dependency_sha256": digest_path(REGISTERED_DEPS),
            "ffbbp_assurance_sha256": digest_path(FFBBP),
            "projection_frontiers_sha256": digest_path(FRONTIERS),
        },
        "interface_families": {
            family: {
                "support": compact_set(family_supports[family]),
                "distinctive_support": compact_set(distinctive[family]),
                "candidate_projected_contact_count": interface_counts[family],
            }
            for family in sorted(family_supports)
        },
        "frontier_probe": {
            "left_claim_id": frontier_probe["left_claim_id"],
            "right_claim_id": frontier_probe["right_claim_id"],
            "eligible_cross_region_edge_count": frontier_probe["eligible_cross_region_edge_count"],
            "eligible_declaration_surface": compact_set(frontier_declarations),
            "candidate_projected_frontier_contact_count": frontier_count,
        },
        "disposition_counts": dict(sorted(disposition_counts.items())),
        "candidate_count": len(contacts),
        "claim_firewall": [
            "module identity is not an OoL handoff",
            "FFBBP cohort membership is navigation only",
            "type digest equality is not semantic equivalence",
            "proof-body-only contact is separated from theorem-value-erased support",
            "cross-interface support contact is not theorem composition",
            "theorem-value-erased frontier contact is not mathematical implication",
            "OoL output does not create PROVED authority",
            "RH remains OPEN",
        ],
    }
    return contacts, report


def render_jsonl(rows: list[dict]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
        for row in rows
    ).encode("utf-8")


def render_json(data: dict) -> bytes:
    return (json.dumps(data, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build/check OoL RHKG Phase Atlas")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    contacts, report = build()
    products = {
        CONTACTS: render_jsonl(contacts),
        REPORT: render_json(report),
    }

    if args.write:
        CONTACTS.parent.mkdir(parents=True, exist_ok=True)
        for path, payload in products.items():
            path.write_bytes(payload)
        print(
            "rhkg_phase_atlas: WROTE "
            f"{report['candidate_count']} candidate contacts; "
            f"frontier_contacts={report['frontier_probe']['candidate_projected_frontier_contact_count']}"
        )
        return 0

    stale = [
        str(path.relative_to(REPO))
        for path, payload in products.items()
        if not path.exists() or path.read_bytes() != payload
    ]
    if stale:
        fail(f"checked-in OoL Phase Atlas products are stale: {stale}")
    print(
        "rhkg_phase_atlas: PASS "
        f"({report['candidate_count']} candidates; "
        f"frontier_contacts={report['frontier_probe']['candidate_projected_frontier_contact_count']})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
