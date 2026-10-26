"""Scoped control dispatch; historical controls never become fresh executions."""
from __future__ import annotations

import argparse
from collections.abc import Callable
from copy import deepcopy
from pathlib import Path
from typing import Any

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, require
    from .finite_baseline import HERE, check_filtered_baseline, verify_filtered_baseline, verify_native_jump_minor
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, require
    from finite_baseline import HERE, check_filtered_baseline, verify_filtered_baseline, verify_native_jump_minor


# Audited A21/A22 component split. Evidence and disposition may evolve; the
# normative clause scopes and linked control requirements need a reviewed amendment.
CONTROL_PLAN_SHA256 = "530606e59ec5d601701366d9a3840b5dbbd46d9b766e26f28eb31e8edc2a5bfd"


def control_plan_fingerprint(families: list[dict[str, Any]]) -> str:
    rows = deepcopy(families)
    for family in rows:
        for key in ("activation", "all_clause_acceptance_false", "source_pinned_receipt",
                    "unchanged_normative_record_ref", "source_package_normative_ref"):
            family.pop(key, None)
        for clause in family["components"]:
            clause.pop("acceptance", None)
            for link in clause["controls"]:
                link.pop("actual_evidence", None)
                link.pop("resolved_theorem_or_replay_reference", None)
    return canonical_sha256(rows)


def finite_mutation_controls(fixture: dict[str, Any]) -> list[dict[str, Any]]:
    """Current exact input/refusal controls, not 21 additional mathematical theorems."""
    variants = [
        ("wrong source", "source", "Q squared"),
        ("wrong filter", "filter", "2^-N I"),
        ("wrong tree", "source_tree", "0" * 40),
        ("wrong commit", "source_commit", "0" * 40),
        ("zero lower", "lower_square", "0"),
        ("forged upper", "upper_square", "0"),
        ("wrong coefficient", "coefficients", ["1", "-1", "-1", "-1"]),
        ("boolean rational", "coefficients", [True, "-1", "-1", "-2/3"]),
        ("zero denominator", "coefficients", ["1/0", "-1", "-1", "-2/3"]),
        ("noncanonical rational", "coefficients", ["2/2", "-1", "-1", "-2/3"]),
        ("wrong region", "region", {"delta": ["0", "3/8"], "abs_tau": ["1", "2"]}),
        ("boolean horizon", "tail_start", True),
        ("wrong horizon", "tail_start", 47),
        ("authority escalation", "authority", "KERNEL_CHECKED_THEOREM"),
        ("RH escalation", "RH", "PROVED"),
        ("unknown schema", "schema", "unknown"),
    ]
    cases: list[tuple[str, dict[str, Any]]] = []
    for name, key, value in variants:
        mutated = deepcopy(fixture)
        mutated[key] = value
        cases.append((name, mutated))
    extra = deepcopy(fixture)
    extra["ignored"] = 1
    cases.append(("extra field", extra))
    missing = deepcopy(fixture)
    del missing["source"]
    cases.append(("missing source", missing))
    results = []
    for name, mutated in cases:
        try:
            check_filtered_baseline(mutated)
        except (InvalidCertificate, ValueError, TypeError) as exc:
            results.append({"case": name, "expected": "REJECT", "actual": "REJECT",
                            "passed": True, "error_code": getattr(exc, "code", type(exc).__name__),
                            "evidence_class": "RUNTIME_NEGATIVE_FIXTURE",
                            "scope": "Frozen finite input and evidence rejection; not an analytic counterexample"})
        else:
            raise InvalidCertificate("mutation_accepted", "Independent finite checker accepted " + name)
    for text in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
        try:
            loads_strict_json(text)
        except InvalidCertificate as exc:
            results.append({"case": "JSON rejection " + text, "expected": "REJECT", "actual": "REJECT",
                            "passed": True, "error_code": exc.code,
                            "evidence_class": "RUNTIME_NEGATIVE_FIXTURE",
                            "scope": "Strict JSON parsing only"})
        else:
            raise InvalidCertificate("mutation_accepted", "Malformed JSON was accepted")
    return results


def check_control_bindings(mapping: Any, *, required_ids: set[str] | None = None,
                           acceptance: bool = False,
                           evidence_validator: Callable[[dict, dict | None, dict | None], bool] | None = None) -> dict[str, Any]:
    """Check clause coverage without inventing theorem/replay references."""
    require(type(mapping) is dict and type(mapping.get("family_bindings")) is list
            and type(mapping.get("controls")) is list, "control_mapping", "Complete clause/control mapping required")
    families = mapping["family_bindings"]
    expected_required = required_ids or (
        {f"OPICA2_P{k:02d}" for k in range(1, 24)} | {f"OPICA2_S{k:02d}" for k in range(1, 18)})
    expected_all = expected_required | {"OPICA2_P24", "OPICA2_P25", "OPICA2_O_C2",
                                        "OPICA2_O_C3", "OPICA2_O_C4", "OPICA2_X01"}
    require(len(families) == 46 and {f.get("family_id") for f in families} == expected_all,
            "family_coverage", "Exactly 46 original family bindings are required")
    require({f["family_id"] for f in families if f.get("required_for_full_core") is True} == expected_required,
            "mandatory_families", "Required/optional family classification changed")
    controls = mapping["controls"]
    ids = [c.get("id") for c in controls]
    require(all(type(x) is str and x for x in ids) and len(set(ids)) == len(ids),
            "control_identities", "Control IDs must be nonempty and unique")
    clauses = []
    pending = []
    for family in families:
        require(family.get("all_normative_fields_required") is True, "normative_scope", "Normative fields were narrowed")
        require(type(family.get("components")) is list and family["components"],
                "component_coverage", "Family has no component clauses")
        for clause in family["components"]:
            cid = clause.get("clause_id")
            require(type(cid) is str and bool(cid), "clause_id", "Missing clause ID")
            clauses.append(cid)
            require(type(clause.get("acceptance")) is bool and clause.get("evidence_required") is True,
                    "clause_acceptance", "A Boolean clause disposition and evidence requirement are mandatory")
            links = clause.get("controls")
            require(type(links) is list and links, "clause_controls", "Every clause needs scoped controls")
            require(len({x.get("control_id") for x in links}) == len(links),
                    "duplicate_clause_control", "A clause cannot duplicate a control to inflate evidence")
            all_links_verified = True
            for link in links:
                require(link.get("control_id") in ids, "unknown_control", "Unknown linked control")
                require(type(link.get("expected_scientific_disposition")) is str
                        and bool(link["expected_scientific_disposition"])
                        and type(link.get("accepted_evidence_classes")) is list
                        and bool(link["accepted_evidence_classes"])
                        and all(type(x) is str and x for x in link["accepted_evidence_classes"])
                        and len(set(link["accepted_evidence_classes"])) == len(link["accepted_evidence_classes"]),
                        "control_scope", "Expected disposition and evidence classes are required")
                require(link.get("not_applicable_requires_review") is True
                        and link.get("evidence_required") is True,
                        "control_review", "Control evidence or applicability review was silently removed")
                evidence = link.get("actual_evidence")
                reference = link.get("resolved_theorem_or_replay_reference")
                require(type(evidence) is list, "control_evidence", "Control evidence must be an explicit list")
                if evidence or reference is not None:
                    require(evidence_validator is not None and evidence and reference is not None
                            and evidence_validator(family, clause, link) is True,
                            "unverified_control_evidence", "Actual control evidence needs independent verification")
                else:
                    all_links_verified = False
            if clause["acceptance"]:
                require(all_links_verified and evidence_validator is not None,
                        "unverified_clause", "A Boolean cannot accept a clause without all verified controls")
            elif family["required_for_full_core"]:
                pending.append(cid)
        if family.get("source_pinned_receipt") is not None:
            require(evidence_validator is not None and evidence_validator(family, None, None) is True,
                    "unverified_family", "A family receipt needs compiler revalidation")
        elif family["required_for_full_core"] and acceptance:
            pending.append(family["family_id"] + ":receipt")
    require(len(clauses) == 143 and len(set(clauses)) == 143,
            "clause_coverage", "Exactly 143 unique proposed component clauses are required")
    require(control_plan_fingerprint(families) == CONTROL_PLAN_SHA256,
            "control_plan_changed", "Clause scope/control requirements differ from the audited component split")
    if acceptance:
        require(not pending and evidence_validator is not None, "pending_clause_evidence",
                "Clause acceptance requires independent actual evidence; a mapping PASS is insufficient")
    return {"status": "PASS_VERIFIED_CONTROL_EVIDENCE" if acceptance else "PASS_CONTROL_MAPPING_ONLY", "families": 46, "required_families": 40,
            "clauses": 143, "pending_required_clauses": pending,
            "all_acceptance_false": all(c["acceptance"] is False for f in families for c in f["components"]),
            "RH": "OPEN", "Step4": "OPEN"}


def run_controls(*, registry_path: Path | None = None, mapping_path: Path | None = None) -> dict[str, Any]:
    fixture = load_strict_json(HERE / "fixtures" / "filtered_four_column.json", 65_536)
    finite = verify_filtered_baseline(fixture)
    minor = verify_native_jump_minor(load_strict_json(HERE / "fixtures" / "native_jump_minor.json", 65_536))
    current = finite_mutation_controls(fixture)
    inherited = []
    registry = None
    if registry_path is not None:
        registry = load_strict_json(registry_path)
        rows = registry.get("inherited_controls")
        require(type(rows) is list and len(rows) == 25
                and {r.get("id") for r in rows} == {f"OPICA2_F{k:02d}" for k in range(1, 26)},
                "inherited_controls", "All 25 original inherited controls must be retained")
        for row in rows:
            inherited.append({"id": row["id"], "scope": row["scope"], "inherited_authority": row["authority"],
                              "execution": "PRESERVED_NOT_REPLAYED",
                              "scientific_disposition": "Retain the exact inherited scoped result; no new theorem authority"})
    mapping_result = None
    if mapping_path is not None:
        mapping = load_strict_json(mapping_path)
        if "controls" not in mapping:
            require(registry is not None, "control_registry", "Clause mapping needs its actual control registry")
            combined = []
            for key in ("inherited_controls", "runtime_mutations", "typed_semantic_guards"):
                require(type(registry.get(key)) is list, "control_registry", "Missing control population: " + key)
                combined.extend(registry[key])
            mapping = {**mapping, "controls": combined}
        mapping_result = check_control_bindings(mapping)
    mutations = load_strict_json(HERE / "fixtures" / "mutations.json", 65_536)
    require({r["id"] for r in mutations["mutations"]} == {f"R2M{k:02d}" for k in range(1, 33)},
            "runtime_designs", "All 32 mutation designs must remain visible")
    return {"schema": "OPICA2_CONTROL_RUN_V1", "status": "PASS_EXECUTED_FINITE_CONTROLS_ONLY",
            "finite": finite, "minor_budget": minor, "executed_controls": current,
            "inherited_controls": inherited, "clause_mapping": mapping_result,
            "additional_mutation_designs": [
                {"id": r["id"], "scope": r["mutation"], "expected": r["expected"],
                 "execution": "NOT_CLAIMED_BY_THIS_SCOPED_RUN"}
                for r in mutations["mutations"]],
            "full_control_acceptance": False, "full_core_accepted": False,
            "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}


def main() -> int:
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry", type=Path, default=HERE / "CONTROL_REGISTRY.json")
    parser.add_argument("--mapping", type=Path, default=HERE / "PAPER_CROSSWALK.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = run_controls(registry_path=args.registry, mapping_path=args.mapping)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        result = failure_envelope("controls", exc)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result.get("status") == "PASS_EXECUTED_FINITE_CONTROLS_ONLY" else 1


if __name__ == "__main__":
    raise SystemExit(main())

