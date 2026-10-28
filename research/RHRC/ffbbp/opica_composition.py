"""Full-information assurance for OPICA applications, with exact expected sets.

Every replay callback is trusted evaluator code. Candidate data cannot select a
checker. Assurance results are not Lean theorem or terminal-claim authority.
"""
from __future__ import annotations
from research.RHRC.integration.opica_composition.canonical import (
    require, digest, digest_text, nonempty_text, closed_keys)

def verify_required_gates(expected: list[dict], received: list[dict], replay) -> tuple[str, ...]:
    require(type(expected) is list and bool(expected) and callable(replay),
            "nonempty independent required gate inventory and replay required")
    require(type(received) is list, "gate evidence list required")
    ids = [r["id"] for r in expected]
    got_ids = [r["id"] for r in received]
    require(len(set(ids)) == len(ids) and len(set(got_ids)) == len(got_ids), "duplicate gate")
    require(set(ids) == set(got_ids), "missing or unexpected gate")
    by_id = {r["id"]: r for r in received}
    for wanted in expected:
        actual = by_id[wanted["id"]]
        closed_keys(wanted, {"id", "scope", "identity", "checker"})
        closed_keys(actual, {"id", "scope", "identity", "checker", "status", "evidence"})
        require(wanted["scope"] in {"CURRENT_HOST", "FROZEN_BASELINE", "SELECTED_PROVIDER", "SYNTHETIC_FIXTURE"},
                "unadmitted evidence scope")
        nonempty_text(wanted["id"], "gate ID"); nonempty_text(wanted["checker"], "checker ID")
        require(type(wanted["identity"]) is dict, "explicit expected source/run identity required")
        for key in ("scope", "identity", "checker"):
            require(key in wanted and actual.get(key) == wanted[key], "gate identity differs: " + key)
        require(actual.get("status") == "PASS" and type(actual.get("evidence")) is list and bool(actual["evidence"]),
                "missing or unsuccessful required evidence")
        for ref in actual["evidence"]: digest_text(ref, "raw evidence digest")
        require(replay(wanted, actual) is True, "raw gate replay rejected")
    return tuple(sorted(ids))

def assess_composition_reduction(full_contracts: list[dict], reduction_fields: tuple[str, ...],
                                 decision_spec, *, hidden_fields=frozenset({"expected", "answer", "gold"})) -> dict:
    require(type(full_contracts) is list and type(reduction_fields) is tuple and callable(decision_spec),
            "finite full-information population and trusted decision function required")
    require(not set(reduction_fields) & set(hidden_fields), "qualification answer leakage")
    groups = {}
    for row in full_contracts:
        require(all(f in row for f in reduction_fields), "reduction field absent")
        key = digest({f: row[f] for f in reduction_fields}, domain="OPICA_REDUCTION_KEY_V1")
        groups.setdefault(key, []).append(row)
    collisions = []
    for key, group in sorted(groups.items()):
        decisions = [decision_spec(r) for r in group]
        if len({digest(x, domain="OPICA_DECISION_V1") for x in decisions}) > 1:
            collisions.append({"fiber": key, "members": [r["id"] for r in group],
                               "decisions": decisions})
    return {"status": "FALSIFIED_SUFFICIENCY" if collisions else "SURVIVED_FROZEN_POPULATION",
            "population": len(full_contracts), "retained_fields": list(reduction_fields),
            "colliding_fibers": collisions, "universal_authority": False}

def restore_full_contract(retrieved_id: str, frozen: dict[str, dict]) -> dict:
    require(retrieved_id in frozen, "retrieval outside frozen full-information inventory")
    from research.RHRC.integration.opica_composition.canonical import canonical_bytes, load_bytes
    return load_bytes(canonical_bytes(frozen[retrieved_id]))

def validate_residual_budget(required: dict, evidence: dict, replay) -> None:
    fields = {"source", "object", "norm", "domain", "normalization", "full_output",
              "tail", "quantifiers", "correction", "prime_powers"}
    require(set(required) >= fields, "incomplete expected residual contract")
    for field in fields:
        require(field in evidence and evidence[field] == required[field], "residual contract differs: " + field)
    require(evidence.get("scope") in {"FINITE_CERTIFICATE", "LEAN_THEOREM"}, "unqualified residual authority")
    require(evidence.get("exact_kernel") is not True or evidence.get("scope") == "LEAN_THEOREM",
            "numerical interval cannot certify exact resonance")
    require(callable(replay) and replay(required, evidence) is True, "budget replay rejected")

def build_falsifier_requirements(contract: dict) -> tuple[str, ...]:
    required = {"source_completeness", "same_witness", "same_aperture", "same_cutoff",
                "physical_metric", "signed_terms", "normalization", "quantifiers"}
    if contract.get("newborn"):
        required |= {"regular_and_resonant", "empty_predecessor", "tied_cutoffs"}
        require(contract.get("shell_unit") is True and contract.get("witness_nonzero") is True,
                "native newborn data missing")
        if contract.get("diagnostic_requires_unit_witness") and not contract.get("unit_witness_adapter"):
            required.add("ADAPTER_REQUIRED_UNIT_WITNESS")
    return tuple(sorted(required))

def verify_countermodel(target: dict, model: dict, replay) -> dict:
    require(set(model.get("preserved_premises", [])) == set(target["premises"]),
            "countermodel does not preserve every target premise")
    require(model.get("source_kind") == target["source_kind"], "source-incompatible countermodel")
    require(callable(replay) and replay(target, model) is True, "countermodel check failed")
    return {"status": "COUNTERMODEL_VERIFIED", "scope": target["source_kind"],
            "native_zeta_counterexample": target["source_kind"] == "ACTUAL_ZETA"}

def deduplicate_evidence_origins(rows: list[dict]) -> list[dict]:
    origins = {}
    for row in rows:
        for key in ("source", "invocation", "raw_sha256"):
            nonempty_text(row[key], key)
        identity = (row["source"], row["invocation"], row["raw_sha256"])
        origins.setdefault(identity, row)
    return [origins[k] for k in sorted(origins)]
