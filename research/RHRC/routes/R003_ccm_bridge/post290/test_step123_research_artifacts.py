#!/usr/bin/env python3
"""Adversarial tests of the Step123 non-proof research/output integration.

Fixtures below are SYNTHETIC TEST DATA; none is a numerical observation,
an actual zero, an independent semantic review or theorem authority.
Runs under normal and optimized Python with explicit exceptions.
"""
from __future__ import annotations

from copy import deepcopy

from build_step4_handoff import build
from compare_representations import compare
from countermodel_survival import audit
from evaluate_native_output import APERTURES, CARRIERS, CUTOFFS
from materialize_step123_outputs import output_packet
from prepare_field_review_package import produce as prepare_unapproved_44_field_dossier

SOURCE = {"source_raw_sha256": "e" * 64, "source_hash_mode": "RAW_BYTES"}


def raises(f, message):
    try:
        f()
    except (ValueError, TypeError, KeyError):
        return
    raise RuntimeError("Failed to reject " + message)


def panel():
    pairs = []
    receipts = []
    for ap in APERTURES:
        for k in CUTOFFS:
            rows = [{"carrier": c, "status": "EVALUATED_NATIVE_PROBE",
                     "is_hypothetical_zero_generated_detector": False,
                     "consistency": {"unit_norm": {"contains_zero": True}}}
                    for c in CARRIERS]
            pairs.append({"aperture": ap, "K": k, "status": "EVALUATED_NATIVE_PROBE",
                          "rows": rows})
            receipts.append({"aperture": ap, "K": k, "status": "FRESH_1024BIT_CONSISTENT"})
    return ({
        "schema": "post290.native-observation-panel.v1",
        "source_identity": SOURCE,
        "terminal_claim": "RH_OPEN",
        "pairs": pairs, "pair_count": 44, "row_count": 176
    }, {
        "schema": "post290.native-observation-checker.v1",
        "source_sha256": SOURCE["source_raw_sha256"],
        "terminal_claim": "RH_OPEN", "precision_bits": 1024,
        "verified_pairs": 44, "unresolved_pairs": 0,
        "receipts": receipts,
    })


def cuts():
    return {"claim_cap": "RH_OPEN",
            "cuts": [{"id": name, "status": "OPEN", "core_formal_sufficiency_module": "M24"}
                     for name in ("A-X", "B-Y", "C-Schur")]}


def tests():
    p, c = panel()
    good = compare(p, c)
    if not good["finite_panel_reproduced"] or good["consistent_pair_count"] != 44:
        raise RuntimeError("synthetic positive comparison baseline failed")
    malformed = deepcopy(p)
    malformed["pairs"][0]["rows"][0]["consistency"]["unit_norm"]["contains_zero"] = False
    if compare(malformed, c)["finite_panel_reproduced"]:
        raise RuntimeError("incorrectly accepted falsified Gram consistency")
    malformed = deepcopy(p)
    malformed["pairs"][0]["rows"][0]["is_hypothetical_zero_generated_detector"] = True
    if compare(malformed, c)["finite_panel_reproduced"]:
        raise RuntimeError("silently promoted finite probe into zero-generated detector")
    malformed = deepcopy(p)
    malformed["pairs"].append(deepcopy(malformed["pairs"][0]))
    raises(lambda: compare(malformed, c), "duplicate pair")
    malformed = deepcopy(c)
    malformed["source_sha256"] = "f" * 64
    raises(lambda: compare(p, malformed), "wrong source")
    malformed = deepcopy(c)
    malformed["receipts"].pop()
    missing = compare(p, malformed)
    if missing["finite_panel_reproduced"] or not missing["unresolved"]:
        raise RuntimeError("missing fresh-replay pair hidden")
    original = audit(good, cuts())
    if any(x["antecedent_proved"] for x in original["cuts"]):
        raise RuntimeError("OPEN mathematical cut was promoted")
    malformed = cuts()
    malformed["cuts"][0]["status"] = "PROVED"
    raises(lambda: audit(good, malformed), "fictitious closing cut")
    malformed = deepcopy(good)
    malformed["discrepancies"].append("FALSIFIED")
    raises(lambda: audit(malformed, cuts()), "numerical discrepancy")
    formal = {"claim_cap": "RH_OPEN", "producer_complete": False,
              "independent_assumption_review_pass": False,
              "head": "a" * 40, "source_tree": "b" * 40,
              "declarations": [], "definitions": []}
    from pathlib import Path
    import json
    root = Path(__file__).resolve().parents[5]
    contract = json.loads((root / "research/RHRC/integration/post290/"
                           "review_execution_2026-10-14/spec/OUTPUT_FIELD_CONTRACT.json").read_text())
    packet = output_packet(contract, formal, None, "a" * 40, "b" * 40)
    dossier, template = prepare_unapproved_44_field_dossier(
        formal, contract, "a" * 40, "b" * 40)
    if dossier["field_count"] != 44 or dossier["not_independently_reviewed"] != 44:
        raise RuntimeError("44-field candidate dossier improperly claims completion")
    if any(row["reviewed"] or row["evidence_verified"] for row in dossier["fields"]):
        raise RuntimeError("compiler candidates were mislabeled semantic proof review")
    if template["independent_assumption_review_pass"] or any(
            item["semantic_proof_review"] != "NOT_REVIEWED"
            for item in template["field_reviews"]):
        raise RuntimeError("unreviewed candidate template created review approval")
    if len(packet["quantities"]) != 44 or packet["scientific_disposition"] != "PARTIAL_OUTPUT_RH_OPEN":
        raise RuntimeError("unreviewed 44-field packet was accepted as complete")
    if any(q["theorem_receipt"] is not None for q in packet["quantities"]):
        raise RuntimeError("invented proof binding from an unreviewed field")
    raises(lambda: output_packet(contract, formal,
           {"field_reviews": []}, "a" * 40, "b" * 40), "fake independent semantic review")
    forged = deepcopy(template)
    forged["independent_assumption_review_pass"] = True
    forged["reviewer_is_source_author"] = False
    raises(lambda: output_packet(contract, formal, forged,
           "a" * 40, "b" * 40), "forged independent review on incomplete producer")
    doc = build(formal, good, original, None, None,
                {"head": "a" * 40, "tree": "b" * 40})
    if "RH OPEN" not in doc or "pending" in doc.lower() and "OPEN" not in doc:
        raise RuntimeError("handoff claim cap missing")
    return {"schema": "post290.research-artifact-mutations.v1",
            "status": "PASS", "authority": "SYNTHETIC_VALIDATOR_TEST_ONLY",
            "claim_cap": "RH_OPEN",
            "tested": ["44-pair identity", "numerical inconsistency", "same-source protection",
                       "no generated-detector impersonation", "missing replay", "OPEN cuts",
                       "44 unreviewed proof fields", "compiler-candidate dossier",
                       "unapproved template integrity", "independent review gate", "handoff cap"]}


if __name__ == "__main__":
    import json
    print(json.dumps(tests(), sort_keys=True))
