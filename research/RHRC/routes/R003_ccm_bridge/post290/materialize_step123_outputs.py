#!/usr/bin/env python3
"""Materialize the original Step123 research artifacts from source-bound evidence.

This produces a SYMBOLIC conditional output, not numerical zero coordinates.
A partial compiler receipt produces an explicitly PARTIAL output; the tool
never manufactures a 44-field proof review, D2 certificate or RH theorem.
Final release authority belongs solely to output_contract_check.py.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from build_step4_handoff import build as build_handoff
from output_contract_check import release_gaps, frozen_spec

REPO = Path(__file__).resolve().parents[5]
INTEGRATION = REPO / "research/RHRC/integration/post290"
FIELD_CONTRACT = REPO / "research/RHRC/integration/post290/review_execution_2026-10-14/spec/OUTPUT_FIELD_CONTRACT.json"
FIXED_SOURCE = "frozen-universal-sinc-product-s0-1/4096"

VIEW_MAP = (
    ("original_source", "ORIGINAL_SOURCE", "Zeta23.CCM.universalSincSource", "mass-one-source"),
    ("original_trial", "ORIGINAL_TRIAL", "Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial", "fixed-normalization"),
    ("finite_image", "FINITE_IMAGE", "Zeta23.CCM.nativeOriginalDetectorPaddedUnit", "native-unit"),
    ("selected_ground", "SELECTED_GROUND", "Zeta23.CCM.DetectorRetainedSchurState", "selected-unit"),
    ("exterior", "EXTERIOR", "Zeta23.CCM.OriginalNativeExteriorRecord", "same-original-phase"),
    ("native_field", "NATIVE_FIELD", "Zeta23.CCM.nativeOriginalPrimeField", "fixed-source"),
    ("forward_input", "FORWARD_INPUT", "Zeta23.CCM.nativeCompletedInputCausalL2", "actual-damping"),
)


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def write_jsonl(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        for row in rows:
            stream.write(json.dumps(row, sort_keys=True) + "\n")


def harvest_markdown(harvest):
    lines = ["# PR292 — exact-tree workflow harvest", "",
             "Claim cap: RH OPEN. A successful job must be reviewed for its actual research disposition.", ""]
    jobs = harvest.get("jobs", [])
    for job in jobs:
        lines.append("- " + str(job.get("workflow", "UNKNOWN")) + " / " +
                     str(job.get("name", job.get("job", "UNKNOWN"))) +
                     ": status=" + str(job.get("status", "UNKNOWN")) +
                     ", conclusion=" + str(job.get("conclusion", "UNKNOWN")) +
                     ", classification=" + str(job.get("classification", "NOT_REVIEWED")) +
                     ", output_reviewed=" + str(job.get("output_reviewed", False)) +
                     ", scientific_acceptance=" + str(job.get("scientific_acceptance", False)))
    if not jobs:
        lines.append("No reviewable jobs supplied. Acceptance OPEN.")
    return "\n".join(lines) + "\n"


def source_bindings(formal, head, tree):
    if formal.get("head") != head or formal.get("source_tree") != tree:
        raise ValueError("compiler receipt is for another source head or tree")
    if formal.get("claim_cap") != "RH_OPEN":
        raise ValueError("RH firewall failed")
    bindings = {}
    for row in formal.get("declarations", []) + formal.get("definitions", []):
        name = row.get("declaration", row.get("theorem"))
        if not isinstance(name, str) or not name or name in bindings:
            raise ValueError("duplicate/invalid compiler root")
        if row.get("source_tree") != tree:
            raise ValueError("stale source-tree compiler root: " + name)
        if row.get("axiom_audit_pass") is not True:
            raise ValueError("unverified compiler axiom root: " + name)
        if set(row.get("axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("admitted proof escape: " + name)
        bindings[name] = row
    return bindings


def semantic_field_map(semantic, formal, head, tree):
    if semantic is None:
        return {}
    if not (formal.get("producer_complete") is True
            and formal.get("independent_assumption_review_pass") is True):
        raise ValueError("review cannot promote a partial compiler receipt")
    if semantic.get("reviewed_head") != head or semantic.get("reviewed_tree") != tree:
        raise ValueError("independent review was done at a different exact tree")
    if semantic.get("reviewer_is_source_author") is not False:
        raise ValueError("not an independent semantic review")
    if semantic.get("independent_assumption_review_pass") is not True:
        raise ValueError("independent assumption review not passed")
    values = semantic.get("field_reviews", [])
    if len(values) != 44 or len({r.get("id") for r in values}) != 44:
        raise ValueError("all 44 independently reviewed fields required")
    return {r["id"]: r for r in values}


def output_packet(contract, formal, review, head, tree):
    groups = contract.get("field_groups", [])
    if len(groups) != 44 or len({r.get("id") for r in groups}) != 44:
        raise ValueError("original 44-field contract is missing or modified")
    bindings = source_bindings(formal, head, tree)
    reviews = semantic_field_map(review, formal, head, tree)
    if reviews and set(reviews) != {r["id"] for r in groups}:
        raise ValueError("field review does not match the original frozen contract")
    quantities = []
    verified = 0
    for field in groups:
        item = reviews.get(field["id"], {})
        declaration = item.get("declaration_ref")
        proved = bool(declaration in bindings
                      and item.get("semantic_proof_review") == "PASS"
                      and item.get("evidence_verified") is True
                      and isinstance(item.get("reason"), str) and item.get("reason"))
        if proved:
            verified += 1
        quantities.append({
            "id": field["id"],
            "source_id": FIXED_SOURCE,
            "carrier_id": "original-detector/same-retained-state",
            "resolution": "SYMBOLIC_FORMAL" if proved else "UNRESOLVED",
            "authority": "PROVED" if proved and bindings[declaration].get("declaration_kind") == "THEOREM"
                else "DERIVED" if proved else "OPEN",
            "definition_ref": declaration if proved else field["producer"],
            "scope": {
                "field": field["field"], "requirement": field["exact_content"],
                "kind": field["kind"], "task": field["task"],
                "caller_can_supply_unproved_bridge": False,
                "hypothetical_offline_zero_is_symbolic": True,
                "independently_reviewed": proved
            },
            "theorem_receipt": declaration if proved else None,
            "reason": None if proved else "Required field not separately signed off by exact-head independent semantic review.",
        })
    views = [{"id": name, "source_id": FIXED_SOURCE, "role": role,
              "carrier_id": "original-detector/same-retained-state",
              "definition_ref": definition, "normalization_ref": norm}
             for name, role, definition, norm in VIEW_MAP]
    cuts = [{"id": cut, "status": "OPEN", "sufficiency_ref": ref,
             "source_id": FIXED_SOURCE, "scope": {"antecedent": "OPEN",
               "conditional_implication": "requires exact-head compiler proof receipt"}}
            for cut, ref in (("A-X", "Zeta23.ExceptionalZero.riemannHypothesis_of_step4_AX"),
                             ("B-Y", "Zeta23.ExceptionalZero.riemannHypothesis_of_step4_BY"),
                             ("C-Schur", "Zeta23.ExceptionalZero.riemannHypothesis_of_originalDetectorSchurSubexponential"))]
    return {
        "schema_version": "RH_STEP123_OUTPUT_1.0",
        "source_tree": tree,
        "execution_status": "SUCCESS",
        "integrity_status": "PASS" if verified == 44 else "NOT_CHECKED",
        "scientific_disposition": "CORE_OUTPUT_COMPLETE_RH_OPEN" if verified == 44 else "PARTIAL_OUTPUT_RH_OPEN",
        "claim_cap": "RH_OPEN",
        "origin": "FORMAL_CONDITIONAL",
        "views": views,
        "quantities": quantities,
        "relations": [
            {"id": "exact-source-to-original-phase", "from_view": "original_source",
             "to_view": "original_trial", "kind": "PAPER_ADAPTER",
             "authority": "OPEN", "scope": {"not_an_RH_proof": True},
             "evidence_ref": "Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial"},
            {"id": "one-retained-detector", "from_view": "finite_image",
             "to_view": "selected_ground", "kind": "EXACT_LINEAR_MAP",
             "authority": "OPEN", "scope": {"selected_ground_is_not_original_detector": True},
             "evidence_ref": "Zeta23.CCM.DetectorRetainedSchurState"}
        ],
        "cuts": cuts,
        "workflow_harvest_ref": "NOT_SUPPLIED",
        "d2_receipt_ref": None
    }


def materialize(inputs, outdir, semantic=None):
    head, tree = git("rev-parse", "HEAD"), git("rev-parse", "HEAD^{tree}")
    formal = load(inputs["formal"])
    fields = load(FIELD_CONTRACT)
    packet = output_packet(fields, formal, semantic, head, tree)
    lineage, panel, checker = (load(inputs[k]) for k in ("lineage", "panel", "checker"))
    comparison, survival, d2, harvest = (load(inputs[k]) for k in
                                         ("comparison", "survival", "d2", "harvest"))
    cuts = load(inputs["cuts"])
    if any(x.get("claim_cap", x.get("terminal_claim", "RH_OPEN")) != "RH_OPEN"
           for x in (lineage, comparison, survival, d2, harvest, cuts)):
        raise ValueError("source/observation claim firewall failed")
    if lineage.get("integrity_status") != "PASS":
        raise ValueError("pinned source lineage has not passed its independent byte check")
    if panel.get("source_identity") != comparison.get("source_identity"):
        raise ValueError("comparison not bound to supplied panel")
    if checker.get("panel_sha256") != digest(inputs["panel"]):
        raise ValueError("1024-bit native checker belongs to a different panel")
    if comparison.get("checker_sha256") != digest(inputs["checker"]):
        raise ValueError("representation comparison belongs to a different checker")
    if any(c.get("status") != "OPEN" for c in cuts.get("cuts", [])):
        raise ValueError("the original three conditional cuts were promoted")
    packet["workflow_harvest_ref"] = str(inputs["harvest"])
    packet["d2_receipt_ref"] = str(inputs["d2"])
    write(outdir / "STEP123_FORMAL_OUTPUT.json", packet)
    write(outdir / "SOURCE_LINEAGE.json", lineage)
    write(outdir / "NATIVE_OBSERVATIONS.json", panel)
    observation_rows = [
        dict(row,
             aperture=pair.get("aperture"),
             K=pair.get("K"),
             source_id=FIXED_SOURCE,
             source_identity=panel["source_identity"],
             origin="NATIVE_PARAMETER_EVALUATION",
             resolution="CERTIFIED_INTERVAL" if row.get("status") == "EVALUATED_NATIVE_PROBE" else "UNRESOLVED",
             mathematical_scope="FINITE_FIXED_PROBE_NOT_HYPOTHETICAL_ZERO_DETECTOR")
        for pair in panel.get("pairs", []) for row in pair.get("rows", [])
    ]
    write_jsonl(outdir / "NATIVE_OBSERVATIONS.jsonl", observation_rows)
    residuals = [{"aperture": p.get("aperture"), "K": p.get("K"),
                  "rows": [{"carrier": row.get("carrier"), "status": row.get("status"),
                            "residual_norm_sq": row.get("residual_norm_sq"),
                            "spectral_variance": row.get("spectral_variance"),
                            "channel_names": row.get("channel_names"),
                            "residual_gram_real": row.get("residual_gram_real"),
                            "consistency": row.get("consistency")}
                           for row in p.get("rows", [])]}
                 for p in panel.get("pairs", [])]
    write(outdir / "RESIDUAL_CHANNELS.json", {
        "schema": "post290.source-bound-residual-channels.v1",
        "claim_cap": "RH_OPEN", "source_identity": panel["source_identity"],
        "scope": "finite native probes only; not original zero-generated detector",
        "pairs": residuals})
    write_jsonl(outdir / "RESIDUAL_CHANNELS.jsonl", [
        dict(row, aperture=pair.get("aperture"), K=pair.get("K"),
             source_id=FIXED_SOURCE,
             origin="NATIVE_PARAMETER_EVALUATION",
             mathematical_scope="FINITE_POINT_GRAM_ONLY")
        for pair in residuals for row in pair.get("rows", [])
    ])
    write(outdir / "CONSTRAINTS.json", comparison)
    write(outdir / "COUNTERMODEL_SURVIVAL.json", survival)
    write(outdir / "D2_CONTINUUM_RECEIPT.json", d2)
    write(outdir / "STEP4_CUTS.json", cuts)
    write(outdir / "WORKFLOW_HARVEST.json", harvest)
    (outdir / "WORKFLOW_HARVEST.md").write_text(
        harvest_markdown(harvest), encoding="utf-8")
    write(outdir / "FORMAL_BINDINGS.json", formal)
    write(outdir / "ASSUMPTION_AUDIT.json", {
        "schema": "post290.assumption-audit-output.v1",
        "claim_cap": "RH_OPEN",
        "source_head": head, "source_tree": tree,
        "producer_complete": formal.get("producer_complete") is True,
        "independent_assumption_review_pass": formal.get("independent_assumption_review_pass") is True,
        "fields_independently_reviewed": sum(q["scope"]["independently_reviewed"]
                                              for q in packet["quantities"]),
        "three_step4_antecedents": {"A-X": "OPEN", "B-Y": "OPEN", "C-Schur": "OPEN"},
        "not_a_new_proof": True,
    })
    doc = build_handoff(formal, comparison, survival, d2, harvest,
                        {"head": head, "tree": tree})
    (outdir / "STEP4_RESEARCH_HANDOFF.md").write_text(doc, encoding="utf-8")
    required = [p.name for p in outdir.iterdir() if p.is_file()]
    write(outdir / "MATERIALIZATION_RECEIPT.json", {
        "schema": "post290.materialization-receipt.v1", "claim_cap": "RH_OPEN",
        "head": head, "tree": tree,
        "producer_complete": formal.get("producer_complete") is True,
        "required_fields": len(packet["quantities"]),
        "verified_fields": sum(q["scope"]["independently_reviewed"]
                               for q in packet["quantities"]),
        "outputs": {name: digest(outdir / name) for name in sorted(required)},
        "scientific_disposition": "PARTIAL_OUTPUT_RH_OPEN"
            if formal.get("producer_complete") is not True else "EXTERNAL_RELEASE_REVIEW_REQUIRED",
        "release_authority": "NONE; output_contract_check.py must pass independently",
    })
    return outdir / "MATERIALIZATION_RECEIPT.json"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ("formal", "lineage", "panel", "checker", "comparison", "survival",
                "d2", "harvest", "cuts"):
        p.add_argument("--" + key, required=True, type=Path)
    p.add_argument("--semantic-review", type=Path)
    p.add_argument("--out-dir", required=True, type=Path)
    a = p.parse_args()
    items = {key: getattr(a, key) for key in
             ("formal", "lineage", "panel", "checker", "comparison", "survival",
              "d2", "harvest", "cuts")}
    semantic = load(a.semantic_review) if a.semantic_review else None
    out = materialize(items, a.out_dir, semantic)
    print(json.dumps({"receipt": str(out), "claim_cap": "RH_OPEN",
                      "authority": "NONE_CREATED_BY_MATERIALIZATION"}))


if __name__ == "__main__":
    main()
