#!/usr/bin/env python3
"""Production artifact/tampering controls; every fixture is SYNTHETIC.

No fixture is a compiler receipt, native observation, external approval or
research result. Explicit checks run identically under python -O.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

from build_formal_receipt import AUDIT, audit_roots, full_expression_record
import materialize_step123_outputs as materializer
from prepare_field_review_package import FIELDS, produce
from symbolic_step123_artifacts import (
    SOURCE_ID, CUT_ROOTS, FIELD_IDS, SYMBOLIC_KIND, build_symbolic_index,
    finite_residual_rows, matched_control_inventory,
)
from test_formal_receipt import synthetic_type_expression
from test_step123_research_artifacts import audited_formal_fixture, cuts, panel
from compare_representations import compare
from countermodel_survival import audit, validate_survival_source_ids

IDENTITY = {"head": "a" * 40, "tree": "b" * 40}


def require(value, message):
    if not value:
        raise RuntimeError(message)


def rejects(action, label):
    try:
        action()
    except (ValueError, KeyError, TypeError):
        return
    raise RuntimeError("Failed to reject " + label)


def fixture():
    formal = audited_formal_fixture(IDENTITY)
    modules, kinds = audit_roots(AUDIT.read_text(encoding="utf-8-sig"))
    present = {r["declaration"] for key in ("declarations", "definitions") for r in formal[key]}
    for name in ["Zeta23.RHRC.consume" + f for f in FIELD_IDS] + list(CUT_ROOTS.values()):
        if name in present:
            continue
        kind = kinds[name]
        text = "SYNTHETIC_SCHEMA_CONTROL_NOT_A_LEAN_PROOF " + name
        row = {"declaration": name, "declaration_kind": kind, "module": modules[name],
               "source_tree": IDENTITY["tree"], "normalized_type": text,
               "normalized_type_sha256": hashlib.sha256(text.encode()).hexdigest(),
               **full_expression_record(synthetic_type_expression(name)),
               "structure_constructor_types": [], "axioms": [], "axiom_audit_pass": True,
               "authority": "PROVED" if kind == "THEOREM" else "DEFINED_DATA_NOT_A_THEOREM"}
        if kind == "THEOREM":
            row["theorem"] = name
        formal["declarations" if kind == "THEOREM" else "definitions"].append(row)
        present.add(name)
    formal["audited_root_count"] = len(present)
    contract = json.loads(FIELDS.read_text(encoding="utf-8"))
    dossier, _ = produce(formal, contract, **IDENTITY)
    return formal, dossier


def evaluated_panel():
    p, checker = panel()
    exact = lambda n: {"lower": [n, 1], "upper": [n, 1], "finite": True}
    for pair in p["pairs"]:
        pair.update(Q=1, L=exact(1), a=exact(1),
                    pole_normal_even_norm_sq=exact(2), pole_normal_odd_norm_sq=exact(3))
        for row in pair["rows"]:
            row.update(channel_names=["Arch", "PrimeForward"],
                       residual_gram_real=[[exact(1), exact(-1)], [exact(-1), exact(1)]],
                       residual_gram_imaginary="ZERO_BY_REAL_PROBE_AND_REAL_SYMMETRIC_NATIVE_CHANNELS",
                       channel_rayleigh={"Arch": exact(2), "PrimeForward": exact(-3)},
                       native_source={"status": "EVALUATED", "S": exact(2), "S0": exact(1), "correction": exact(-1)},
                       residual_norm_sq=exact(0), spectral_variance=exact(0),
                       synthetic_fixture_marker="NOT_AN_OBSERVATION")
    return p, checker


def test_symbolic_and_negative_controls():
    formal, dossier = fixture()
    before = deepcopy((formal, dossier))
    symbolic = build_symbolic_index(formal, dossier, **IDENTITY)
    require((formal, dossier) == before, "symbolic generation mutated compiler inputs")
    require([r["id"] for r in symbolic["compiler_statements"]] == list(FIELD_IDS), "missing/reordered field statements")
    require(len(symbolic["residual_rows"]) == 7 and len(symbolic["optional_paper_ports"]) == 5,
            "missing symbolic residual or PAPER port")
    # Dossier order cannot corrupt indexed cross-references.
    reverse = deepcopy(dossier)
    reverse["fields"].reverse()
    require(build_symbolic_index(formal, reverse, **IDENTITY) == symbolic, "field order changed proof references")
    mutations = [
        ("failed execution", lambda f: f.update(execution_status="FAILURE")),
        ("failed integrity", lambda f: f.update(integrity_status="FAIL")),
        ("wrong head", lambda f: f.update(head="c" * 40)),
        ("wrong tree", lambda f: f.update(source_tree="c" * 40)),
        ("stale normalized hash", lambda f: f["declarations"][0].update(normalized_type_sha256="0" * 64)),
        ("missing DAG", lambda f: f["declarations"][0].pop("full_type_expr")),
        ("stale DAG hash", lambda f: f["declarations"][0].update(full_type_expr_sha256="0" * 64)),
        ("project axiom", lambda f: f["declarations"][0].update(axioms=["Project.assumption"])),
        ("forged kind", lambda f: f["declarations"][0].update(declaration_kind="DEFINITION")),
        ("forged origin", lambda f: f["declarations"][0].update(module="Other.Module")),
    ]
    for label, mutate in mutations:
        altered = deepcopy(formal)
        mutate(altered)
        rejects(lambda: build_symbolic_index(altered, dossier, **IDENTITY), label)
    for label, mutate in (
        ("truncated dossier", lambda d: d["fields"].pop()),
        ("missing typed consumer", lambda d: d["fields"][0].update(candidate_declarations=[])),
        ("forged dossier approval", lambda d: d.update(authority="APPROVED")),
    ):
        altered = deepcopy(dossier)
        mutate(altered)
        rejects(lambda: build_symbolic_index(formal, altered, **IDENTITY), label)
    return 13


def test_finite_preservation():
    p, _ = evaluated_panel()
    before = deepcopy(p)
    rows = finite_residual_rows(p)
    require(p == before and len(rows) == 176, "finite input changed or rows lost")
    for copied, original in zip(rows, (r for pair in p["pairs"] for r in pair["rows"])):
        require(all(copied[k] == v for k, v in original.items()), "producer field dropped/rewritten")
        require(copied["row_kind"] == "FINITE_NATIVE_PARAMETER_EVALUATION", "wrong finite kind")
    for label, mutate in (
        ("missing imaginary part", lambda x: x["pairs"][0]["rows"][0].pop("residual_gram_imaginary")),
        ("missing normal correction", lambda x: x["pairs"][0]["rows"][0].pop("native_source")),
        ("missing normal geometry", lambda x: x["pairs"][0].pop("pole_normal_even_norm_sq")),
        ("conditional vector relabel", lambda x: x["pairs"][0]["rows"][0].update(is_hypothetical_zero_generated_detector=True)),
        ("synthetic origin relabel", lambda x: x["pairs"][0]["rows"][0].update(origin="SYNTHETIC_CONTROL")),
        ("modified source relabel", lambda x: x["pairs"][0]["rows"][0].update(source_id="MODIFIED_PRIME_SOURCE")),
    ):
        altered = deepcopy(p)
        mutate(altered)
        rejects(lambda: finite_residual_rows(altered), label)
    return 6


def test_control_receipt_bytes(directory):
    missing = matched_control_inventory({})
    require(len(missing) == 8 and all(r["receipt_evidence"] is None for r in missing),
            "missing controls falsely acquired evidence")
    path = directory / "synthetic-control-receipt.json"
    payload = {"claim_cap": "RH_OPEN", "source_id": "SYNTHETIC_MODIFIED_PRIME_CONTROL",
               "scientific_disposition": "SYNTHETIC_REPORTED_RESULT_NOT_REAL_EVIDENCE"}
    path.write_text(json.dumps(payload), encoding="utf-8")
    item = {"control_id": "MODIFIED_PRIME_K3", "receipt_path": str(path),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    received = matched_control_inventory({"control_receipt_inputs": [item]})
    require(received[0]["receipt_evidence"]["original_receipt"] == payload
            and received[0]["first_proved_incompatible_identity"] is None,
            "attached control evidence was rewritten or promoted")
    altered = deepcopy(item)
    altered["sha256"] = "0" * 64
    rejects(lambda: matched_control_inventory({"control_receipt_inputs": [altered]}), "stale control hash")
    rejects(lambda: matched_control_inventory({"control_receipt_inputs": [item, item]}), "duplicate control")
    altered = deepcopy(item)
    altered["control_id"] = "UNKNOWN_CONTROL"
    rejects(lambda: matched_control_inventory({"control_receipt_inputs": [altered]}), "unknown control")
    payload["claim_cap"] = "RH_PROVED"
    path.write_text(json.dumps(payload), encoding="utf-8")
    item["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    rejects(lambda: matched_control_inventory({"control_receipt_inputs": [item]}), "control RH promotion")
    return 4


def test_actual_materializer(directory):
    formal, _ = fixture()
    p, checker = evaluated_panel()
    inputs = {}
    def save(key, payload):
        path = directory / (key + ".json")
        path.write_text(json.dumps(payload), encoding="utf-8")
        inputs[key] = path
    save("formal", formal)
    save("panel", p)
    checker["panel_sha256"] = materializer.digest(inputs["panel"])
    save("checker", checker)
    comparison = compare(p, checker, panel_path=inputs["panel"], checker_path=inputs["checker"])
    save("comparison", comparison)
    cut_data = cuts()
    save("cuts", cut_data)
    d2 = {"status": "D2_OPEN", "receipt_status": "NOT_ISSUED", "claim_cap": "RH_OPEN"}
    save("d2", d2)
    save("survival", audit(comparison, cut_data, formal=formal, d2=d2))
    save("lineage", {"integrity_status": "PASS", "claim_cap": "RH_OPEN",
                     "scope": "SYNTHETIC_BYTE_CHECK_FIXTURE_NOT_REAL_SOURCE_EVIDENCE"})
    save("harvest", {"claim_cap": "RH_OPEN", "jobs": []})
    outdir = directory / "synthetic-bundle"
    with patch.object(materializer, "git", side_effect=lambda *args:
                      IDENTITY["tree"] if args[-1] == "HEAD^{tree}" else IDENTITY["head"]):
        receipt_path = materializer.materialize(inputs, outdir)
    load = lambda name: json.loads((outdir / name).read_text(encoding="utf-8"))
    receipt = json.loads(receipt_path.read_text())
    packet = load("STEP123_FORMAL_OUTPUT.json")
    require(all(r["resolution"] == "UNRESOLVED" and not r["scope"]["independently_reviewed"]
                for r in packet["quantities"]), "unapproved fields were promoted")
    require(packet["quantities"][0]["scope"]["bundle_compiler_inventory"] == formal,
            "literal formal artifact lacks exact compiler statements/hypotheses")
    schema = json.loads((materializer.INTEGRATION / "OUTPUT_CONTRACT.schema.json").read_text())
    require(set(packet) <= set(schema["properties"]), "frozen top-level formal schema changed")
    require(receipt["verified_fields"] == 0 and receipt["producer_complete"] is False,
            "partial release flags changed")
    require(load("FORMAL_BINDINGS.json") == formal, "compiler receipt changed")
    constraints = load("CONSTRAINTS.json")["symbolic_constraints"]
    require(len(constraints["compiler_statements"]) == 44 and len(constraints["branch_eligibility"]) == 4,
            "missing symbolic constraints/branch coverage")
    lineage = load("SOURCE_LINEAGE.json")["symbolic_source_lineage"]
    require(len(lineage["objects"]) == 13 and len(lineage["maps"]) == 8 and len(lineage["non_preservations"]) == 9,
            "source-lineage semantics missing")
    rows = [json.loads(line) for line in (outdir / "RESIDUAL_CHANNELS.jsonl").read_text().splitlines()]
    require(len(rows) == 183 and sum(r["row_kind"] == SYMBOLIC_KIND for r in rows) == 7,
            "symbolic rows replaced/masqueraded as finite observations")
    require(all("residual_gram_imaginary" in r and "channel_rayleigh" in r and "native_source" in r
                for r in rows if r["row_kind"] != SYMBOLIC_KIND), "finite complex/normal data truncated")
    require(len(load("COUNTERMODEL_SURVIVAL.json")["matched_controls"]) == 8,
            "mandatory control inventory missing")
    canonical = json.loads((materializer.INTEGRATION / "COUNTERMODEL_CONTRACTS.json").read_text())["source_id"]
    original_survival = load("COUNTERMODEL_SURVIVAL.json")
    require(canonical == SOURCE_ID, "frozen source ID disagrees with native symbolic source")
    require(validate_survival_source_ids(original_survival) == canonical,
            "valid original survival cuts rejected")
    require(all(row["source_id"] == canonical for row in original_survival["cuts"]),
            "materialized survival cuts do not join the source contract")
    for mutation in ("wrong_id", "missing", "duplicate", "wrong_source_identity"):
        altered = deepcopy(original_survival)
        if mutation == "wrong_id":
            altered["cuts"][0]["source_id"] = "MODIFIED_PRIME_SOURCE"
        elif mutation == "missing":
            altered["cuts"].pop()
        elif mutation == "duplicate":
            altered["cuts"][1]["id"] = altered["cuts"][0]["id"]
        else:
            altered["source_identity"] = {"source_id":"WRONG_ORIGIN"}
        if mutation != "wrong_source_identity":
            rejects(lambda a=altered: validate_survival_source_ids(a),
                    "invalid countermodel survival "+mutation)
        save("survival", altered)
        with patch.object(materializer, "git", side_effect=lambda *args:
                          IDENTITY["tree"] if args[-1] == "HEAD^{tree}" else IDENTITY["head"]):
            rejects(lambda: materializer.materialize(inputs, directory / ("reject-"+mutation)),
                    "materialized countermodel source "+mutation)
    save("survival", audit(comparison, cut_data, formal=formal, d2=d2))
    cuts_out = load("STEP4_CUTS.json")
    require(len(cuts_out["exact_compiler_sufficiency_statements"]) == 3
            and all(r["status"] == "OPEN" and r["newly_formalized"] is False for r in cuts_out["optional_paper_ports"]),
            "cut/PAPER ports missing or promoted")
    require(all(materializer.digest(outdir / name) == digest for name, digest in receipt["outputs"].items()),
            "materialization hashes stale after enrichment")


def main():
    mutations = test_symbolic_and_negative_controls() + test_finite_preservation()
    with tempfile.TemporaryDirectory(prefix="step123-symbolic-control-") as scratch:
        directory = Path(scratch)
        mutations += test_control_receipt_bytes(directory)
        test_actual_materializer(directory)
    print(json.dumps({"status": "PASS", "synthetic_only": True,
                      "adversarial_rejections": mutations, "finite_rows_preserved": 176,
                      "symbolic_rows": 7, "field_statements": 44,
                      "independent_semantic_approval": False, "RH": "OPEN"}))


if __name__ == "__main__":
    main()
