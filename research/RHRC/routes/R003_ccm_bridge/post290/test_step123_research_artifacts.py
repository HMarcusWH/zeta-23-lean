#!/usr/bin/env python3
"""Adversarial tests of the Step123 non-proof research/output integration.

Fixtures below are SYNTHETIC TEST DATA; none is a numerical observation,
an actual zero, an independent semantic review or theorem authority.
Runs under normal and optimized Python with explicit exceptions.
"""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path

from build_formal_receipt import AUDIT, audit_roots, full_expression_record
from test_formal_receipt import synthetic_type_expression
from build_step4_handoff import COMPARISON_ROOTS, INTEGRATED_ROOTS, build
from compare_representations import compare, EXPECTED_SOURCE_PATHS, SOURCE_HASH_MODE
from countermodel_survival import audit
from evaluate_native_output import APERTURES, CARRIERS, CUTOFFS
from materialize_step123_outputs import output_packet
from prepare_field_review_package import produce as prepare_unapproved_44_field_dossier

SOURCE = {"commit": "a" * 40, "tree": "b" * 40, "working_tree_dirty": False,
          "source_raw_sha256": {path: "e" * 64 for path in EXPECTED_SOURCE_PATHS},
          "source_sha256": {path: "f" * 64 for path in EXPECTED_SOURCE_PATHS},
          "source_hash_mode": SOURCE_HASH_MODE}
STRUCTURE_CONTROL = "Zeta23.CCM.DetectorRetainedSchurState"


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
        "source_sha256": SOURCE["source_sha256"],
        "source_hash_mode": SOURCE_HASH_MODE,
        "checker_source_raw_sha256": {path: "d" * 64 for path in EXPECTED_SOURCE_PATHS},
        "terminal_claim": "RH_OPEN", "precision_bits": 1024,
        "verified_pairs": 44, "unresolved_pairs": 0,
        "receipts": receipts,
    })


def native_source_identity_controls(p, c):
    """Reject malformed provenance while retaining distinct raw/normalized maps."""
    original_panel, original_checker = deepcopy(p), deepcopy(c)
    if compare(p, c)["source_identity"] != SOURCE:
        raise RuntimeError("native comparison rewrote the producer's source identity")
    if (p != original_panel or c != original_checker
            or p["source_identity"]["source_raw_sha256"] == c["checker_source_raw_sha256"]
            or p["source_identity"]["source_sha256"] != c["source_sha256"]):
        raise RuntimeError("distinct cross-platform raw evidence was not preserved")
    path = sorted(EXPECTED_SOURCE_PATHS)[0]
    checked = []

    def reject(label, mutate):
        changed = deepcopy(p)
        mutate(changed["source_identity"])
        raises(lambda: compare(changed, c), label)
        checked.append(label)

    reject("legacy scalar source hash", lambda s: s.update(source_raw_sha256="e" * 64))
    reject("empty raw source map", lambda s: s.update(source_raw_sha256={}))
    reject("empty normalized source map", lambda s: s.update(source_sha256={}))
    reject("missing normalized source map", lambda s: s.pop("source_sha256"))
    reject("missing raw source path", lambda s: s["source_raw_sha256"].pop(path))
    reject("missing normalized source path", lambda s: s["source_sha256"].pop(path))

    def missing_both(s):
        s["source_raw_sha256"].pop(path)
        s["source_sha256"].pop(path)
    reject("same-key truncated source maps", missing_both)

    def extra_both(s):
        s["source_raw_sha256"]["unknown/source.lean"] = "e" * 64
        s["source_sha256"]["unknown/source.lean"] = "f" * 64
    reject("same-key unexpected source path", extra_both)
    for field in ("source_raw_sha256", "source_sha256"):
        for label, value in (("uppercase", "E" * 64), ("short", "e" * 63),
                             ("nonhex", "g" * 64), ("nonstring", False)):
            reject(field + " " + label + " hash", lambda s, f=field, v=value:
                   s[f].__setitem__(path, v))
    for key in ("commit", "tree"):
        reject("missing " + key, lambda s, k=key: s.pop(k))
        for label, value in (("short", "a" * 39), ("nonhex", "g" * 40),
                             ("nonstring", False)):
            reject(key + " " + label, lambda s, k=key, v=value: s.__setitem__(k, v))
    for label, value in (("dirty", True), ("numeric dirty flag", 0),
                         ("string dirty flag", "false")):
        reject(label, lambda s, v=value: s.update(working_tree_dirty=v))
    reject("missing clean source flag", lambda s: s.pop("working_tree_dirty"))
    reject("wrong source normalization mode", lambda s: s.update(source_hash_mode="RAW_BYTES"))
    changed = deepcopy(c)
    changed["source_sha256"] = deepcopy(SOURCE["source_raw_sha256"])
    raises(lambda: compare(p, changed), "checker raw map impersonates normalized map")
    checked.append("checker raw map impersonates normalized map")
    changed = deepcopy(c)
    changed["source_hash_mode"] = "RAW_BYTES"
    raises(lambda: compare(p, changed), "wrong checker source normalization mode")
    checked.append("wrong checker source normalization mode")
    checker_raw_mutations = [
        ("missing checker raw map", lambda x: x.pop("checker_source_raw_sha256")),
        ("empty checker raw map", lambda x: x.update(checker_source_raw_sha256={})),
        ("checker raw scalar", lambda x: x.update(checker_source_raw_sha256="d" * 64)),
        ("missing checker raw path", lambda x: x["checker_source_raw_sha256"].pop(path)),
        ("unexpected checker raw path", lambda x:
            x["checker_source_raw_sha256"].__setitem__("unknown/source.lean", "d" * 64)),
        ("malformed checker raw hash", lambda x:
            x["checker_source_raw_sha256"].__setitem__(path, "D" * 64)),
    ]
    for label, mutate in checker_raw_mutations:
        changed = deepcopy(c)
        mutate(changed)
        raises(lambda: compare(p, changed), label)
        checked.append(label)
    return checked


def cuts():
    return {"claim_cap": "RH_OPEN",
            "cuts": [{"id": name, "status": "OPEN", "core_formal_sufficiency_module": "M24"}
                     for name in ("A-X", "B-Y", "C-Schur")]}


def audited_formal_fixture(identity):
    """Fabricated compiler-schema control; never actual compiler evidence."""
    modules, kinds = audit_roots(AUDIT.read_text(encoding="utf-8-sig"))
    declarations, definitions = [], []
    for name in sorted(INTEGRATED_ROOTS | COMPARISON_ROOTS | {STRUCTURE_CONTROL}):
        text = "SYNTHETIC_VALIDATOR_TYPE_NOT_A_PROOF " + name
        kind = kinds[name]
        row = {"declaration": name, "declaration_kind": kind, "module": modules[name],
               "source_tree": identity["tree"], "normalized_type": text,
               "normalized_type_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
               **full_expression_record(synthetic_type_expression(name)),
               "structure_constructor_types": [],
               "axioms": ["propext", "Classical.choice", "Quot.sound"],
               "axiom_audit_pass": True,
               "authority": "PROVED" if kind == "THEOREM" else "DEFINED_DATA_NOT_A_THEOREM"}
        if kind == "INDUCTIVE":
            row["structure_constructor_types"] = [{
                "constructor": name + ".mk",
                **full_expression_record(synthetic_type_expression(name + ".mk"))}]
        if kind == "THEOREM":
            row["theorem"] = name
            declarations.append(row)
        else:
            definitions.append(row)
    root = Path(__file__).resolve().parents[5]
    declared = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    packages = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    context = dict(identity)
    context.update(declared_toolchain=declared,
                   actual_compiler_version="Lean (version " + declared.rsplit(":v", 1)[-1] +
                       ", SYNTHETIC VALIDATOR CONTROL)",
                   mathlib_revision=next(package["rev"] for package in packages
                                         if package["name"] == "mathlib"),
                   tracked_lean_toolchain_manifest_clean=True,
                   dependencies=[{"package": package["name"], "revision": package["rev"],
                                  "lean_source_clean": True} for package in packages])
    return {"schema_version": "RH_POST290_COMPONENT_COMPILER_RECEIPT_1.0",
            "claim_cap": "RH_OPEN", "producer_complete": False,
            "independent_assumption_review_pass": False,
            "execution_status": "SUCCESS", "integrity_status": "PASS",
            "head": identity["head"], "source_tree": identity["tree"],
            "compiler_context": context, "compiler_log_sha256": "0" * 64,
            "audited_root_count": len(declarations) + len(definitions),
            "declarations": declarations, "definitions": definitions}


def handoff_receipt_controls(comparison, survival, sparse, identity, contract):
    """Exercise the real handoff builder against failed and forged receipts."""
    positive = audited_formal_fixture(identity)
    doc = build(positive, comparison, survival, None, None, identity)
    for expected in (
            "The audited receipt resolves the same-packet interfaces",
            "PROVED ingredients", "Re W(f,f)<=-4 exp(beta L)",
            "16 kappa X_L>=4 exp(beta L)+Re A_f",
            "H1(f)^2<=1+M1 B1", "OPEN C-Schur upper law",
            "C exp(epsilon L)<exp(beta L)/2<S<=C exp(epsilon L)",
            "A-X, B-Y and C-Schur remain OPEN", "Complete source/packet signoff: NO"):
        if expected not in doc:
            raise RuntimeError("handoff omitted audited comparison/control: " + expected)
    partial = build(sparse, comparison, survival, None, None, identity)
    if ("UNVERIFIED SPARSE COMPONENT INPUT" not in partial
            or "The audited receipt resolves" in partial
            or "PROVED ingredients" in partial or "PROVED C-Schur lower ingredient" in partial):
        raise RuntimeError("sparse component fixture acquired audited proof authority")

    # A valid subset may resolve the five integrated interfaces, but cannot
    # certify worked mathematical ingredients whose roots were not audited.
    thin = deepcopy(positive)
    for key in ("declarations", "definitions"):
        thin[key] = [row for row in thin[key] if row["declaration"] in INTEGRATED_ROOTS]
    thin["audited_root_count"] = len(thin["declarations"]) + len(thin["definitions"])
    thin_doc = build(thin, comparison, survival, None, None, identity)
    if ("The audited receipt resolves" not in thin_doc
            or "PROVED ingredients" in thin_doc or "Conditional C-Schur lower target" not in thin_doc):
        raise RuntimeError("unaudited worked-comparison ingredients were promoted")

    checked = []

    def reject(label, mutate):
        changed = deepcopy(positive)
        mutate(changed)
        raises(lambda: build(changed, comparison, survival, None, None, identity), label)
        checked.append(label)

    reject("failed compiler named-root receipt", lambda f: f.update(execution_status="FAILURE"))
    reject("failed receipt integrity", lambda f: f.update(integrity_status="FAIL"))
    reject("stale compiler head", lambda f: f.update(head="c" * 40))
    reject("stale compiler tree", lambda f: f.update(source_tree="c" * 40))
    reject("missing compiler context", lambda f: f.pop("compiler_context"))
    reject("stale compiler context head", lambda f: f["compiler_context"].update(head="c" * 40))
    reject("stale compiler context tree", lambda f: f["compiler_context"].update(tree="c" * 40))
    reject("wrong declared Lean toolchain", lambda f:
           f["compiler_context"].update(declared_toolchain="leanprover/lean4:v0.0.0"))
    reject("wrong actual Lean compiler", lambda f:
           f["compiler_context"].update(actual_compiler_version="Lean (version 0.0.0)"))
    reject("wrong Mathlib revision", lambda f:
           f["compiler_context"].update(mathlib_revision="f" * 40))
    reject("unclean tracked compiler sources", lambda f:
           f["compiler_context"].update(tracked_lean_toolchain_manifest_clean=False))
    reject("missing pinned dependency context", lambda f:
           f["compiler_context"].pop("dependencies"))
    reject("wrong pinned dependency revision", lambda f:
           f["compiler_context"]["dependencies"][0].update(revision="f" * 40))
    reject("unclean pinned dependency", lambda f:
           f["compiler_context"]["dependencies"][0].update(lean_source_clean=False))
    reject("duplicate pinned dependency", lambda f:
           f["compiler_context"]["dependencies"].__setitem__(
               1, deepcopy(f["compiler_context"]["dependencies"][0])))
    reject("missing compiler log hash", lambda f: f.pop("compiler_log_sha256"))
    reject("wrong audited root count", lambda f: f.update(audited_root_count=0))
    reject("empty claimed compiler audit", lambda f:
           f.update(declarations=[], definitions=[], audited_root_count=0))
    reject("forged normalized type hash", lambda f:
           f["declarations"][0].update(normalized_type_sha256="f" * 64))
    reject("changed normalized type", lambda f:
           f["declarations"][0].update(normalized_type="FORGED_TYPE"))
    reject("missing full type expression", lambda f: f["declarations"][0].pop("full_type_expr"))
    reject("changed full type expression", lambda f:
           f["declarations"][0].update(full_type_expr=synthetic_type_expression("Forged.ValidatorControl")))
    reject("wrong full type expression format", lambda f:
           f["declarations"][0].update(full_type_expr_format="PRETTY_TYPE_NOT_FULL_EXPR"))
    reject("missing constructor inventory", lambda f:
           f["declarations"][0].pop("structure_constructor_types"))

    def structure_row(f):
        return next(row for row in f["definitions"] if row["declaration"] == STRUCTURE_CONTROL)

    reject("missing inductive constructor types", lambda f:
           structure_row(f).update(structure_constructor_types=[]))
    reject("changed constructor expression", lambda f:
           structure_row(f)["structure_constructor_types"][0].update(full_type_expr=synthetic_type_expression("Forged.ConstructorValidatorControl")))
    reject("duplicate constructor expression", lambda f:
           structure_row(f)["structure_constructor_types"].append(
               deepcopy(structure_row(f)["structure_constructor_types"][0])))
    reject("constructor inventory on theorem", lambda f:
           f["declarations"][0].update(
               structure_constructor_types=deepcopy(structure_row(f)["structure_constructor_types"])))
    reject("wrong compiler origin module", lambda f:
           f["declarations"][0].update(module="Zeta23.Forged"))
    reject("wrong compiler declaration kind", lambda f:
           f["declarations"][0].update(declaration_kind="DEFINITION"))
    reject("stale per-root tree", lambda f:
           f["declarations"][0].update(source_tree="c" * 40))
    reject("failed per-root axiom audit", lambda f:
           f["declarations"][0].update(axiom_audit_pass=False))
    reject("unadmitted root axiom", lambda f:
           f["declarations"][0].update(axioms=["sorryAx"]))
    reject("missing root axioms", lambda f: f["declarations"][0].pop("axioms"))
    reject("theorem authority on wrong root", lambda f:
           f["declarations"][0].update(authority="DEFINED_DATA_NOT_A_THEOREM"))
    reject("mismatched theorem alias", lambda f:
           f["declarations"][0].update(theorem="Zeta23.Forged"))

    def forged_root(f):
        f["declarations"][0].update(declaration="Zeta23.Forged", theorem="Zeta23.Forged")
    reject("unregistered forged compiler root", forged_root)

    def duplicate_root(f):
        f["declarations"].append(deepcopy(f["declarations"][0]))
        f["audited_root_count"] += 1
    reject("duplicated audited compiler root", duplicate_root)

    # Reproduce the original exploit exactly: names alone plus explicit
    # failed execution/integrity must not emit an integration assertion.
    failed_names = deepcopy(sparse)
    failed_names.update(execution_status="FAILURE", integrity_status="FAIL",
                        declarations=[{"declaration": name} for name in INTEGRATED_ROOTS])
    raises(lambda: build(failed_names, comparison, survival, None, None, identity),
           "failed unaudited five-name integration exploit")
    names_only = deepcopy(sparse)
    names_only["declarations"] = [{"declaration": name} for name in INTEGRATED_ROOTS]
    raises(lambda: build(names_only, comparison, survival, None, None, identity),
           "unaudited names-only integration exploit")
    explicit_failed_sparse = deepcopy(sparse)
    explicit_failed_sparse["execution_status"] = "FAILURE"
    raises(lambda: build(explicit_failed_sparse, comparison, survival, None, None, identity),
           "explicit failed sparse receipt")

    # The real unapproved dossier must preserve the literal type and structure
    # constructor expressions, rather than substitute its pretty-print view.
    dossier, template = prepare_unapproved_44_field_dossier(
        positive, contract, identity["head"], identity["tree"])
    n17 = next(row for row in dossier["fields"] if row["id"] == "N17")
    candidate = next(row for row in n17["candidate_declarations"]
                     if row["name"] == STRUCTURE_CONTROL)
    expected_structure = structure_row(positive)
    for key in ("normalized_type", "normalized_type_sha256", "full_type_expr",
                "full_type_expr_sha256", "full_type_expr_format", "structure_constructor_types"):
        if candidate.get(key) != expected_structure[key]:
            raise RuntimeError("dossier omitted or altered literal compiler type field: " + key)
    if template["independent_assumption_review_pass"] is not False or any(
            row["evidence_verified"] or row["reviewed"] for row in dossier["fields"]):
        raise RuntimeError("literal type visibility incorrectly promoted independent approval")
    malformed = deepcopy(positive)
    structure_row(malformed).pop("full_type_expr")
    raises(lambda: prepare_unapproved_44_field_dossier(
        malformed, contract, identity["head"], identity["tree"]), "dossier missing literal type")
    malformed = deepcopy(positive)
    structure_row(malformed)["structure_constructor_types"][0]["full_type_expr"] = "FORGED_CTOR_EXPR"
    raises(lambda: prepare_unapproved_44_field_dossier(
        malformed, contract, identity["head"], identity["tree"]), "dossier changed constructor type")
    checked.extend(["dossier missing literal type", "dossier changed constructor type"])
    return checked + ["failed five-name exploit", "names-only exploit", "explicit failed sparse receipt"]


def tests():
    p, c = panel()
    good = compare(p, c)
    source_identity_mutations = native_source_identity_controls(p, c)
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
    contract_source = json.loads((root / "research/RHRC/integration/post290/"
                                  "COUNTERMODEL_CONTRACTS.json").read_text())["source_id"]
    if {x["source_id"] for x in original["cuts"]} != {contract_source}:
        raise RuntimeError("survival cuts do not reuse the frozen contract source identifier")
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
    handoff_mutations = handoff_receipt_controls(
        good, original, formal, {"head": "a" * 40, "tree": "b" * 40}, contract)
    return {"schema": "post290.research-artifact-mutations.v1",
            "status": "PASS", "authority": "SYNTHETIC_VALIDATOR_TEST_ONLY",
            "claim_cap": "RH_OPEN",
            "tested": ["44-pair identity", "numerical inconsistency", "same-source protection",
                       "no generated-detector impersonation", "missing replay", "OPEN cuts",
                       "44 unreviewed proof fields", "compiler-candidate dossier",
                       "unapproved template integrity", "independent review gate", "handoff cap",
                       "exact compiler receipt authority guard", "worked same-source lower/upper comparison",
                       "literal full type and constructor visibility", "canonical per-path source identity maps"],
            "source_identity_mutations": source_identity_mutations,
            "source_identity_mutation_count": len(source_identity_mutations),
            "handoff_receipt_mutations": handoff_mutations,
            "handoff_receipt_mutation_count": len(handoff_mutations)}


if __name__ == "__main__":
    import json
    print(json.dumps(tests(), sort_keys=True))
