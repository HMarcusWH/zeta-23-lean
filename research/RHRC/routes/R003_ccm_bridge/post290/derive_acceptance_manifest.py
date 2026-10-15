#!/usr/bin/env python3
"""Derive current PR292 module/work-package acceptance from exact evidence.

The original BUILD_MANIFEST.json is immutable historical input. This script
never edits it and never promotes a filename, source comment, status flag, or
numerical sample into a Lean theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from d2_source_equivalence import exact_numeric_source, verify_d2_receipt

REPO = Path(__file__).resolve().parents[5]
FROZEN = REPO / "research/RHRC/integration/post290/spec/BUILD_MANIFEST.json"
ACCEPTED_AX = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_PRODUCTS = (
    "STEP123_FORMAL_OUTPUT.json", "SOURCE_LINEAGE.json", "CONSTRAINTS.json",
    "NATIVE_OBSERVATIONS.jsonl", "RESIDUAL_CHANNELS.jsonl",
    "COUNTERMODEL_SURVIVAL.json", "D2_CONTINUUM_RECEIPT.json",
    "STEP4_CUTS.json", "WORKFLOW_HARVEST.json", "WORKFLOW_HARVEST.md",
    "STEP4_RESEARCH_HANDOFF.md", "MATERIALIZATION_RECEIPT.json",
)


def get_commit() -> tuple[str, str]:
    git = lambda *args: subprocess.check_output(("git", *args), cwd=REPO, text=True).strip()
    return git("rev-parse", "HEAD"), git("rev-parse", "HEAD^{tree}")


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def hfile(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def accepted_formal_roots(formal: dict, head: str, tree: str) -> dict[str, dict]:
    if (formal.get("head") != head or formal.get("source_tree") != tree or
        formal.get("execution_status") != "SUCCESS" or formal.get("integrity_status") != "PASS" or
        formal.get("producer_complete") is not True or
        formal.get("independent_assumption_review_pass") is not True):
        return {}
    roots = {}
    for item in formal.get("declarations", []) + formal.get("definitions", []):
        key = item.get("declaration", item.get("theorem"))
        kind = item.get("declaration_kind")
        expected_auth = "PROVED" if kind == "THEOREM" else "DEFINED_DATA_NOT_A_THEOREM"
        actual_type = item.get("normalized_type")
        if (not isinstance(key, str) or key in roots or not isinstance(actual_type, str) or
            not actual_type or htext(actual_type) != item.get("normalized_type_sha256") or
            item.get("source_tree") != tree or item.get("authority") != expected_auth or
            item.get("axiom_audit_pass") is not True or
            not isinstance(item.get("axioms"), list) or
            not set(item["axioms"]) <= ACCEPTED_AX):
            return {}
        roots[key] = item
    return roots


def htext(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def accepted_review(review: dict, head: str, tree: str, roots: dict) -> bool:
    fields = review.get("field_reviews", [])
    required = {f"N{i:02d}" for i in range(1, 41)} | {f"G{i:02d}" for i in range(1, 5)}
    return (
        review.get("schema_version") == "POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0"
        and review.get("reviewed_head") == head and review.get("reviewed_tree") == tree
        and review.get("reviewer_is_source_author") is False
        and review.get("independent_assumption_review_pass") is True
        and review.get("reviewer_identity") not in (None, "", "SELF", "AUTOMATED")
        and isinstance(review.get("external_review_reference"), str)
        and bool(review["external_review_reference"])
        and isinstance(fields, list) and len(fields) == 44
        and {f.get("id") for f in fields} == required
        and all(f.get("semantic_proof_review") == "PASS"
                and f.get("evidence_verified") is True
                and f.get("declaration_ref") in roots
                and isinstance(f.get("reason"), str) and bool(f["reason"]) for f in fields)
    )


def verified_outputs(directory: Path, head: str, tree: str) -> bool:
    if not all((directory / name).is_file() and (directory / name).stat().st_size > 0
               for name in EXPECTED_PRODUCTS):
        return False
    receipt = read(directory / "MATERIALIZATION_RECEIPT.json")
    if (receipt.get("head") != head or receipt.get("tree") != tree or
        receipt.get("producer_complete") is not True):
        return False
    recorded = receipt.get("outputs", {})
    if not isinstance(recorded, dict):
        return False
    # The receipt does not hash itself, and the status file may be added later.
    for filename in EXPECTED_PRODUCTS:
        if filename == "MATERIALIZATION_RECEIPT.json":
            continue
        if recorded.get(filename) != hfile(directory / filename):
            return False
    return True


def derive(formal: dict, review: dict, d2: dict, harvest: dict,
           output_dir: Path, graph_checked: bool = False) -> dict:
    """Unproved, unreviewed or incomplete evidence stays INCOMPLETE."""
    baseline = read(FROZEN)
    head, tree = get_commit()
    roots = accepted_formal_roots(formal, head, tree)
    reviewed = bool(roots) and accepted_review(review, head, tree, roots)
    evidence_ok = reviewed and graph_checked

    numerical_ok = False
    d2_identity_error = None
    try:
        equivalence = exact_numeric_source(head, tree)
        verify_d2_receipt(d2, equivalence)
        numerical_ok = (d2.get("status") == "D2_COMPLETE"
                        and d2.get("independent_nonpartial_verified") is True
                        and d2.get("complete_layers") == 30
                        and d2.get("both_parities") is True
                        and d2.get("physical_seams_verified") is True
                        and all(type(d2.get(key)) is int and d2[key] == 0 for key in
                                ("unrun_tiles", "missing_artifacts", "unresolved_tiles",
                                 "unverified_tiles", "nonfinite_enclosures")))
    except (ValueError, KeyError, subprocess.CalledProcessError) as exc:
        d2_identity_error = str(exc)

    # Validate each original export, its kind, exact type and approved axioms.
    api = read(REPO / "research/RHRC/integration/post290/review_execution_2026-10-14/spec/API_CROSSWALK.json")
    kind_map = {entry["requested_name"]: entry["required_kind"] for entry in api["rows"]}
    kind_map = {k: "INDUCTIVE" if v == "STRUCTURE" else v for k, v in kind_map.items()}
    modules = []
    status = {}
    for item in baseline["new_lean_modules"]:
        declared = item["proposed_exports"]
        passed = (evidence_ok and
                  all(name in roots and roots[name]["declaration_kind"] == kind_map.get(name)
                      for name in declared))
        if not declared:  # M25 is a compiler-binding module, not an empty proof obligation.
            passed = (evidence_ok and
                      "Zeta23/RHRC/Step123OutputBindings.lean" in {
                          entry["path"] for entry in formal.get("source_blobs", [])})
        entry = dict(item)
        entry["status"] = "COMPLETE_VERIFIED" if passed else "INCOMPLETE"
        entry["status_authority"] = "EXACT_COMPILER_AND_INDEPENDENT_REVIEW" if passed else "OPEN"
        modules.append(entry)
        status[item["id"]] = passed

    workflow_jobs = harvest.get("jobs", [])
    complete_harvest = (isinstance(workflow_jobs, list) and bool(workflow_jobs)
                        and harvest.get("head") == head
                        and all(job.get("output_reviewed") is True
                                and job.get("classification") in (
                                    "FORMAL_VALIDITY_GATE", "REGRESSION_GATE",
                                    "RESEARCH_PRODUCING_CHECK")
                                for job in workflow_jobs)
                        and all(job.get("scientific_acceptance") is True
                                and job.get("status") == "completed"
                                and job.get("conclusion") == "success"
                                for job in workflow_jobs if job.get("required") is True))
    all_outputs = verified_outputs(output_dir, head, tree)
    packages = []
    done = {}
    for item in baseline["work_packages"]:
        dep_ok = all(done.get(w, False) for w in item.get("depends_on", []))
        if item["id"] == "W00":
            passed = evidence_ok and bool(formal.get("compiler_context"))
        elif item["id"] == "W09":
            passed = numerical_ok and dep_ok
        elif item["id"] == "W10":
            passed = dep_ok and complete_harvest and all_outputs
        else:
            passed = dep_ok and evidence_ok and all(status.get(m, False) for m in item["module_ids"])
        entry = dict(item)
        entry["status"] = "COMPLETE_VERIFIED" if passed else "INCOMPLETE"
        entry["status_authority"] = "DERIVED_FROM_VERIFIED_EVIDENCE" if passed else "OPEN"
        packages.append(entry)
        done[item["id"]] = passed

    result = dict(baseline)
    result["status"] = "COMPLETE_VERIFIED_RH_OPEN" if all(done.values()) else "PARTIAL_OUTPUT_RH_OPEN"
    result["new_lean_modules"] = modules
    result["work_packages"] = packages
    result["source_status"] = {
        "head": head, "tree": tree, "original_manifest_sha256": hfile(FROZEN),
        "producer_compiler_verified": bool(roots),
        "independent_44_field_reviewed": reviewed,
        "graph_checked_before_materialization": graph_checked,
        "d2_nonpartial_source_matched": numerical_ok,
        "d2_identity_error": d2_identity_error,
        "every_job_scientific_reviewed": complete_harvest,
        "outputs_digest_verified": all_outputs,
        "status_not_mathematical_authority": True, "claim_cap": "RH_OPEN",
    }
    result["claim_cap"] = "RH_OPEN"
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("formal", "review", "d2", "harvest", "output-dir", "out"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--graph-precheck-passed", action="store_true")
    args = parser.parse_args()
    result = derive(read(args.formal), read(args.review), read(args.d2), read(args.harvest),
                    args.output_dir, args.graph_precheck_passed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "head": result["source_status"]["head"],
                      "complete_packages": sum(x["status"] == "COMPLETE_VERIFIED"
                                               for x in result["work_packages"])}))


if __name__ == "__main__":
    main()
