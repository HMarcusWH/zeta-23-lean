#!/usr/bin/env python3
"""Prepare the mandatory 44-field INDEPENDENT review dossier.

This tool never performs the independent review. It binds candidate proof
names to the actual exact-head compiler receipt, preserves full types and
axioms, and emits an explicitly unapproved review template. A reviewer
who is not a source author must verify all fields separately before
complete-output mode may accept any approval.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
FIELDS = REPO / "research/RHRC/integration/post290/review_execution_2026-10-14/spec/OUTPUT_FIELD_CONTRACT.json"

# Concrete source-linked candidates. A listed name is a REVIEW QUESTION,
# not a proof of the whole corresponding field. Only a compiler receipt
# and external semantic review can promote it.
CANDIDATES = {
    "N01": ["Zeta23.CCM.universalSincSource"],
    "N02": ["Zeta23.CCM.universalSincSource", "Zeta23.CCM.universalSincKernel",
            "Zeta23.CCM.universalSincSecondKernel"],
    "N03": ["Zeta23.CCM.step123_fixed_source_evidence"],
    "N04": ["Zeta23.CCM.poleKilled_universalSincSource_norm_sq",
            "Zeta23.CCM.universalSincSource_gevrey_bound"],
    "N05": ["Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture",
            "Zeta23.CCM.nativeOriginalDetectorPhaseSign"],
    "N06": ["Zeta23.CCM.Step123NativeOutput.originalTrial"],
    "N07": ["Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_integral_norm_sq",
            "Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_reflected_formula"],
    "N08": ["Zeta23.CCM.originalDetectorPaddedFinitePhaseUnitVector"],
    "N09": ["Zeta23.CCM.originalDetectorPaddedFinitePhaseUnitVector_native_poles_zero"],
    "N10": ["Zeta23.CCM.originalDetectorFiniteImage_endpointJets"],
    "N11": ["Zeta23.CCM.nativeOriginalDetectorPaddedUnit"],
    "N12": ["Zeta23.CCM.Step123NativeOutput.detector_source_unit"],
    "N13": ["Zeta23.CCM.Step123NativeOutput.finitePhysicalSource_eq_originalPadded"],
    "N14": ["Zeta23.CCM.Step123NativeOutput.finite_image_H1_bound",
            "Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_H1_concrete_rate"],
    "N15": ["Zeta23.CCM.originalDetectorPaddedFinitePhaseGram"],
    "N16": ["Zeta23.CCM.originalDetectorPhaseRayleigh_eq"],
    "N17": ["Zeta23.CCM.DetectorRetainedSchurState"],
    "N18": ["Zeta23.CCM.NativeDeepThresholdGroundData"],
    "N19": ["Zeta23.CCM.Step123NativeOutput.detector_inverse_budget",
            "Zeta23.CCM.Step123NativeOutput.selected_inverse_budget"],
    "N20": ["Zeta23.CCM.Step123NativeOutput.selected_ground_eigen"],
    "N21": ["Zeta23.CCM.poleNeutralGround_branch_exhaustive"],
    "N22": ["Zeta23.CCM.canonicalPoleNeutral_rankOneIntertwining"],
    "N23": ["Zeta23.CCM.poleNeutral_tied_kernel_compatibility"],
    "N24": ["Zeta23.CCM.AdmissibleDetectorSelector"],
    "N25": ["Zeta23.CCM.Step123NativeOutput.original_detector_complement_dimension",
            "Zeta23.CCM.Step123NativeOutput.originalSchur_full_complement"],
    "N26": ["Zeta23.CCM.Step123NativeOutput.selected_ground_shiftedSchur"],
    "N27": ["Zeta23.CCM.Step123NativeOutput.ownNeutralResidual_variance"],
    "N28": ["Zeta23.CCM.Step123NativeOutput.ownNeutralResidual_gram"],
    "N29": ["Zeta23.CCM.Step123NativeArithmeticRangeEvidence.fromNative",
            "Zeta23.CCM.originalDetector_correlationField_eq_sourceConvolution"],
    "N30": ["Zeta23.CCM.Step123NativeArithmeticRangeEvidence.fromNative",
            "Zeta23.CCM.nativeOriginalIntegerDrive_rapid_bound"],
    "N31": ["Zeta23.CCM.Step123NativeArithmeticRangeEvidence.fromNative",
            "Zeta23.CCM.Step123NativeOutput.rangeView_eq_actual"],
    "N32": ["Zeta23.CCM.nativeCompletedInput_complexLaplace"],
    "N33": ["Zeta23.CCM.Step123NativeArithmeticRangeEvidence.fromNative",
            "Zeta23.CCM.nativeDampedCompletionCausalL2Operator"],
    "N34": ["Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_residual_pairing"],
    "N35": ["Zeta23.CCM.originalDetectorNativeForcing_physical_mixed"],
    "N36": ["Zeta23.CCM.NativeCompactPoleH2.originalSmoothFourPrimeHistories_to_actualX",
            "Zeta23.CCM.originalDetector_nativeFourPrimeHistories",
            "Zeta23.CCM.NativeCompactPoleH2.originalKernelPrimeField_localPairing"],
    "N37": ["Zeta23.CCM.Step123NativeOutput.actualProjectedForcing_error_bound",
            "Zeta23.CCM.originalDetector_eta_source_upper"],
    "N38": ["Zeta23.CCM.Step123NativeOutput.selectedResponse_decomposition",
            "Zeta23.CCM.Step123NativeOutput.selectedOuterGalerkin_orthogonal"],
    "N39": ["Zeta23.CCM.originalSmoothWeilResponse_reconstruction"],
    "N40": ["Zeta23.CCM.originalSmoothRightBoundary_convolution_split",
            "Zeta23.CCM.originalSmoothRightBoundary_pointwise_cut",
            "Zeta23.CCM.originalSmoothWeilResponse_compactPairing_split",
            "Zeta23.CCM.originalNativeFourHistories_common_finite_cutoff",
            "Zeta23.CCM.originalNativeExterior_history_eq"],
    "G01": ["Zeta23.ExceptionalZero.GeneratedStep123Output"],
    "G02": ["Zeta23.ExceptionalZero.exists_generatedStep123Output_cofinal"],
    "G03": ["Zeta23.CCM.exists_generatedStep123IntegratedPacket",
            "Zeta23.ExceptionalZero.exists_generatedStep123BoundaryPacket",
            "Zeta23.ExceptionalZero.exists_step123Output_of_offLine_zero"],
    "G04": ["Zeta23.ExceptionalZero.nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero"],
}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def produce(formal, contract, head, tree):
    groups = contract.get("field_groups", [])
    ids = {r.get("id") for r in groups}
    if len(groups) != 44 or len(ids) != 44 or set(CANDIDATES) != ids:
        raise ValueError("the original 44-field contract does not match the required review mapping")
    if formal.get("head") != head or formal.get("source_tree") != tree:
        raise ValueError("not exact-head compiler evidence")
    if formal.get("claim_cap") != "RH_OPEN":
        raise ValueError("wrong compiler claim cap")
    available = {}
    for root in formal.get("declarations", []) + formal.get("definitions", []):
        name = root.get("declaration", root.get("theorem"))
        if name in available or not name:
            raise ValueError("duplicate or unnamed compiler declaration")
        if root.get("source_tree") != tree:
            raise ValueError("compiler declaration at another tree")
        data = root.get("normalized_type")
        if not isinstance(data, str) or hashlib.sha256(data.encode()).hexdigest() != root.get("normalized_type_sha256"):
            raise ValueError("wrong compiler normalized type")
        if set(root.get("axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("unadmitted root is not reviewable")
        available[name] = root
    rows = []
    for field in groups:
        matched = []
        absent = []
        for name in CANDIDATES[field["id"]]:
            if name in available:
                root = available[name]
                matched.append({
                    "name": name,
                    "kind": root["declaration_kind"],
                    "module": root["module"],
                    "normalized_type": root["normalized_type"],
                    "normalized_type_sha256": root["normalized_type_sha256"],
                    "axioms": root.get("axioms", []),
                    "compiler_eligible": root.get("axiom_audit_pass") is True,
                })
            else:
                absent.append(name)
        rows.append({
            "id": field["id"],
            "field": field["field"],
            "exact_requirement": field["exact_content"],
            "original_task": field["task"],
            "required_kind": field["kind"],
            "producer": field["producer"],
            "candidate_declarations": matched,
            "not_receipted_candidates": absent,
            "missing_semantic_proof_review": True,
            "reviewed": False,
            "evidence_verified": False,
            "candidate_coverage_not_a_proof": True,
            "review_question": (
                "Does this exact declaration/theorem and its hypotheses prove the WHOLE frozen field "
                "for the same original source, normalized image, selected state, branch and interval?"
            ),
        })
    dossier = {
        "schema_version": "POST290_44_FIELD_REVIEW_DOSSIER_1.0",
        "source_head": head,
        "source_tree": tree,
        "claim_cap": "RH_OPEN",
        "authority": "UNREVIEWED_COMPILER_CANDIDATES_ONLY",
        "field_count": len(rows),
        "not_independently_reviewed": len(rows),
        "fields": rows,
    }
    template = {
        "schema_version": "POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0",
        "reviewed_head": head,
        "reviewed_tree": tree,
        "claim_cap": "RH_OPEN",
        "reviewer_identity": None,
        "external_review_reference": None,
        "reviewer_is_source_author": None,
        "independent_assumption_review_pass": False,
        "field_reviews": [{
            "id": row["id"],
            "declaration_ref": row["candidate_declarations"][0]["name"]
                if row["candidate_declarations"] else None,
            "semantic_proof_review": "NOT_REVIEWED",
            "evidence_verified": False,
            "reason": "Unreviewed template; independent mathematical verification required.",
        } for row in rows],
        "warning": "TEMPLATE_NOT_AUTHORITY; must fail complete-output release until external review.",
    }
    return dossier, template


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--formal", type=Path, required=True)
    p.add_argument("--out-dir", type=Path, required=True)
    a = p.parse_args()
    head, tree = git("rev-parse", "HEAD"), git("rev-parse", "HEAD^{tree}")
    dossier, template = produce(json.loads(a.formal.read_text()),
                                json.loads(FIELDS.read_text()), head, tree)
    write(a.out_dir / "FIELD_REVIEW_DOSSIER.json", dossier)
    write(a.out_dir / "INDEPENDENT_REVIEW_TEMPLATE_UNAPPROVED.json", template)
    print(json.dumps({"fields": dossier["field_count"], "unreviewed": 44,
                      "claim_cap": "RH_OPEN", "source_head": head, "source_tree": tree}))


if __name__ == "__main__":
    main()
