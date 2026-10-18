#!/usr/bin/env python3
"""Generate a claim-capped Step4 research handoff from actual uploaded receipts.

Never upgrades paper deductions, finite observations, skipped workflows or
synthetic release fixtures into Lean proof authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from build_formal_receipt import ALLOW, AUDIT, audit_roots, validate_full_type_fields

REPO = Path(__file__).resolve().parents[5]
SECTIONS = (
    "What became formally true", "Workflow harvest", "What changed",
    "Upstream implications", "Downstream implications", "Resurrected routes",
    "New RH-relevant clues", "Falsification checks", "Highest-leverage next moves"
)
INTEGRATED_ROOTS = frozenset({
    "Zeta23.ExceptionalZero.exists_generatedStep123CompleteOutput",
    "Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.forcingErrors",
    "Zeta23.CCM.Step123NativeOutput.n38_forcing_ambient_residuals",
    "Zeta23.CCM.Step123NativeOutput.originalDetectorPoleNormal_eq_smul_poleNormal",
    "Zeta23.CCM.Step123NativeOutput.originalInterior_not_ae_zero",
})
COMPARISON_ROOTS = frozenset({
    "Zeta23.ExceptionalZero.exists_generatedStep123CompleteOutput",
    "Zeta23.CCM.Step123NativeFieldRecord.fromNative",
    "Zeta23.CCM.Step123NativeOutput.original_depth",
    "Zeta23.CCM.Step123NativeFieldRecord.n07_trial_original_properties",
    "Zeta23.CCM.nativeWeilResponse_pairing",
    "Zeta23.CCM.n36_originalTrial_poleResponse_eq_zero",
    "Zeta23.CCM.originalDetector_primeResponse_pairing_le_sixteenKappa",
    "Zeta23.CCM.nativeWeilArchResponse_bilinear_bound",
    "Zeta23.CCM.Step123NativeFieldRecord.n25_schur_detector",
})


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def summarize(data):
    if data is None:
        return "NOT SUPPLIED — acceptance remains OPEN"
    return str(data.get("scientific_disposition",
               data.get("scope", data.get("status", "UNRESOLVED"))))


def validated_formal_roots(formal, identity):
    """Check receipt integrity before using a resolved name as proof evidence.

    An empty historical component fixture without execution evidence is allowed
    only as an explicitly unverified partial input. A populated or explicitly
    failed receipt must pass the actual compiler-receipt checks below. Hashes
    preserve the supplied compiler type; they do not replace semantic review.
    """
    head, tree = identity.get("head"), identity.get("tree")
    if any(re.fullmatch(r"[0-9a-f]{40}", str(value)) is None for value in (head, tree)):
        raise ValueError("handoff exact source identity missing")
    if formal.get("head") != head or formal.get("source_tree") != tree:
        raise ValueError("compiler receipt is not bound to the handoff exact source")
    declarations, definitions = formal.get("declarations", []), formal.get("definitions", [])
    if not isinstance(declarations, list) or not isinstance(definitions, list):
        raise ValueError("malformed compiler root lists")
    rows = declarations + definitions
    execution_keys = {"execution_status", "integrity_status", "compiler_context"}
    if not rows and not execution_keys.intersection(formal):
        if formal.get("producer_complete") is not False or formal.get("independent_assumption_review_pass") is not False:
            raise ValueError("unverified sparse input cannot claim producer signoff")
        return {}, False
    if not rows:
        raise ValueError("claimed compiler audit has no resolved roots")
    if (formal.get("schema_version") != "RH_POST290_COMPONENT_COMPILER_RECEIPT_1.0"
            or formal.get("execution_status") != "SUCCESS"
            or formal.get("integrity_status") != "PASS"):
        raise ValueError("formal compiler receipt execution/integrity unverified")
    context = formal.get("compiler_context")
    if not isinstance(context, dict) or context.get("head") != head or context.get("tree") != tree:
        raise ValueError("compiler-generated head/tree context missing or stale")
    declared = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    version = declared.rsplit(":v", 1)[-1]
    packages = json.loads((REPO / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    expected_dependencies = {package["name"]: package["rev"] for package in packages}
    mathlib = expected_dependencies.get("mathlib")
    dependencies = context.get("dependencies")
    if (context.get("declared_toolchain") != declared
            or not isinstance(context.get("actual_compiler_version"), str)
            or re.search(r"\bversion " + re.escape(version) + r"(?=[,\s)]|$)",
                         context["actual_compiler_version"]) is None
            or not mathlib or context.get("mathlib_revision") != mathlib
            or context.get("tracked_lean_toolchain_manifest_clean") is not True
            or not isinstance(dependencies, list)
            or len(dependencies) != len(expected_dependencies)):
        raise ValueError("compiler toolchain/Mathlib/clean-source context unverified")
    dependency_names = set()
    for dependency in dependencies:
        if (not isinstance(dependency, dict)
                or not isinstance(dependency.get("package"), str)
                or dependency["package"] in dependency_names
                or dependency["package"] not in expected_dependencies
                or dependency.get("revision") != expected_dependencies[dependency["package"]]
                or dependency.get("lean_source_clean") is not True):
            raise ValueError("compiler dependency revision/clean-source context unverified")
        dependency_names.add(dependency["package"])
    if re.fullmatch(r"[0-9a-f]{64}", str(formal.get("compiler_log_sha256"))) is None:
        raise ValueError("compiler log content identity missing")
    if type(formal.get("audited_root_count")) is not int or formal["audited_root_count"] != len(rows):
        raise ValueError("compiler audited-root count differs from receipt")
    expected_modules, expected_kinds = audit_roots(AUDIT.read_text(encoding="utf-8-sig"))
    checked = {}
    for category, records in (("theorem", declarations), ("data", definitions)):
        for row in records:
            if not isinstance(row, dict):
                raise ValueError("malformed compiler declaration receipt")
            name = row.get("declaration", row.get("theorem"))
            kind = row.get("declaration_kind")
            text = row.get("normalized_type")
            axioms = row.get("axioms")
            if (not isinstance(name, str) or name in checked
                    or name not in expected_modules
                    or row.get("theorem", name) != name
                    or row.get("module") != expected_modules[name]
                    or kind != expected_kinds[name]
                    or (category == "theorem") != (kind == "THEOREM")
                    or row.get("authority") != ("PROVED" if kind == "THEOREM" else "DEFINED_DATA_NOT_A_THEOREM")
                    or row.get("source_tree") != tree
                    or not isinstance(text, str) or not text.strip()
                    or hashlib.sha256(text.encode("utf-8")).hexdigest() != row.get("normalized_type_sha256")
                    or row.get("axiom_audit_pass") is not True
                    or not isinstance(axioms, list)
                    or any(not isinstance(axiom, str) for axiom in axioms)
                    or len(axioms) != len(set(axioms)) or not set(axioms) <= ALLOW):
                raise ValueError("unverified, duplicate, forged or stale compiler root: " + str(name))
            validate_full_type_fields(row)
            checked[name] = row
    return checked, True


def worked_comparison(audited):
    qualification = (
        "PROVED ingredients (audited exact-source roots; no closing law is supplied): "
        if audited else
        "LEAD / conditional source-analysis target: this input does not audit all comparison roots. "
        "The following equations describe the required same-source composition, not new proof authority from this handoff. "
    )
    return qualification + (
        "Under a hypothetical off-line zero, take one generated packet with 0<beta<|Re rho-1/2|; "
        "the two original phases are separately cofinal. Put f=out.originalTrial, "
        "L=2a+2(1+s0), kappa=fixedOriginalSincTrialNormalization, "
        "X_L=||X||_L2[0,L]. The retained N39 original depth is exactly "
        "Re W(f,f)<=-4 exp(beta L), with ||f||_2=1 and both elementary-pole moments zero. "
        "For the literal original response, write W(f,f)=A_f-P_f (Arch minus all four prime histories), "
        "and |P_f|<=16 kappa X_L. The finite detector and selected ground are different objects.\n\n"
        "DERIVED comparison, conditional on those proved ingredients and not separately formalized here: "
        "||1_[0,L]R(f)||_2>=4 exp(beta L), and "
        "16 kappa X_L>=4 exp(beta L)+Re A_f>=4 exp(beta L)-|A_f|. "
        "The prime-only estimate is not an upper bound on the total response.\n\n"
        "LEAD (a precise source-only helper and composition remain to be formalized): with "
        "M1=originalDetectorOriginalPhaseJetSupBudget 1 and "
        "B1=originalDetectorOriginalPhaseL1JetBudget 1, the existing derivative sup/L1 bounds suggest "
        "H1(f)^2<=1+M1 B1. The separate aperture-independent Arch theorem gives "
        "|A_f|<=C_A H1(f)^2, so A_0=C_A(1+M1 B1) would imply "
        "X_L>=(4 exp(beta L)-A_0)/(16 kappa). "
        "Using the total-form exp(L/2) bound in place of this Arch bound would not supply that source-only constant. "
        "This is a lower bound on actual X, compatible with the off-line hypothesis; it does not prove A-X.\n\n"
        + ("PROVED C-Schur lower ingredient: " if audited else "Conditional C-Schur lower target: ") +
        "on the SAME generated packet the original full-complement loss "
        "S=-Re<Schur_(-eta)y,y> satisfies S>exp(beta L)/2. "
        "OPEN C-Schur upper law: S<=C exp(epsilon L), uniformly for the actual admissible original-source selectors "
        "beyond a source threshold. If independently established with 0<epsilon<beta, cofinality gives the worked "
        "same-source comparison C exp(epsilon L)<exp(beta L)/2<S<=C exp(epsilon L), a contradiction. "
        "The upper law is not established here. Neither the selected one-shell loss at lambda, normal/outer residual "
        "vanishing, a finite numerical panel, nor the accurate N37 bridge supplies it. A-X, B-Y and C-Schur remain OPEN."
    )


def build(formal, comparison, survival, d2, harvest, identity):
    if formal.get("claim_cap") != "RH_OPEN" or survival.get("claim_cap") != "RH_OPEN":
        raise ValueError("RH claim firewall violation")
    if survival.get("scientific_disposition") != "COUNTEREXAMPLE_SPACE_REMAINS_OPEN":
        raise ValueError("the countermodel audit has been improperly upgraded")
    completed = formal.get("producer_complete") is True
    reviewed = formal.get("independent_assumption_review_pass") is True
    if completed != reviewed:
        raise ValueError("inconsistent producer/independent review flags")
    roots, compiler_audited = validated_formal_roots(formal, identity)
    integrated = compiler_audited and INTEGRATED_ROOTS <= roots.keys()
    comparison_audited = compiler_audited and COMPARISON_ROOTS <= roots.keys()
    jobs = harvest.get("jobs", []) if harvest else []
    pending = [j for j in jobs if j.get("status") != "completed"]
    unresolved = [j for j in jobs if j.get("conclusion") != "success"
                  or j.get("scientific_acceptance") is not True
                  or j.get("output_reviewed") is not True]
    lines = [
        "# PR #292 — Step 4 research handoff",
        "",
        "**Status:** RH OPEN. Three independently stated upper/membership laws A-X, B-Y, C-Schur remain OPEN.",
        "",
        "**Source identity:** `" + identity["head"] + "`, tree `" + identity["tree"] + "`.",
        "**Compiler:** " + (summarize(formal) if compiler_audited else
                            "UNVERIFIED SPARSE COMPONENT INPUT; no audited theorem authority"),
        "**Native finite observations:** " + summarize(comparison),
        "**Countermodel-space audit:** " + summarize(survival),
        "**D2:** " + summarize(d2),
        ""
    ]
    sections = {
        "What became formally true":
            ("The audited exact-source compiler receipt contains " if compiler_audited else
             "This sparse component input establishes no audited formal result. It contains ") +
            str(len(formal.get("declarations", [])) ) +
            " theorem roots and " + str(len(formal.get("definitions", []))) +
            " non-theorem roots; only audited exact-head compiler entries carry component proof authority. "
            "Complete source/packet signoff: " + ("YES" if completed else "NO") + ".",
        "Workflow harvest":
            str(len(jobs)) + " recorded job attempts; " + str(len(pending)) +
            " unfinished, " + str(len(unresolved)) +
            " not independently accepted. Green replay alone is not new theorem authority.",
        "What changed":
            ("The audited receipt resolves the same-packet interfaces, common N14/N37 source threshold, "
             "actual original-detector legal/neutral/pole-normal/outer decomposition and "
             "original interior nonvanishing as an AE class. Independent 44-field semantic "
             "signoff remains a separate gate. " if integrated else "") +
            "The exact same-source physical trial, finite image, native response, signed histories, "
            "actual original-detector Schur complement and zero-indexed conditional packet are the objects to compose. "
            "No result was upgraded beyond its receipt.",
        "Upstream implications":
            "Reuse the fixed q/k/j/X/U/Y source and representative-independent compact weak-H2 inverse. "
            "Do not restore stronger regularity or replace the original detector with the selected ground.",
        "Downstream implications":
            "A-X and B-Y use the actual damped prime source and causal input. C-Schur concerns the full signed "
            "original-detector complement at shift -eta. No global exclusion follows without the OPEN antecedent.\n\n" +
            worked_comparison(comparison_audited),
        "Resurrected routes":
            "Revisit source-specific compact inverse/local-to-exterior duality only with retained interior history. "
            "Keep parity-gap and generic monotonicity falsifications intact.",
        "New RH-relevant clues":
            "LEAD: the exact four signed original histories plus complete Schur loss may encode a "
            "source-dependent obstruction invisible to generic finite-dimensional geometry.",
        "Falsification checks":
            "Try opposite phases separately; tied/empty-predecessor cases; asymmetric probes; "
            "eta-versus-lambda substitutions; original history nonzero; modified-prime controls "
            "respecting or violating the native divisor law. No numerical observation proves a universal estimate.",
        "Highest-leverage next moves":
            ("Review the compiled 44-field same-packet projections and formalize the explicit "
             "uniform original-source H1 helper and Archimedean-to-X composition as a separate "
             "proof of the existing A-X implication. " if integrated else
             "Finish the source-bound field obligations identified by the compiler receipt. ") +
            "Arrange authenticated independent 44-field review and harvest every completed job. "
            "D2 remains OPEN; any new checker or continuation needs separate authorization.",
    }
    for name in SECTIONS:
        lines.extend(["## " + name, "", sections[name], ""])
    lines.extend(["## References and authority", "",
                  "All input hashes and the checked repository head/tree are recorded in the sibling handoff manifest. "
                  "This document is not a proof of RH.", ""])
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--formal", type=Path, required=True)
    p.add_argument("--comparison", type=Path, required=True)
    p.add_argument("--survival", type=Path, required=True)
    p.add_argument("--d2", type=Path)
    p.add_argument("--harvest", type=Path)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    git = lambda *xs: subprocess.check_output(["git", *xs], cwd=REPO, text=True).strip()
    identity = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}")}
    formal, comparison, survival = load(a.formal), load(a.comparison), load(a.survival)
    if formal.get("head") != identity["head"] or formal.get("source_tree") != identity["tree"]:
        raise ValueError("compiler receipt is not bound to the current exact source")
    d2 = load(a.d2) if a.d2 else None
    harvest = load(a.harvest) if a.harvest else None
    doc = build(formal, comparison, survival, d2, harvest, identity)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(doc, encoding="utf-8")
    manifest = {"schema": "post290.step4-handoff-provenance.v1",
                "claim_cap": "RH_OPEN", "source": identity,
                "inputs": {name: {"path": str(path), "sha256": sha256(path)}
                           for name, path in (("formal", a.formal), ("comparison", a.comparison),
                                              ("survival", a.survival), ("d2", a.d2), ("harvest", a.harvest))
                           if path is not None},
                "document_sha256": sha256(a.out),
                "authority": "RESEARCH_HANDOFF_ONLY; NO_RH_PROOF"}
    a.out.with_suffix(a.out.suffix + ".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"head": identity["head"], "claim_cap": "RH_OPEN",
                      "document_sha256": manifest["document_sha256"]}))


if __name__ == "__main__":
    main()
