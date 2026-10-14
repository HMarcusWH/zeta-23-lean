#!/usr/bin/env python3
"""Generate a claim-capped Step4 research handoff from actual uploaded receipts.

Never upgrades paper deductions, finite observations, skipped workflows or
synthetic release fixtures into Lean proof authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
SECTIONS = (
    "What became formally true", "Workflow harvest", "What changed",
    "Upstream implications", "Downstream implications", "Resurrected routes",
    "New RH-relevant clues", "Falsification checks", "Highest-leverage next moves"
)


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def summarize(data):
    if data is None:
        return "NOT SUPPLIED — acceptance remains OPEN"
    return str(data.get("scientific_disposition",
               data.get("scope", data.get("status", "UNRESOLVED"))))


def build(formal, comparison, survival, d2, harvest, identity):
    if formal.get("claim_cap") != "RH_OPEN" or survival.get("claim_cap") != "RH_OPEN":
        raise ValueError("RH claim firewall violation")
    if survival.get("scientific_disposition") != "COUNTEREXAMPLE_SPACE_REMAINS_OPEN":
        raise ValueError("the countermodel audit has been improperly upgraded")
    completed = formal.get("producer_complete") is True
    reviewed = formal.get("independent_assumption_review_pass") is True
    if completed != reviewed:
        raise ValueError("inconsistent producer/independent review flags")
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
        "**Compiler:** " + summarize(formal),
        "**Native finite observations:** " + summarize(comparison),
        "**Countermodel-space audit:** " + summarize(survival),
        "**D2:** " + summarize(d2),
        ""
    ]
    sections = {
        "What became formally true":
            "The compiler receipt contains " + str(len(formal.get("declarations", [])) ) +
            " theorem roots and " + str(len(formal.get("definitions", []))) +
            " non-theorem roots; only independently checked exact-head entries can be labelled PROVED. "
            "Complete source/packet signoff: " + ("YES" if completed else "NO") + ".",
        "Workflow harvest":
            str(len(jobs)) + " recorded job attempts; " + str(len(pending)) +
            " unfinished, " + str(len(unresolved)) +
            " not independently accepted. Green replay alone is not new theorem authority.",
        "What changed":
            "The exact same-source physical trial, finite image, native response, signed histories, "
            "actual original-detector Schur complement and zero-indexed conditional packet are the objects to compose. "
            "No result was upgraded beyond its receipt.",
        "Upstream implications":
            "Reuse the fixed q/k/j/X/U/Y source and representative-independent compact weak-H2 inverse. "
            "Do not restore stronger regularity or replace the original detector with the selected ground.",
        "Downstream implications":
            "A-X and B-Y use the actual damped prime source and causal input. C-Schur concerns the full signed "
            "original-detector complement at shift -eta. No global exclusion follows without the OPEN antecedent.",
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
            "Finish the compact-inverse duality and source-bound forcing error, "
            "complete the exact 44-field packet and independent review, "
            "harvest every completed workflow job, and independently complete D2 without a retry/reset.",
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
