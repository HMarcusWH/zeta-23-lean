#!/usr/bin/env python3
"""Source-faithful Step 4 countermodel survival audit, never an RH proof.

An exact conditional sufficiency theorem restricts the counterexample space
only once its OPEN antecedent is proved. A finite-point replay does not prove
an all-aperture signed Schur bound or any global range property.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from symbolic_step123_artifacts import SOURCE_ID

CUTS = ("A-X", "B-Y", "C-Schur")
FROZEN_COUNTERMODEL_CONTRACT = (Path(__file__).resolve().parents[5] /
    "research/RHRC/integration/post290/COUNTERMODEL_CONTRACTS.json")


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def hashfile(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()



def validate_survival_source_ids(survival):
    """Original A/B/C cuts use the frozen canonical source, not a countermodel."""
    contract = load(FROZEN_COUNTERMODEL_CONTRACT)
    canonical = contract.get("source_id")
    if (contract.get("claim_cap") != "RH_OPEN" or
        contract.get("open_cuts") != list(CUTS) or
        canonical != SOURCE_ID):
        raise ValueError("frozen countermodel source contract mismatch")
    if not isinstance(survival, dict) or survival.get("claim_cap") != "RH_OPEN":
        raise ValueError("countermodel survival claim cap mismatch")
    rows = survival.get("cuts")
    if (not isinstance(rows, list) or len(rows) != len(CUTS) or
        {item.get("id") for item in rows if isinstance(item, dict)} != set(CUTS)):
        raise ValueError("countermodel survival cuts missing, duplicated or altered")
    if any(item.get("source_id") != canonical or item.get("status") != "OPEN"
           for item in rows):
        raise ValueError("countermodel survival source ID or cut status mismatch")
    return canonical


def audit(comparison, cuts, *, formal=None, d2=None):
    if load(FROZEN_COUNTERMODEL_CONTRACT).get("source_id") != SOURCE_ID:
        raise ValueError("countermodel source disagrees with frozen contract")
    if comparison.get("claim_cap") != "RH_OPEN":
        raise ValueError("representation comparison has wrong claim cap")
    if comparison.get("discrepancies"):
        raise ValueError("numerical discrepancies require investigation before interpretation")
    cut_records = cuts.get("cuts", [])
    by_name = {x.get("id"): x for x in cut_records}
    if set(by_name) != set(CUTS) or len(cut_records) != len(CUTS):
        raise ValueError("original three independent cuts not preserved")
    if cuts.get("claim_cap") != "RH_OPEN":
        raise ValueError("original frozen cut source incorrectly promotes RH")
    if formal is not None and formal.get("claim_cap") != "RH_OPEN":
        raise ValueError("formal receipt violates RH claim cap")
    if d2 is not None and d2.get("terminal_claim", d2.get("RH", "RH_OPEN")) != "RH_OPEN":
        raise ValueError("external D2 receipt promoted to RH authority")
    has_compiler = bool(formal and formal.get("execution_status") == "SUCCESS"
                        and formal.get("integrity_status") == "PASS")
    results = []
    descriptions = {
        "A-X": "Literal fixed-source von Mangoldt prime field is L2 at every positive damping.",
        "B-Y": "Literal causal-completion input lies in the actual causal-operator range closure at every positive damping.",
        "C-Schur": "For all source-generated selectors and either original phase, the full signed detector complement loss has a source-specific subexponential upper bound.",
    }
    for cut_id in CUTS:
        item = by_name[cut_id]
        if item.get("status") != "OPEN":
            raise ValueError("no independent verified promotion of the original cut: " + cut_id)
        results.append({
            "id": cut_id,
            "source_id": SOURCE_ID,
            "status": "OPEN",
            "necessary_to_exclude": descriptions[cut_id],
            "conditional_sufficiency_ref": item.get("core_formal_sufficiency_module"),
            "compiler_receipt_available": has_compiler,
            "antecedent_proved": False,
            "countermodels_eliminated_by_current_data": False,
            "surviving_case": "Every hypothetical off-critical zero not excluded by an independently proved cut remains admissible to this audit.",
            "fast_falsifier": (
                "Test exact divisor identity under any modified prime sequence"
                if cut_id == "A-X" else
                "Construct an actual causal adjoint witness and test the nonzero Y pairing"
                if cut_id == "B-Y" else
                "Probe full signed Schur complement, parity ties, eta/lambda distinction and the original interior-history contribution"
            ),
        })
    d2_complete = bool(d2 and d2.get("status") == "D2_COMPLETE"
                       and d2.get("independent_nonpartial_verified") is True
                       and d2.get("complete_layers") == 30)
    result = {
        "schema": "post290.countermodel-survival.v1",
        "claim_cap": "RH_OPEN",
        "scientific_disposition": "COUNTEREXAMPLE_SPACE_REMAINS_OPEN",
        "source_identity": comparison.get("source_identity"),
        "finite_probe_comparison": comparison.get("scientific_disposition"),
        "observed_finite_pairs": comparison.get("consistent_pair_count", 0),
        "observation_authority": "FINITE_ONLY_NO_GLOBAL_EXCLUSION",
        "d2_finite_certification_complete": d2_complete,
        "d2_implies_rh": False,
        "cuts": results,
        "logical_status": {
            "conditional_A_X_and_B_Y": "PROVED_ONLY_IF_EXACT_LEAN_RECEIPT",
            "conditional_C_Schur": "PROVED_ONLY_IF_EXACT_LEAN_RECEIPT",
            "independent_antecedents": "OPEN",
            "riemann_hypothesis": "OPEN",
        },
        "priority_obstructions": [
            "Construct original projected forcing with all four signed histories and compact-inverse duality",
            "Retain the interior and full complement in original physical exterior reconstruction",
            "Attack the subexponential signed loss on the fixed divisor source, or exhibit a source-faithful countermodel",
        ],
    }
    validate_survival_source_ids(result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--comparison", type=Path, required=True)
    p.add_argument("--cuts", type=Path, required=True)
    p.add_argument("--formal", type=Path)
    p.add_argument("--d2", type=Path)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    sources = {"comparison": str(a.comparison), "cuts": str(a.cuts)}
    for key in ("formal", "d2"):
        value = getattr(a, key)
        if value:
            sources[key] = str(value)
    result = audit(load(a.comparison), load(a.cuts),
                   formal=load(a.formal) if a.formal else None,
                   d2=load(a.d2) if a.d2 else None)
    result["source_sha256"] = {key: hashfile(path) for key, path in sources.items()}
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"cut_statuses": {r["id"]: r["status"] for r in result["cuts"]},
                      "claim_cap": result["claim_cap"]}))


if __name__ == "__main__":
    main()
