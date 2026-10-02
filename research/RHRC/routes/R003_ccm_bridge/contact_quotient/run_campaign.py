from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_vs_synthetic import compare
from dual_scout import scout
from feature_closure_audit import audit_feature_closure
from countermodel_controls import replay_controls
from source_authority_lint import lint
from staged_rank_audit import staged_audit


def dump(obj: dict, path: Path) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    lint()
    canonical = staged_audit(canonical=True)
    synthetic = staged_audit(canonical=False)
    comparison = compare()
    dual = scout()
    feature_closure = audit_feature_closure()
    countermodels = replay_controls()

    dump(canonical, out / "CANONICAL_STAGED_RANK.json")
    dump(synthetic, out / "SYNTHETIC_STAGED_RANK.json")
    dump(comparison, out / "CANONICAL_VS_SYNTHETIC.json")
    dump(dual, out / "QUOTIENT_DUAL_SCOUT.json")
    dump(feature_closure, out / "FEATURE_CLOSURE_AUDIT.json")
    dump(countermodels, out / "COUNTERMODEL_CONTROLS.json")

    receipt = {
        "schema_version": "RHRC-CONTACT-QUOTIENT-CAMPAIGN-1.0",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "LIFTED_RELATION_SPACE_MATERIALIZED__POINTWISE_CANONICAL_EQUALITY_RIGIDITY_OPEN",
        "canonical_final_rank": canonical["stages"][-1]["rank"],
        "canonical_final_nullity": canonical["stages"][-1]["nullity"],
        "synthetic_final_rank": synthetic["stages"][-1]["rank"],
        "synthetic_final_nullity": synthetic["stages"][-1]["nullity"],
        "diagnostic_dual_source_derived": False,
        "paper_saturation_used_in_rank": False,
        "feature_closure_status": feature_closure["status"],
        "global_basis_completeness_claimed": feature_closure["global_basis_completeness"],
        "countermodel_controls_status": countermodels["status"],
        "pair_d_simultaneous_badness_replayed": countermodels["pair_d_c1"]["simultaneous_badness"],
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
    }
    dump(receipt, out / "CAMPAIGN_RECEIPT.json")
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
