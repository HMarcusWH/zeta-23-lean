from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from flint import arb, ctx, fmpq

FROZEN_L_NUM = 1
FROZEN_L_DEN = 512
FROZEN_K = (0, 1, 3, 6)
PREC = 256


def rec(x: arb) -> dict:
    return {
        "mid": x.mid().str(40, radius=False),
        "rad": x.rad().str(20, radius=False),
        "lower": x.lower().str(50, radius=False),
        "upper": x.upper().str(50, radius=False),
        "rel_accuracy_bits": int(x.rel_accuracy_bits()),
        "certified_positive": bool(x > 0),
        "certified_negative": bool(x < 0),
        "contains_zero": bool(x.contains(0)),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    r003 = repo / "research" / "RHRC" / "routes" / "R003_ccm_bridge"
    sys.path.insert(0, str(r003))
    from post247_remainder_budget_ratio_scout import channels, _eigs, _sym

    ctx.prec = PREC
    L = arb(fmpq(FROZEN_L_NUM, FROZEN_L_DEN))
    lower = arb(2) - L - arb(fmpq(2, 9)) * L ** 3
    rows = []
    for K in FROZEN_K:
        ch = channels(L, K)
        E = _sym(ch["A"] - ch["B"])
        vals = _eigs(E)
        rows.append({
            "K": K,
            "lambda_min": rec(vals[0]),
            "lambda_max": rec(vals[-1]),
            "analytic_candidate_lower": rec(lower),
            "prime_cutoff_Q": ch["Q"],
        })

    all_positive = all(r["lambda_min"]["certified_positive"] for r in rows)
    out = {
        "schema_version": "RHRC-CLOSURE-SMALL-APERTURE-ARB-AUDIT-1.1",
        "claim_cap": "RIGOROUS_BOUNDED_ARB_RESEARCH",
        "adaptive_search": False,
        "precision_bits": PREC,
        "L": f"{FROZEN_L_NUM}/{FROZEN_L_DEN}",
        "K": list(FROZEN_K),
        "rows": rows,
        "classification": (
            "FULL_SPACE_POSITIVE_ON_FROZEN_SMALL_APERTURE_SCOPE"
            if all_positive else "SMALL_APERTURE_SIGN_UNRESOLVED_OR_NEGATIVE"
        ),
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "This finite K audit does not prove the all-K source-contraction, arch, or pole bounds.",
            "Rigorous bounded Arb evidence is not Lean theorem authority.",
            "The boundary-flat/full-space analytic base remains open until its premises are Lean-proved.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
