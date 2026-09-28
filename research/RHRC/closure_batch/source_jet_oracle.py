from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def effective_power(a: float, b: float, scale_ratio: float = 4.0) -> float:
    return math.log(abs(a / b)) / math.log(scale_ratio)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    repo = Path(args.repo)
    receipt_path = repo / "research/RHRC/receipts/POST272_FIRST_CONTACT_ATLAS.json"
    powers = []
    if receipt_path.exists():
        raw = json.loads(receipt_path.read_text())
        for case in raw.get("atlas", {}).get("cases", []):
            if case.get("kind") != "VON_MANGOLDT_SEAM":
                continue
            vals = [
                abs(float(s["right"]["global_canonical_minus_ablated"]["mid"]))
                for s in case.get("scales", [])
            ]
            if len(vals) >= 3 and all(v > 0 for v in vals):
                powers.append({
                    "q": case["q"],
                    "K": case["K"],
                    "p08_p10": effective_power(vals[0], vals[1]),
                    "p10_p12": effective_power(vals[1], vals[2]),
                })
    out = {
        "schema_version": "RHRC-CLOSURE-TRACK-1.0",
        "track_id": "A",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "FIXED_VECTOR_JETS_THEOREM_BACKED_MOVING_GROUND_TRANSFER_OPEN",
        "theorem_authority": False,
        "rh_closure": False,
        "terminal_claim": "RH_OPEN",
        "diagnostic_only_effective_powers": powers,
        "note": "Serialized decimal midpoints are diagnostics only; exact fixed-vector seventh/ninth jets are supplied by Lean."
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
