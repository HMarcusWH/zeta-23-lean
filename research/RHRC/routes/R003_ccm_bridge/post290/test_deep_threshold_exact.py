"""Adversarial exact tests of both-parity predecessor and empty-space scope."""
from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path
import random

from deep_threshold_exact import select_bottom_threshold
from pole_neutral_exact import require_checks


def run() -> dict:
    rng = random.Random(290123)
    rows = []
    branch_counts = {"STRICT_EVEN": 0, "STRICT_ODD": 0, "TIE": 0}
    empty = 0
    for count in range(1, 65):
        depth = F(3, 2)
        for repeat in range(3):
            even = sorted([F(rng.randint(-180, 90), 90) for _ in range(count - 1)] + [-depth], reverse=True)
            odd = sorted([F(rng.randint(-180, 90), 90) for _ in range(count - 1)] + [-depth], reverse=True)
            if repeat == 2:
                odd = even.copy()
            result = select_bottom_threshold(even, odd, depth)
            eta, gap, lam = (result[k] for k in ("eta", "gap", "lambda"))
            checks = {
                "threshold_window": depth / 3 < eta < depth / 2,
                "all_global_bottoms_avoided": all(abs(v + eta) >= gap for v in result["global_bottoms"]),
                "selected_depth": lam <= -eta - gap,
                "inverse_constant": result["inverse_budget"] == 1 / (2 * gap),
            }
            predecessor = result["predecessor"]
            if predecessor is None:
                empty += 1
                checks["first_nonempty_handled_without_bottom"] = result["selected_K"] == 3
            else:
                checks["both_predecessors_above_threshold"] = all(v >= -eta + gap for v in predecessor.values())
                checks["both_predecessors_shifted_coercive"] = all(v - lam >= 2 * gap for v in predecessor.values())
            require_checks(checks)
            branch_counts[result["branch"]] += 1
            rows.append({"Kd": result["Kd"], "selected_K": result["selected_K"],
                         "eta": str(eta), "gap": str(gap), "branch": result["branch"],
                         "empty_predecessor": predecessor is None, "checks": checks})
    require_checks({"all_three_branches": all(v > 0 for v in branch_counts.values()),
                    "empty_predecessor_exercised": empty > 0})
    return {"status": "PASS", "authority": "EXACT_FINITE_CONTROL", "RH_status": "OPEN",
            "is_actual_zeta": False, "Lean_authority": False,
            "scope": "192 rational nested-bottom controls with both parities and explicit empty predecessor",
            "branch_counts": branch_counts, "empty_predecessor_cases": empty,
            "assertion_count": sum(len(r["checks"]) for r in rows) + 2, "rows": rows}


if __name__ == "__main__":
    report = run()
    out = Path(__file__).parent / "evidence" / "deep_threshold_exact.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}))
