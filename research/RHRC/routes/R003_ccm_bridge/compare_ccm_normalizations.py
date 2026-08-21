"""R003 external normalization autopsy (REFERENCE AUDIT ONLY).

Compares the fork-owned executable CCM model (which mirrors `Zeta23.CCM`) against
the pinned cutoff-free CCM/CvS closed-form implementation adapted from Groskin's
finite Guinand--Weil verification package.

This script has no theorem authority.  Its job is to prevent the next Lean proof
from targeting the wrong normalization.

Expected convention map, to be TESTED rather than assumed:

    Q_inf = M + 2*cCorrection(L)*I

where `M` is the fork-owned CCM matrix and `Q_inf` is the cutoff-free
Connes--van Suijlekom / CCM Galerkin matrix.  Combined with the pre-existing R003
finite explicit-formula diagnostic

    WeilGram = 2*M + 4*cCorrection(L)*I,

this predicts that the inherited `WeilGram` convention is `2*Q_inf`.

No RH evidence and no theorem promotion follows from this numerical/source audit.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
RHRC = HERE.parents[1]
R004 = RHRC / "routes" / "R004_prolate_v2"
EXT = RHRC / "external" / "connes_cvs"
sys.path.insert(0, str(R004))
sys.path.insert(0, str(EXT))

from run_commutator_gauntlet_v2 import (  # noqa: E402
    alpha_L as ours_alpha_L,
    arch_component as ours_arch_component,
    beta_L as ours_beta_L,
    c_correction as ours_c_correction,
    gamma_L as ours_gamma_L,
    pole_component as ours_pole_component,
    prime_component as ours_prime_component,
)
from closed_form_ccm_reference import CutoffFreeCCM  # noqa: E402


DEFAULT_C = [4, 9, 13, 25, 29, 100]
DEFAULT_INDICES = [-2, -1, 0, 1, 2]


def ours_entry(n: int, m: int, L: float) -> float:
    return (
        ours_pole_component(n, m, L)
        - ours_arch_component(n, m, L)
        - ours_prime_component(n, m, L)
    )


def run_case(c: int, indices: list[int]) -> dict:
    ref = CutoffFreeCCM(c, max(abs(k) for k in indices))
    L = float(ref.L)
    cc = float(ours_c_correction(L))

    entry_rows = []
    max_offdiag_abs = 0.0
    diag_shift_values = []
    max_shift_residual = 0.0
    max_pole_residual = 0.0

    for n in indices:
        for m in indices:
            ours = float(ours_entry(n, m, L))
            qinf = float(ref.entry(n, m))
            delta = qinf - ours
            predicted = 2.0 * cc if n == m else 0.0
            residual = delta - predicted
            if n == m:
                diag_shift_values.append(delta)
            else:
                max_offdiag_abs = max(max_offdiag_abs, abs(delta))
            max_shift_residual = max(max_shift_residual, abs(residual))
            max_pole_residual = max(
                max_pole_residual,
                abs(float(ref.pole_entry(n, m)) - ours_pole_component(n, m, L)),
            )
            entry_rows.append(
                {
                    "n": n,
                    "m": m,
                    "ours_M": ours,
                    "reference_Q_inf": qinf,
                    "Q_inf_minus_M": delta,
                    "predicted_shift": predicted,
                    "residual": residual,
                }
            )

    primitive_rows = []
    max_alpha_residual = 0.0
    max_beta_residual = 0.0
    max_gamma_shift_residual = 0.0
    for n in indices:
        alpha_res = float(ref.alpha_L(n)) - float(ours_alpha_L(n, L))
        beta_res = float(ref.beta_L(n)) - float(ours_beta_L(n, L))
        # Source-formula prediction: gamma_ref = gamma_ours - cCorrection(L).
        gamma_res = (
            float(ref.gamma_L(n))
            - float(ours_gamma_L(n, L))
            + cc
        )
        max_alpha_residual = max(max_alpha_residual, abs(alpha_res))
        max_beta_residual = max(max_beta_residual, abs(beta_res))
        max_gamma_shift_residual = max(max_gamma_shift_residual, abs(gamma_res))
        primitive_rows.append(
            {
                "n": n,
                "alpha_reference_minus_ours": alpha_res,
                "beta_reference_minus_ours": beta_res,
                "gamma_reference_minus_ours_plus_cCorrection": gamma_res,
            }
        )

    diag_spread = max(diag_shift_values) - min(diag_shift_values)
    return {
        "c": c,
        "lambda": math.sqrt(c),
        "L": L,
        "cCorrection": cc,
        "predicted_Q_inf_diagonal_shift": 2.0 * cc,
        "diag_shift_mean": sum(diag_shift_values) / len(diag_shift_values),
        "diag_shift_spread": diag_spread,
        "max_offdiag_abs_Q_inf_minus_M": max_offdiag_abs,
        "max_entry_residual_after_shift": max_shift_residual,
        "max_pole_residual": max_pole_residual,
        "max_alpha_residual": max_alpha_residual,
        "max_beta_residual": max_beta_residual,
        "max_gamma_shift_residual": max_gamma_shift_residual,
        "entries": entry_rows,
        "primitives": primitive_rows,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--c", nargs="+", type=int, default=DEFAULT_C)
    ap.add_argument("--indices", nargs="+", type=int, default=DEFAULT_INDICES)
    ap.add_argument(
        "--tolerance",
        type=float,
        default=2e-9,
        help="Float/SciPy-vs-mpmath comparison tolerance; this is an audit, not a proof.",
    )
    ap.add_argument(
        "--output",
        type=Path,
        default=HERE / "CCM_NORMALIZATION_LOCK_v1.json",
    )
    args = ap.parse_args()

    if not args.indices:
        raise SystemExit("need at least one index")
    mp.mp.dps = 60

    cases = [run_case(c, args.indices) for c in args.c]
    tol = args.tolerance
    metrics = {
        "max_entry_residual_after_shift": max(c["max_entry_residual_after_shift"] for c in cases),
        "max_offdiag_abs_Q_inf_minus_M": max(c["max_offdiag_abs_Q_inf_minus_M"] for c in cases),
        "max_diag_shift_spread": max(c["diag_shift_spread"] for c in cases),
        "max_pole_residual": max(c["max_pole_residual"] for c in cases),
        "max_alpha_residual": max(c["max_alpha_residual"] for c in cases),
        "max_beta_residual": max(c["max_beta_residual"] for c in cases),
        "max_gamma_shift_residual": max(c["max_gamma_shift_residual"] for c in cases),
    }
    passed = all(v <= tol for v in metrics.values())

    payload = {
        "schema_version": "CCM_NORMALIZATION_LOCK_v1",
        "status": "PASS" if passed else "FAIL",
        "phase": "DISCOVERY_AUDIT",
        "claim_cap": "FINITE_NUMERICAL_AND_SOURCE_FORMULA_AUDIT_ONLY",
        "comparison": {
            "fork_object": "M = Zeta23.CCM.entry / R004 executable mirror",
            "reference_object": "Q_inf = cutoff-free finite CvS/CCM Galerkin matrix",
            "tested_relation": "Q_inf = M + 2*cCorrection(L)*I",
            "source_formula_primitive_relation": [
                "alpha_reference = alpha_ours",
                "beta_reference = beta_ours",
                "gamma_reference = gamma_ours - cCorrection(L)",
                "pole_reference = pole_ours"
            ],
            "preexisting_R003_diagnostic": "WeilGram = 2*M + 4*cCorrection(L)*I",
            "implied_normalization_if_both_relations_hold": "WeilGram = 2*Q_inf"
        },
        "configuration": {
            "c_values": args.c,
            "indices": args.indices,
            "mp_dps": mp.mp.dps,
            "tolerance": tol,
        },
        "metrics": metrics,
        "cases": cases,
        "nonclaims": [
            "No RH evidence or proof.",
            "No external Python result promotes an RHRC theorem claim.",
            "The exact bridge still requires a Lean proof in the fork normalization.",
            "The pre-existing WeilGram relation remains a finite diagnostic until formalized."
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": payload["status"], "metrics": metrics}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
