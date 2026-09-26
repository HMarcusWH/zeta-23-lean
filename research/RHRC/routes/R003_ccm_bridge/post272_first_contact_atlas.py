#!/usr/bin/env python3
"""Post-#272 true-ground first-contact atlas.

Research/falsification tooling only.  Claim cap: EXPERIMENTAL_SIGNAL_ONLY.

Dumbassery correction locked into the implementation:
at an arithmetic threshold L=log(q), the entering q atom has q_basis(...)=0.
Therefore there is no value jump to discover.  The informative object is the
one-sided response immediately to the right of the threshold, compared with
(1) the smooth q-ablated continuation, (2) exact Lambda(q)=0 controls, and
(3) the already-scoped #249 planted-zero perturbations.

All sign-bearing spectral quantities below are Arb enclosures.  A parity ground
is called strict only when the two bottom eigenvalue balls are certified
disjoint.  No eigenvector is selected at an unresolved parity tie.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

import canonical_source_arb as ca
from post247_remainder_budget_ratio_scout import (
    _eigs,
    _q,
    _rec,
    _sym,
    arch_matrix,
    boundary_flat_parity_basis,
    exp_weight_sprime,
    orthonormalizer,
    planted_increment,
    prime_matrix,
    restrict,
)

SCHEMA = "POST272_TRUE_GROUND_FIRST_CONTACT_ATLAS_v1"
CLAIM_CAP = "EXPERIMENTAL_SIGNAL_ONLY"
DEFAULT_PREC = 256


def _zero_matrix(K: int) -> arb_mat:
    return arb_mat(2 * K + 1, 2 * K + 1)


def _fixed_background(L: arb, K: int, q: int) -> tuple[arb_mat, arb_mat]:
    """Return smooth q-ablated energy and the entering-q prime matrix.

    E_background uses primes <= q-1.  The physical right-hand energy is
    E_background - P_q, where P_q is exactly the q-only prime contribution.
    For Lambda(q)=0 controls P_q is identically zero.
    """
    Pprev = prime_matrix(L, K, q - 1) if q > 2 else _zero_matrix(K)
    Pthrough = prime_matrix(L, K, q)
    Pq = _sym(Pthrough - Pprev)
    G = exp_weight_sprime(acb(L / 2), acb(2), K)
    T = exp_weight_sprime(acb(-L / 2), acb(2), K)
    Arch = arch_matrix(L, K)
    background = _sym(G - Pprev - T - Arch)
    return background, Pq


def _matrix_exact_zero(M: arb_mat) -> bool:
    return all(M[i, j].is_zero() for i in range(M.nrows()) for j in range(M.ncols()))


def _matrix_contains_zero(M: arb_mat) -> bool:
    return all(M[i, j].contains(0) for i in range(M.nrows()) for j in range(M.ncols()))


def _matrix_abs_upper(M: arb_mat) -> float:
    out = 0.0
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            out = max(out, float(abs(M[i, j]).upper()))
    return out


def _parity_bottom(E: arb_mat, K: int, parity: str) -> tuple[dict, arb]:
    V = boundary_flat_parity_basis(K, parity)
    Linv = orthonormalizer(V)
    H = restrict(E, V, Linv)
    vals = _eigs(_sym(H))
    lam = vals[0]
    rec = {
        "dimension": H.nrows(),
        "lambda_min": _rec(lam),
        "lambda_2": _rec(vals[1]) if len(vals) > 1 else None,
        "ground_gap": _rec(vals[1] - vals[0]) if len(vals) > 1 else None,
    }
    return rec, lam


def _ground_summary(E: arb_mat, K: int) -> tuple[dict, arb | None]:
    even, le = _parity_bottom(E, K, "even")
    odd, lo = _parity_bottom(E, K, "odd")
    if le < lo:
        ordering = "EVEN_STRICT"
        gl = le
    elif lo < le:
        ordering = "ODD_STRICT"
        gl = lo
    else:
        ordering = "PARITY_GAP_UNRESOLVED"
        gl = None
    return {
        "ordering": ordering,
        "global_lambda_min": _rec(gl) if gl is not None else None,
        "even": even,
        "odd": odd,
    }, gl


def _delta_record(a: arb | None, b: arb | None) -> dict | None:
    if a is None or b is None:
        return None
    return _rec(a - b)


def _evaluate_point(L: arb, K: int, q: int, side: str, gamma: arb, delta: arb) -> dict:
    background, Pq = _fixed_background(L, K, q)
    canonical = background if side in {"left", "seam"} else _sym(background - Pq)
    ablated = background
    Don = planted_increment(L, K, gamma, arb(0))
    Doff = planted_increment(L, K, gamma, delta)

    can_j, can_g = _ground_summary(canonical, K)
    abl_j, abl_g = _ground_summary(ablated, K)
    on_j, on_g = _ground_summary(_sym(canonical - Don), K)
    off_j, off_g = _ground_summary(_sym(canonical - Doff), K)

    inc = {}
    atom_exact_zero = _matrix_exact_zero(Pq)
    atom_contains_zero = _matrix_contains_zero(Pq)
    for parity in ("even", "odd"):
        V = boundary_flat_parity_basis(K, parity)
        Linv = orthonormalizer(V)
        if atom_exact_zero:
            z = arb(0)
            inc[parity] = {
                "status": "EXACT_ZERO_OPERATOR",
                "lambda_min": _rec(z),
                "lambda_max": _rec(z),
            }
            continue
        if side == "seam" and atom_contains_zero:
            inc[parity] = {
                "status": "SEAM_ZERO_MULTIPLICITY_NOT_DIAGONALIZED",
                "lambda_min": None,
                "lambda_max": None,
            }
            continue
        try:
            vals = _eigs(_sym(-restrict(Pq, V, Linv)))
            inc[parity] = {
                "status": "CERTIFIED_EIGENVALUE_ENCLOSURES",
                "lambda_min": _rec(vals[0]),
                "lambda_max": _rec(vals[-1]),
            }
        except ValueError:
            inc[parity] = {
                "status": "EIGENVALUE_ISOLATION_UNRESOLVED",
                "lambda_min": None,
                "lambda_max": None,
            }

    return {
        "L": ca.ball_record(L),
        "side": side,
        "current_q_atom_exact_zero": atom_exact_zero,
        "current_q_atom_contains_zero_entrywise": atom_contains_zero,
        "current_q_atom_max_abs_upper": _matrix_abs_upper(Pq),
        "current_q_energy_increment": inc,
        "canonical": can_j,
        "current_q_ablated": abl_j,
        "planted_on_line": on_j,
        "planted_off_line": off_j,
        "global_canonical_minus_ablated": _delta_record(can_g, abl_g),
        "global_canonical_minus_planted_on_line": _delta_record(can_g, on_g),
        "global_canonical_minus_planted_off_line": _delta_record(can_g, off_g),
    }


def _certified_sign(rec: dict | None) -> int:
    if not rec:
        return 0
    if rec["certified_positive"]:
        return 1
    if rec["certified_negative"]:
        return -1
    return 0


def _case_record(spec: dict, powers: list[int], gamma: arb, delta: arb) -> dict:
    q, K = int(spec["q"]), int(spec["K"])
    L0 = arb(q).log()
    vm = ca.von_mangoldt(q)
    seam = _evaluate_point(L0, K, q, "seam", gamma, delta)
    scales = []
    for p in powers:
        h = _q(1, 2 ** p)
        left = _evaluate_point(L0 - h, K, q, "left", gamma, delta)
        right = _evaluate_point(L0 + h, K, q, "right", gamma, delta)
        scales.append({
            "offset_power": p,
            "h": ca.ball_record(h),
            "left": left,
            "right": right,
            "right_ground_response_sign": _certified_sign(
                right["global_canonical_minus_ablated"]
            ),
        })

    nonzero_signs = [s["right_ground_response_sign"] for s in scales if s["right_ground_response_sign"]]
    consistent = len(nonzero_signs) >= 2 and len(set(nonzero_signs)) == 1
    return {
        **spec,
        "von_mangoldt": ca.ball_record(vm),
        "von_mangoldt_is_zero": vm.is_zero(),
        "seam": seam,
        "scales": scales,
        "certified_consistent_right_ground_response": consistent,
        "claim_cap": CLAIM_CAP,
    }


def summarize(cases: list[dict]) -> dict:
    controls = [c for c in cases if c["kind"] == "ZERO_VON_MANGOLDT_CONTROL"]
    seams = [c for c in cases if c["kind"] == "VON_MANGOLDT_SEAM"]
    control_ok = all(
        c["von_mangoldt_is_zero"]
        and c["seam"]["current_q_atom_exact_zero"]
        and all(s["right"]["current_q_atom_exact_zero"] for s in c["scales"])
        for c in controls
    )
    seam_vm_ok = all(not c["von_mangoldt_is_zero"] for c in seams)
    responsive = [c for c in seams if c["certified_consistent_right_ground_response"]]

    if not control_ok or not seam_vm_ok:
        classification = "CONTROL_FAILURE"
    elif responsive:
        classification = "CERTIFIED_CURRENT_PRIME_GROUND_RESPONSE"
    else:
        classification = "NO_CERTIFIED_CURRENT_PRIME_GROUND_RESPONSE"

    return {
        "classification": classification,
        "control_count": len(controls),
        "seam_count": len(seams),
        "control_zero_atom_checks_pass": control_ok,
        "seam_von_mangoldt_checks_pass": seam_vm_ok,
        "responsive_case_count": len(responsive),
        "responsive_cases": [{"q": c["q"], "K": c["K"]} for c in responsive],
        "theorem_promotion": False,
        "rh_claim": False,
    }


def validate_fixture(fixture: dict) -> None:
    if fixture.get("schema_version") != SCHEMA:
        raise ValueError("unexpected fixture schema")
    if fixture.get("claim_cap") != CLAIM_CAP:
        raise ValueError("claim cap drift")
    if fixture.get("adaptive_search") is not False:
        raise ValueError("adaptive search is forbidden")
    powers = fixture.get("offset_powers")
    if powers != [8, 10, 12]:
        raise ValueError("offset schedule drift")
    for spec in fixture["primary_cases"] + fixture["replication_cases"]:
        q = int(spec["q"])
        for p in powers:
            h = 2.0 ** (-p)
            import math
            if not (math.log(q - 1) < math.log(q) - h < math.log(q)):
                raise ValueError(f"left offset leaves adjacent cell for q={q}, p={p}")
            if not (math.log(q) < math.log(q) + h < math.log(q + 1)):
                raise ValueError(f"right offset leaves adjacent cell for q={q}, p={p}")


def run(fixture: dict) -> dict:
    validate_fixture(fixture)
    ctx.prec = DEFAULT_PREC
    gamma = _q(*fixture["planted_gamma"])
    delta = _q(*fixture["planted_off_line_delta"])
    specs = fixture["primary_cases"] + fixture["replication_cases"]
    cases = [_case_record(s, fixture["offset_powers"], gamma, delta) for s in specs]
    return {
        "schema_version": SCHEMA,
        "claim_cap": CLAIM_CAP,
        "precision_bits": DEFAULT_PREC,
        "adaptive_search": False,
        "fixture": fixture,
        "cases": cases,
        "summary": summarize(cases),
        "nonclaims": [
            "This atlas is research evidence, not Lean theorem authority.",
            "At L=log(q) the entering atom vanishes; no value jump is claimed.",
            "A finite one-sided seam response is not a first-crossing theorem.",
            "Parity-gap overlap is reported as unresolved; no eigenvector is selected at a tie.",
            "The planted controls are not globally self-consistent alternate zeta functions.",
            "No asymptotic rate, global monotonicity, negative-root exclusion, or RH claim is made.",
            "RH remains OPEN."
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    fixture = json.loads(Path(args.input).read_text(encoding="utf-8"))
    out = run(fixture)
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(out["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
