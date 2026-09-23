#!/usr/bin/env python3
"""Scope, semantics and internal-consistency check of the frozen ratio scout.

Static QA over the checked-in fixture and backend: frozen grids, claim cap,
nonclaims, the aggregate summary recomputed from the rows, per-row slack
bounds, threshold brackets, and the published results note.  Nothing here is
theorem authority.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import post247_remainder_budget_ratio_scout as scout

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post247_remainder_budget_ratio_v1.json"
BACKEND = HERE / "post247_remainder_budget_ratio_scout.py"
NOTE = HERE / "POST247_REMAINDER_BUDGET_RATIO_SCOUT_2026_09_23.md"


def _frac(t: tuple[int, int]) -> str:
    return f"{t[0]}/{t[1]}"


def _doc_sci(x: float) -> str:
    """Format like the results note: 6.8e-83, 3.4e-2, 1.0e-57."""
    exp = math.floor(math.log10(abs(x)))
    mant = x / 10 ** exp
    if round(mant, 1) >= 10:
        mant /= 10
        exp += 1
    return f"{mant:.1f}e{exp}"


def _check_grids(d: dict) -> None:
    real = {(r["L"], r["K"]) for r in d["real"]}
    assert real == {(_frac(L), K) for L in scout.REAL_GRID_L for K in scout.REAL_GRID_K}
    assert len(d["real"]) == len(scout.REAL_GRID_L) * len(scout.REAL_GRID_K)
    planted = {(r["L"], r["K"], r["gamma"], r["delta"]) for r in d["planted"]}
    assert planted == {
        (_frac(L), K, _frac(g), _frac(dl))
        for L in scout.PLANT_GRID_L
        for K in scout.PLANT_GRID_K
        for g in scout.PLANT_GAMMAS
        for dl in scout.PLANT_DELTAS
    }
    thresholds = {(t["L"], t["K"], t["gamma"]) for t in d["detection_thresholds"]}
    assert thresholds == {
        (_frac(L), K, _frac(g))
        for L in scout.PLANT_GRID_L
        for K in scout.PLANT_GRID_K
        for g in scout.PLANT_GAMMAS
    }


def _check_rows(d: dict) -> None:
    for r in d["real"]:
        assert r["error"] is None, r
        assert r["all_signs_certified"], r
        assert scout.PREC_START <= r["prec_bits"] <= scout.PREC_MAX
        assert r["pole_equals_G_minus_T_max_abs_upper"] < 1e-60
        assert r["cross_parity_block_max_upper"] < 1e-60
        for p in ("even", "odd"):
            b = r[p]
            assert b["dim"] == r["K"] - 1
            lam = float(b["lambda_min"]["mid"])
            slack = float(b["slack_1_minus_ratio"]["mid"])
            a_min = float(b["A_eig_min"]["mid"])
            a_max = float(b["A_eig_max"]["mid"])
            # min E/A lies between lambda_min/A_max and lambda_min/A_min.
            assert lam / a_max * (1 - 1e-9) <= slack <= lam / a_min * (1 + 1e-9), (r["L"], r["K"], p)
            assert b["slack_1_minus_ratio"]["certified_positive"]
            assert b["slack_ratio_minus_1"]["certified_positive"]
    for r in d["planted"]:
        assert r["error"] is None, r
        assert r["all_signs_certified"], r
    for t in d["detection_thresholds"]:
        lo, hi = t["delta_certified_not_bad"], t["delta_certified_bad"]
        assert 0 < lo < hi
        assert (hi - lo) / hi < 1e-9, t
        assert t["on_line_double_pair_lambda_min"]["certified_positive"]


def _check_summary(d: dict) -> None:
    s = d["summary"]
    assert s == json.loads(json.dumps(scout.summarize(d["real"], d["planted"])))
    assert s["real_points"] == s["real_all_signs_certified"] == s["real_energy_certified_positive"] == 96
    assert s["A_positive_definite_everywhere"] is True
    assert s["B_positive_definite_everywhere"] is True
    split = s["bandwidth_split_at_first_zeta_ordinate"]
    assert split["points_below"] + split["points_above"] == 96
    assert split["max_lambda_max_E_below"] < split["min_lambda_max_E_above"]
    assert s["planted_on_line_certified_bad"] == 0
    assert s["planted_on_line_increment_rank_one_psd_per_parity"] is True
    assert s["planted_off_line_increment_signature_1_1_per_parity"] is True
    assert s["planted_off_line_certified_bad"] == 82


def _check_validation(d: dict) -> None:
    v = d["validation"]
    assert v["float_crosscheck"]["max_relative_entry_difference"] < 1e-12
    ef = v["explicit_formula_sign_check"]
    assert ef["nzeros"] == 300
    assert ef["mean_abs_error_planted_sign_convention"] * 5 < ef["mean_abs_error_flipped_sign"]


def _check_semantics(d: dict) -> None:
    assert d["schema_version"] == scout.SCHEMA == "POST247_REMAINDER_BUDGET_RATIO_SCOUT_v1"
    assert d["claim_cap"] == scout.CLAIM_CAP == "EXPERIMENTAL_SIGNAL_ONLY"
    assert "RH remains OPEN." in d["nonclaims"]
    text = BACKEND.read_text(encoding="utf-8")
    for forbidden in ("optimize.", "minimize(", "differential_evolution", "np.random", "import random"):
        assert forbidden not in text, forbidden
    assert "sort(key=lambda a: a.mid())" in text  # exact ordering, not float keys
    note = NOTE.read_text(encoding="utf-8")
    for claim in ("proves RH", "RH is proved", "RH proved", "RH is true", "RH_PROVED"):
        assert claim not in text, claim
        assert claim not in note, claim
    for overclaim in (
        "super-exponentially small slack",
        "collapses super-exponentially",
        "switches on exactly at the first zeta zero",
        "negative eigenvalue scales as `δ²`",
        "smallest `δ` certified bad",
        "Only the prime-free regime has a real margin",
        "PNT-strength or zero-density-strength) cannot supply this",
    ):
        assert overclaim not in note, overclaim
    for required in (
        "no asymptotic decay law is claimed",
        "nominal resolution scale",
        "not a hard Fourier cutoff theorem",
        "leading-order `O(δ²)` behavior",
        "certified sign-change brackets",
        "not globally minimal deltas",
        "not a globally self-consistent alternate zeta function",
        "does not rule out PNT-strength",
    ):
        assert required in note, required
    assert "not a global minimum certificate" in text


def _check_note(d: dict) -> None:
    note = NOTE.read_text(encoding="utf-8")
    for token in ("EXPERIMENTAL SIGNAL", "RH remains OPEN", "Nonclaims", scout.SCHEMA):
        assert token in note, token
    slack = d["summary"]["min_slack_by_L_then_K"]
    for L in ("1/2", "3/4", "1/1", "3/2", "2/1", "3/1", "4/1", "6/1", "8/1"):
        for K in ("3", "6", "12", "20"):
            assert _doc_sci(slack[L][K]) in note, (L, K, _doc_sci(slack[L][K]))
    for t in d["detection_thresholds"]:
        assert _doc_sci(t["delta_certified_bad"]) in note, t


def main() -> int:
    d = json.loads(FIXTURE.read_text(encoding="utf-8"))
    _check_semantics(d)
    _check_grids(d)
    _check_rows(d)
    _check_summary(d)
    _check_validation(d)
    _check_note(d)
    print("POST247 REMAINDER/BUDGET RATIO SCOUT SCOPE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
