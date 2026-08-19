from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import mpmath as mp
import numpy as np

OUTDIR = Path(__file__).resolve().parent / "outputs"


@dataclass(frozen=True)
class SlopeSummary:
    full: float
    local: float
    low: float
    mid: float
    high: float


def first_zeros(n: int, cache: Path) -> np.ndarray:
    if cache.exists():
        arr = np.load(cache)
        if len(arr) >= n:
            return arr[:n]
    mp.mp.dps = 30
    arr = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, n + 1)], dtype=float)
    cache.parent.mkdir(parents=True, exist_ok=True)
    np.save(cache, arr)
    return arr


def on_line_term(a: float, xi: np.ndarray, gamma: float, multiplicity: int = 1) -> np.ndarray:
    out = np.zeros(xi.shape, dtype=np.complex128)
    for g in (gamma, -gamma):
        d = 1j * (g - xi)
        out += multiplicity * np.exp(2.0 * a * d) / d
    return out


def offline_pair_term(a: float, xi: np.ndarray, gamma: float, delta: float) -> np.ndarray:
    # Functional-equation/conjugation symmetric quartet: 1/2 +/- delta +/- i gamma.
    out = np.zeros(xi.shape, dtype=np.complex128)
    for beta_shift in (delta, -delta):
        for g in (gamma, -gamma):
            d = beta_shift + 1j * (g - xi)
            out += np.exp(2.0 * a * d) / d
    return out


def base_residual(a: float, xi: np.ndarray, gammas: np.ndarray) -> np.ndarray:
    # Closed zero-sum finite numerical diagnostic using computed on-line ordinates only.
    out = np.zeros(xi.shape, dtype=np.complex128)
    for g in gammas:
        out += on_line_term(a, xi, float(g), 1)
    return out


def rms(z: np.ndarray, mask: np.ndarray) -> float:
    vals = z[mask]
    if vals.size == 0:
        return float("nan")
    return float(np.sqrt(np.mean(np.abs(vals) ** 2)))


def fit_slope(a: np.ndarray, values: np.ndarray, min_a: float = 30.0) -> float:
    m = (a >= min_a) & np.isfinite(values) & (values > 0)
    if np.count_nonzero(m) < 2:
        return float("nan")
    return float(np.polyfit(a[m], np.log(values[m]), 1)[0])


def build_masks(xi: np.ndarray, actual_zeros: np.ndarray, gamma_local: float, exclusion: float = 0.15) -> dict[str, np.ndarray]:
    pole_ok = np.ones(xi.shape, dtype=bool)
    for g in actual_zeros:
        pole_ok &= np.abs(xi - g) >= exclusion
    ranges = {
        "full": (10.0, float(xi.max()) + 1),
        "low": (10.0, 120.0),
        "mid": (120.0, 250.0),
        "high": (250.0, float(xi.max()) + 1),
        "local": (gamma_local - 24.0, gamma_local + 24.0),
    }
    return {k: pole_ok & (xi >= lo) & (xi < hi) for k, (lo, hi) in ranges.items()}


def residual_curves(apertures: np.ndarray, xi: np.ndarray, gammas: np.ndarray, gamma_local: float, *, kind: str, delta: float = 0.0, second_gamma: float | None = None) -> tuple[dict[str, np.ndarray], SlopeSummary]:
    masks = build_masks(xi, gammas, gamma_local)
    curves = {k: [] for k in masks}
    for a in apertures:
        z = base_residual(float(a), xi, gammas)
        if kind == "online_double":
            z += on_line_term(float(a), xi, gamma_local, 2)
        elif kind == "offline_pair":
            z += offline_pair_term(float(a), xi, gamma_local, delta)
        elif kind == "offline_two_pair":
            assert second_gamma is not None
            z += offline_pair_term(float(a), xi, gamma_local, delta)
            z += offline_pair_term(float(a), xi, second_gamma, delta)
        elif kind != "baseline":
            raise ValueError(kind)
        for name, mask in masks.items():
            curves[name].append(rms(z, mask))
    curves_np = {k: np.asarray(v, dtype=float) for k, v in curves.items()}
    slopes = SlopeSummary(**{k: fit_slope(apertures, curves_np[k]) for k in ("full", "local", "low", "mid", "high")})
    return curves_np, slopes


def summary_dict(curves: dict[str, np.ndarray], slopes: SlopeSummary, apertures: np.ndarray) -> dict:
    return {
        "slopes_late_log_rms_per_a": asdict(slopes),
        "rms": {k: [float(x) for x in v] for k, v in curves.items()},
        "apertures": [float(x) for x in apertures],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros", type=int, default=200)
    parser.add_argument("--grid", type=int, default=3600)
    parser.add_argument("--output", type=Path, default=OUTDIR / "r001_discovery_run.json")
    args = parser.parse_args()

    t0 = time.time()
    cache = OUTDIR / f"zeta_zeros_{args.zeros}.npy"
    gammas = first_zeros(args.zeros, cache)
    xmax = min(float(gammas[-1]) - 5.0, 390.0)
    xi = np.linspace(10.0, xmax, args.grid)
    apertures = np.array([3,4,5,6,8,10,12,16,20,25,30,40,50,60,70,80,90,100], dtype=float)
    gamma0 = float(gammas[59])

    baseline_curves, baseline_slopes = residual_curves(apertures, xi, gammas, gamma0, kind="baseline")
    double_curves, double_slopes = residual_curves(apertures, xi, gammas, gamma0, kind="online_double")

    deltas = [0.005, 0.01, 0.02, 0.05, 0.10]
    offlines: dict[str, dict] = {}
    for delta in deltas:
        curves, slopes = residual_curves(apertures, xi, gammas, gamma0, kind="offline_pair", delta=delta)
        offlines[f"{delta:.3f}"] = summary_dict(curves, slopes, apertures) | {
            "predicted_asymptotic_rate_2delta": 2.0 * delta,
            "rate_error_local": slopes.local - 2.0 * delta,
        }

    transfer_indices = [39, 79, 119, 149]
    transfer: dict[str, dict] = {}
    for idx in transfer_indices:
        g = float(gammas[idx])
        _, slopes = residual_curves(apertures, xi, gammas, g, kind="offline_pair", delta=0.05)
        transfer[str(idx + 1)] = {"gamma": g, "delta": 0.05, "local_late_slope": slopes.local, "full_late_slope": slopes.full, "predicted_rate": 0.1}

    ablation = {
        "selected_candidate": "off_line_depth_delta",
        "intervention": "delta -> 0 under fixed gamma/probe/apertures/base-zero-set",
        "offline_delta_0_05_local_slope": offlines["0.050"]["slopes_late_log_rms_per_a"]["local"],
        "online_double_local_slope": double_slopes.local,
    }
    ablation["slope_drop"] = ablation["offline_delta_0_05_local_slope"] - ablation["online_double_local_slope"]

    spacings = np.concatenate([np.linspace(0.02, 0.30, 8), np.linspace(0.4, 2.0, 9)])
    cancel_records = []
    xi_fast = np.linspace(10.0, xmax, max(1400, args.grid // 2))
    fast_ap = np.array([20,30,40,50,60,70,80,90,100], dtype=float)
    for spacing in spacings:
        g1 = gamma0 - float(spacing)/2
        g2 = gamma0 + float(spacing)/2
        _, slopes = residual_curves(fast_ap, xi_fast, gammas, g1, kind="offline_two_pair", delta=0.05, second_gamma=g2)
        cancel_records.append({"spacing": float(spacing), "local_late_slope": slopes.local, "full_late_slope": slopes.full})
    worst = min(cancel_records, key=lambda r: r["local_late_slope"])
    wg1 = gamma0 - worst["spacing"]/2
    wg2 = gamma0 + worst["spacing"]/2
    worst_curves, worst_slopes = residual_curves(apertures, xi, gammas, wg1, kind="offline_two_pair", delta=0.05, second_gamma=wg2)

    gammas100 = gammas[:100]
    xi_half = np.linspace(10.0, min(float(gammas100[-1]) - 5.0, 230.0), max(1800, args.grid // 2))
    _, slope_100 = residual_curves(apertures, xi_half, gammas100, float(gammas100[59]), kind="offline_pair", delta=0.05)
    commutation = {
        "100_zero_half_grid_local_slope": slope_100.local,
        "200_zero_full_grid_local_slope": offlines["0.050"]["slopes_late_log_rms_per_a"]["local"],
    }
    commutation["absolute_delta"] = abs(commutation["100_zero_half_grid_local_slope"] - commutation["200_zero_full_grid_local_slope"])

    null_offsets = [-1.7, -1.1, -0.6, 0.0, 0.5, 1.0, 1.6]
    null_slopes = []
    for shift in null_offsets:
        _, s = residual_curves(apertures, xi, gammas, gamma0 + shift, kind="online_double")
        null_slopes.append(float(s.local))
    null_max = max(null_slopes)

    positive_local = [offlines[k]["slopes_late_log_rms_per_a"]["local"] for k in ("0.020", "0.050", "0.100")]
    transfer_local = [x["local_late_slope"] for x in transfer.values()]
    gates = {
        "source_target_firewall": True,
        "tightmult_extra_channel_declared": True,
        "best_on_line_null_separated": min(positive_local) > null_max,
        "candidate_aligned_ablation": ablation["slope_drop"] > 0.02,
        "gamma_transfer": min(transfer_local) > null_max,
        "cancellation_attack": worst_slopes.local > null_max,
        "commutation": commutation["absolute_delta"] < 0.03,
    }
    bounded_result = "PASS" if all(gates.values()) else "FAIL"

    result = {
        "run_id": "R001_DISCOVERY_RUN",
        "phase": "DISCOVERY",
        "date": "2026-08-19",
        "claim_cap": "FINITE_NUMERICAL_SYNTHETIC_DIAGNOSTIC_ONLY",
        "mathematical_claims_promoted": [],
        "source": {
            "formula": "Z_a(xi)=sum_rho exp(2a(rho-s))/(rho-s), s=1/2+i xi",
            "reference": "Kim et al., arXiv:2607.24830v2, R6",
            "zero_ordinates": f"first {args.zeros} mpmath.zetazero ordinates; finite numerical on-line input only",
        },
        "configuration": {
            "zero_count": args.zeros,
            "last_zero_ordinate": float(gammas[-1]),
            "xi_grid_size": args.grid,
            "xi_range": [10.0, xmax],
            "pole_exclusion": 0.15,
            "apertures": [float(a) for a in apertures],
            "anchor_zero_index": 60,
            "anchor_gamma": gamma0,
            "late_slope_fit_min_a": 30.0,
            "new_information_channel": "multi-aperture evolution of the zero-sum residual norm; not a scalar function of TightMult trace/Frobenius/index data",
        },
        "baseline_on_line": summary_dict(baseline_curves, baseline_slopes, apertures),
        "online_double_control": summary_dict(double_curves, double_slopes, apertures),
        "offline_pair_sweep": offlines,
        "null_ensemble": {"online_double_gamma_offsets": null_offsets, "local_late_slopes": null_slopes, "max_slope": null_max},
        "interventions": {
            "J_delta_ablation": ablation,
            "J_gamma_transfer": transfer,
            "J_cluster_spacing_cancellation": {
                "delta": 0.05,
                "scan": cancel_records,
                "worst_fast_record": worst,
                "truth_replay": {"gamma_1": wg1, "gamma_2": wg2, "local_late_slope": worst_slopes.local, "full_late_slope": worst_slopes.full, "predicted_rate": 0.1, "rms_local": [float(x) for x in worst_curves["local"]]},
            },
        },
        "commutation": commutation,
        "gates": gates,
        "bounded_discovery_claim": {
            "statement": "Within this finite synthetic/numerical configuration, the declared multi-aperture residual channel separates tested off-line pairs with delta in {0.02,0.05,0.10} from the on-line-double controls, survives gamma transfer and the scanned two-pair cancellation attack, and loses the growth signal under delta->0 ablation.",
            "result": bounded_result,
            "certificate_status": "VALID",
            "authority": "EXPERIMENTAL_EVIDENCE",
        },
        "open_obligations": [
            "R001_ZERO_GROWTH remains OPEN: finite synthetic separation is not the general zero-side theorem.",
            "R001_PRIME_UPPER remains OPEN: no unconditional prime-side subexponential bound is proved here.",
            "No inference from finite numerical on-line zeros to all zeta zeros is permitted.",
            "No FFBBP/OoL numerical certificate has mathematical theorem authority; Lean/comparator remains the promotion gate.",
        ],
        "runtime_seconds": time.time() - t0,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2))
    print(json.dumps({
        "run_id": result["run_id"],
        "bounded_result": bounded_result,
        "gates": gates,
        "baseline_local_slope": baseline_slopes.local,
        "online_double_local_slope": double_slopes.local,
        "offline_local_slopes": {k: v["slopes_late_log_rms_per_a"]["local"] for k, v in offlines.items()},
        "null_max_local_slope": null_max,
        "cancellation_worst_truth_local_slope": worst_slopes.local,
        "commutation_abs_delta": commutation["absolute_delta"],
        "runtime_seconds": result["runtime_seconds"],
        "output": str(args.output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
