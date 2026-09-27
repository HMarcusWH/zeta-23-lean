from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import numpy as np

FROZEN_L = (2.0, 3.0, 4.0)
FROZEN_K = (3, 4, 6, 8)
FROZEN_Z = (
    0.25j,
    0.5j,
    0.5 + 0.25j,
    1.0 + 0.5j,
    -0.5 + 0.75j,
)


def encode(z: complex) -> dict[str, float]:
    return {"re": float(z.real), "im": float(z.imag)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    r003 = repo / "research" / "RHRC" / "routes" / "R003_ccm_bridge"
    sys.path.insert(0, str(r003))
    from canonical_source_numeric import canonical_source_matrix_L

    rows = []
    normalized: dict[tuple[float, int, complex], complex] = {}
    normalizer_failures = []
    for L in FROZEN_L:
        for K in FROZEN_K:
            M = np.asarray(canonical_source_matrix_L(L, K), dtype=np.complex128)
            M = 0.5 * (M + M.T)
            normalizer = complex(np.linalg.det(M))
            if abs(normalizer) < 1e-280:
                normalizer_failures.append({"L": L, "K": K, "abs": abs(normalizer)})
                continue
            vals = []
            I = np.eye(M.shape[0], dtype=np.complex128)
            for z in FROZEN_Z:
                raw = complex(np.linalg.det(M - z * I))
                norm = raw / normalizer
                normalized[(L, K, z)] = norm
                vals.append({"z": encode(z), "raw": encode(raw), "normalized": encode(norm)})
            rows.append({
                "L": L,
                "K": K,
                "normalizer": encode(normalizer),
                "normalizer_abs": abs(normalizer),
                "values": vals,
            })

    deltas = []
    for L in FROZEN_L:
        for ka, kb in zip(FROZEN_K, FROZEN_K[1:]):
            for z in FROZEN_Z:
                a = normalized.get((L, ka, z))
                b = normalized.get((L, kb, z))
                if a is not None and b is not None:
                    deltas.append({
                        "L": L,
                        "K_from": ka,
                        "K_to": kb,
                        "z": encode(z),
                        "abs_delta": abs(b - a),
                    })

    out = {
        "schema_version": "RHRC-CLOSURE-CANONICAL-CHARACTERISTIC-SCOUT-1.0",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "adaptive_search": False,
        "scope": {
            "L": list(FROZEN_L),
            "K": list(FROZEN_K),
            "z": [encode(z) for z in FROZEN_Z],
        },
        "normalizer_failures": normalizer_failures,
        "rows": rows,
        "successive_K_deltas": deltas,
        "max_successive_K_delta": max((d["abs_delta"] for d in deltas), default=None),
        "classification": (
            "NORMALIZER_FAILURE_ON_FROZEN_SCOPE"
            if normalizer_failures
            else "FINITE_COMPLEX_CHARACTERISTIC_SCOUT_NO_LIMIT_THEOREM"
        ),
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "Finite complex-grid stability is not local-uniform convergence.",
            "No limiting function is identified with Xi.",
            "Float64 determinants are research diagnostics, not interval certificates.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
