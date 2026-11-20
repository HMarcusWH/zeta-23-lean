"""Compute the two-sector node Gram matrix and independently check its masked terms."""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
TREE = HERE.parent / "step4-harmonic-recovery-2026-11-19" / "check_dyadic_tree.py"
spec = importlib.util.spec_from_file_location("dyadic_tree", TREE)
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


def run(x):
    first, cap, top, s, shells, _, digest = native.native_input(x)
    exponent_denominator = 1000
    z = native.root_floor(x, exponent_denominator)
    y = (x - 1).bit_length() ** 2
    shift = top + max(top - s, 0)
    sectors = [defaultdict(list) for _ in range(3)]
    gram = [[0, 0], [0, 0]]
    for j, labels in shells.items():
        depth = max(j - s, 0)
        sums = defaultdict(lambda: [0, 0])
        for row in labels:
            q, sign, _ = row
            primes = [int(p) for p, _ in native.fmpz(q).factor()]
            if min(primes) <= y:
                continue
            group = int(q // max(primes) > z)
            sectors[group][j].append(row)
            sectors[2][j].append(row)
            for k in range(depth + 1):
                sums[k, q >> (depth - k)][group] += sign
        for (k, _), charges in sums.items():
            w = 1 << (shift - j - k)
            for i in range(2):
                for m in range(2):
                    gram[i][m] += w * charges[i] * charges[m]
    results = [native.tree_covariance(rows, s, shift, cap)[0] for rows in sectors]
    if x <= 2**17:
        for rows, result in zip(sectors, results):
            assert native.direct_pairs(rows, s, shift, cap) == result
    units = 1 << shift
    left, cross, right = gram[0][0], gram[0][1], gram[1][1]
    assert gram[1][0] == cross
    assert [row["total_positive_energy"] for row in results] == [left, right, left + right + 2 * cross]
    masked = [row["strict_small_gcd_off_diagonal"] for row in results]
    masked_cross = masked[2] - masked[0] - masked[1]
    assert masked_cross == 2 * cross - (results[2]["complement_gcd_off_diagonal"]
                                          - sum(row["complement_gcd_off_diagonal"] for row in results[:2]))
    det = left * right - cross * cross
    assert det >= 0
    radial = (left - right) ** 2
    discriminant = radial + 4 * det
    assert discriminant == (left + right + 2 * cross) * (left + right - 2 * cross)
    return {
        "X": x, "first": first, "y": y, "integer_cofactor_cutoff": z,
        "cofactor_exponent": "1/1000", "native_gcd_cap": cap, "source_sign_sha256": digest,
        "cone_complement_label_counts": [sum(map(len, rows.values())) for rows in sectors[:2]],
        "gram": [[str(Fraction(v, units)) for v in row] for row in gram],
        "cosine_squared": str(Fraction(cross * cross, left * right)) if left * right else None,
        "squared_energy_difference": str(Fraction(radial, units**2)),
        "four_gram_determinant": str(Fraction(4 * det, units**2)),
        "discriminant_over_X": str(Fraction(discriminant, units**2 * x)),
        "masked_cone_complement_mixed_full": [str(Fraction(v, units)) for v in
                                              (masked[0], masked[1], masked_cross, masked[2])],
        "masked_cross_direct_pair_check": x <= 2**17,
    }


if __name__ == "__main__":
    receipt = {
        "status": "EXACT_FINITE_DETERMINISTIC_CONE_GRAM",
        "scope": "Original cutoff, roughness, cell weights and GCD mask. Deterministic cone and its complete complement. No adaptive matching or asymptotic inference.",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "tree_script_sha256": sha256(TREE.read_bytes()).hexdigest(),
        "cases": [run(x) for x in (2**16, 2**17, 2**20)],
    }
    (HERE / "SIGNED_GRAM_CHECK.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt["cases"][-1]))
