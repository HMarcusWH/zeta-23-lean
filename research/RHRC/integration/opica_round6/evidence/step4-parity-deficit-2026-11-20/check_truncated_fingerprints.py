"""Check product-truncated Boolean interpolation on native PR 303 integer rows."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from math import prod

from check_survivor_cofactor_pairs import complete_cell, independently_factor, native, native_source_digest
from receipt import replay


X = 1656575
Z = 2000
M = 1450000


def subsets(items):
    for k in range(len(items) + 1):
        yield from combinations(items, k)


def variation(vector):
    return sum(abs(value) for value in vector.values())


def digest_rows(vector):
    table = [[list(key), value] for key, value in sorted(vector.items()) if value]
    return sha256(json.dumps(table, separators=(",", ":")).encode()).hexdigest()


def add_basis(vector, subset, coeff):
    for event in subsets(subset):
        vector[event] += coeff * (-1)**(len(subset)-len(event))


def check():
    """Reconstruct the full small-prime histogram and check the wrong-removal control."""
    y = (X - 1).bit_length()**2
    lo, hi = complete_cell(X)
    marked = [p for p in range(y+1, Z+1) if independently_factor(p) == [p]]
    marked_set = set(marked)
    rows = []
    for n, sign, *_ in native.vertex_rows(X, 1):
        if lo <= n < hi:
            factors = independently_factor(n)
            fingerprint = tuple(p for p in factors if p in marked_set)
            if sign != (-1)**len(factors) or min(factors) <= y or len(set(factors)) != len(factors):
                raise ArithmeticError("native factorization discrepancy")
            rows.append((n, sign, fingerprint))
    # Each possible d belongs to this exhaustive list, including all d with count zero.
    if min(marked)**3 <= M:
        raise ValueError("this fixture requires the first omitted degree to exceed M")
    all_d = [()] + [(p,) for p in marked]
    all_d.extend((p, q) for p, q in combinations(marked, 2) if p*q <= M)
    integers = [n for n, _, _ in rows]
    moments = Counter()
    predicted = Counter()
    for subset in all_d:
        d = prod(subset)
        count = sum(n % d == 0 for n in integers)
        moments[subset] = count
        if count:
            add_basis(predicted, subset, count)

    targets = [row for row in rows if prod(row[2]) > M]
    if not targets or any(sign != 1 or len(f) != 2 for _, sign, f in targets):
        raise ValueError("over-limit targets must be genuine positive semiprimes")
    donors = [row for row in rows if row[1] == -1][:len(targets)]
    if len(donors) != len(targets) or any(f for _, _, f in donors):
        raise ValueError("insufficient true opposite-sign donors")
    removed = targets + donors
    removed_ids = {n for n, _, _ in removed}
    survivors = [row for row in rows if row[0] not in removed_ids]
    if not any(len(f) == 2 for _, _, f in survivors):
        raise ValueError("fixture should exercise retained product-pair basis vectors")
    if any(prod(f) > M for _, _, f in survivors) or sum(s for _, s, _ in removed):
        raise ArithmeticError("selection failed its two defining conditions")
    point_only = predicted.copy()
    for _, _, f in removed:
        point_only[f] -= 1
        for subset in subsets(f):
            if prod(subset) <= M:
                add_basis(predicted, subset, -1)
    observed = Counter(f for _, _, f in survivors)
    correct_delta = predicted.copy()
    correct_delta.subtract(observed)
    wrong_delta = point_only.copy()
    wrong_delta.subtract(observed)
    if variation(correct_delta) or variation(wrong_delta) != 4*len(targets):
        raise ArithmeticError("correct reconstruction or intended negative control failed")
    if sum(predicted.values()) != len(survivors) or min(predicted.values()) < 0:
        raise ArithmeticError("reconstructed histogram has an invalid mass")
    return dict(scope="Finite native PR 303 base. Exact raw divisibility counts are the input. "
                      "One-cell auxiliary matched selector tests Boolean algebra, not asymptotic "
                      "density, full three-stage selection, or the Step 4 signed upper.",
                native_generator_sha256_lf=native_source_digest(),
                X=X, cell=[lo, hi], right_open=True, y=y, z=Z, M=M, marks=len(marked),
                admissible_divisors=len(all_d), nonzero_marginals=sum(v > 0 for v in moments.values()),
                marginal_sha256=digest_rows(moments), raw_labels=len(rows),
                matched_positive_targets=len(targets), matched_negative_donors=len(donors),
                first_matching_pair=[targets[0][0], donors[0][0]], survivors=len(survivors),
                survivors_with_two_marks=sum(len(f)==2 for _, _, f in survivors),
                occupied_fingerprints=len(observed), measured_charge=sum(s for _, s, _ in rows),
                surviving_charge=sum(s for _, s, _ in survivors),
                raw_interpolation_example=dict(target=targets[0][0], marks=targets[0][2],
                    terms=[["empty",-1],[str(targets[0][2][0]),1],[str(targets[0][2][1]),1]]),
                reconstruction_l1=variation(correct_delta), direct_sha256=digest_rows(observed),
                reconstructed_sha256=digest_rows(predicted),
                wrong_point_subtraction_l1=variation(wrong_delta))


if __name__ == "__main__":
    replay("TRUNCATED_FINGERPRINTS_CHECK.json", check)
