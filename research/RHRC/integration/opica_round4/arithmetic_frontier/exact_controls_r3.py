"""Exact replays of the revision-3 external countermodels (MP14, MP15, MP18).

Pure Python with exact integers and fractions; no floating point, no optional
dependencies, and explicit conditional failures instead of ``assert`` statements,
so ``python -O`` runs the same checks. These are substitution and inference
controls. They reject a shortcut; they are not counterexamples to any actual
native route. RH and Step 4 remain OPEN.

* MP15 (coarse-growth report, section 9): for Y = floor(sqrt N),
  Q_N = sum_{a,b<=Y} mu(a) mu(b) floor(N/(ab)) satisfies Q_N = 2 M(Y) - M(N), while
  G_N = sum_{a,b<=Y} mu(a) mu(b) floor(N/lcm(a,b)) = sum_{n<=N} (sum_{a<=Y, a|n} mu(a))^2 >= 0.
  At N = 10: Q = -1 and G = 4. The product kernel cannot be replaced by the
  positive lcm Gram.
* MP14 (geometry report, section 10): aligned scalars B_i = -eps (i = 1..m) have
  individual norm a = eps and square-function constant b = sqrt(m) eps, yet the
  nonbacktracking operator (N z)_i = sum_{j != i} B_j z_j has the real eigenvalue
  -(m - 1) eps. With m = 4^k and eps = 2^-k this is -(4^k - 1)/2^k while a -> 0 and b = 1.
  The determinant identity det(I - uN) = prod(1 + u B_i) * F(u) with
  F(u) = 1 - u sum B_i / (1 + u B_i) is checked exactly, as is the reverse
  instability bound r_+ <= (m - 1) eps whenever s > a + 2b.
* MP18: J = diag(0, 1), l = (1, 1), z = (0, M), H = [[0, M], [M, 0]] satisfies
  [J, H] = z l* - l z* with zero diagonal and lambda_min(H) = -M.
* MP20 (centered-prime report, section 8): the exact even and odd seeds of the
  comparison-density falsification lie in the seed moment slices, and their
  partial-fraction identities hold exactly. The comparison density is NOT zeta.
* MP21 (methodology postmortem, section 4): the rational causal model
  E(z) = -lam (1 + delta) / ((z + 1)^2 (z + lam - delta)). For delta = 0 the output
  is globally L2 with ||E||^2 = lam (lam + 2) / (4 (lam + 1)^2), while its first
  variation -1 + (1 + t) e^-t is not L2. For 0 < lam <= delta the residue at
  z = delta - lam is nonzero: local convergence with global failure.
* MP22 (postmortem, section 5): the boundary-layer constants
  int_0^inf |phi_m(u)|^2 du with phi_m(u) = e^-u sum_k (-1)^k C(m, k) u^(k-1)/(k-1)!
  equal 1/2 (m = 1) and 5/4 (m = 2), checked exactly through m = 12.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_EXACT_CONTROLS_R3_V1'


class ControlFailure(RuntimeError):
    pass


def check(value: bool, message: str) -> None:
    if not value:
        raise ControlFailure(message)


def mobius_table(n: int) -> list[int]:
    mu = [1] * (n + 1)
    mu[0] = 0
    is_composite = [False] * (n + 1)
    primes: list[int] = []
    for i in range(2, n + 1):
        if not is_composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_composite[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def isqrt(n: int) -> int:
    r = int(n ** 0.5)
    while r * r > n:
        r -= 1
    while (r + 1) * (r + 1) <= n:
        r += 1
    return r


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def product_vs_lcm(N: int, mu: list[int]) -> dict:
    Y = isqrt(N)
    M = lambda x: sum(mu[1:x + 1])
    Q = sum(mu[a] * mu[b] * (N // (a * b)) for a in range(1, Y + 1) for b in range(1, Y + 1))
    G = sum(mu[a] * mu[b] * (N // (a * b // gcd(a, b))) for a in range(1, Y + 1) for b in range(1, Y + 1))
    gram = sum(sum(mu[a] for a in range(1, Y + 1) if n % a == 0) ** 2 for n in range(1, N + 1))
    return {'N': N, 'Y': Y, 'product_kernel': Q, 'identity_rhs': 2 * M(Y) - M(N), 'lcm_kernel': G,
            'lcm_gram_sum_of_squares': gram}


def det(rows: list[list[Fraction]]) -> Fraction:
    a = [row[:] for row in rows]
    n = len(a)
    sign, result = 1, Fraction(1)
    for c in range(n):
        pivot = next((r for r in range(c, n) if a[r][c] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            sign = -sign
        result *= a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / a[c][c]
            for k in range(c, n):
                a[r][k] -= f * a[c][k]
    return sign * result


def nonbacktracking(B: list[Fraction]) -> list[list[Fraction]]:
    m = len(B)
    return [[(B[j] if i != j else Fraction(0)) for j in range(m)] for i in range(m)]


def aligned_scalar(m: int, eps: Fraction, dense: bool = True) -> dict:
    eigen = -(m - 1) * eps
    if dense:  # explicit matrix-vector product
        B = [-eps] * m
        N = nonbacktracking(B)
        ones = [Fraction(1)] * m
        Nz = [sum(N[i][j] * ones[j] for j in range(m)) for i in range(m)]
        eig_ok = all(Nz[i] == eigen * ones[i] for i in range(m))
    else:  # every row of N 1 is (sum_j B_j) - B_i; computed from the total, not assumed
        total = m * (-eps)
        eig_ok = total - (-eps) == eigen
    a, b2, s = eps, m * eps * eps, m * eps
    regime = (s - a) ** 2 > 4 * b2 and s > a  # s > a + 2b, compared exactly through squares
    # r_+ = (s + a + sqrt((s - a)^2 - 4 b^2)) / 2 <= (m - 1) eps  <=>  sqrt(D) <= 2(m-1)eps - s - a
    lhs = 2 * (m - 1) * eps - s - a
    disc = (s - a) ** 2 - 4 * b2
    bound_ok = (not regime) or (lhs >= 0 and disc <= lhs * lhs)
    return {'m': m, 'eps': str(eps), 'eigenvector_check': eig_ok, 'dense': dense,
            'eigenvalue': str(eigen), 'a': str(a), 'b_squared': str(b2), 's': str(s),
            'regime_s_gt_a_plus_2b': regime, 'reverse_bound_r_plus_le_eigen_magnitude': bound_ok}


def determinant_identity(B: list[Fraction], u: Fraction) -> dict:
    m = len(B)
    N = nonbacktracking(B)
    lhs = det([[(Fraction(1) if i == j else Fraction(0)) - u * N[i][j] for j in range(m)] for i in range(m)])
    prod = Fraction(1)
    for x in B:
        prod *= 1 + u * x
    F = 1 - u * sum(x / (1 + u * x) for x in B)
    return {'B': [str(x) for x in B], 'u': str(u), 'det_I_minus_uN': str(lhs), 'product_times_F': str(prod * F),
            'holds': lhs == prod * F}


def two_by_two(M: Fraction) -> dict:
    J = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    H = [[Fraction(0), M], [M, Fraction(0)]]
    ell = [Fraction(1), Fraction(1)]
    z = [Fraction(0), M]
    comm = [[sum(J[i][k] * H[k][j] - H[i][k] * J[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    rank_two = [[z[i] * ell[j] - ell[i] * z[j] for j in range(2)] for i in range(2)]
    # eigenvalues of [[0, M], [M, 0]] are +-M
    return {'M': str(M), 'commutator_identity': comm == rank_two, 'diagonal': [str(H[0][0]), str(H[1][1])],
            'lambda_min': str(-abs(M))}


def comparison_seeds() -> dict:
    """MP20: exact seeds and partial fractions of the comparison-density test."""
    ye, wo = [70, -56, 28, -8, 1], [42, -48, 27, -8, 1]
    We = [1, 2, 2, 2, 2]
    even_moments = [sum(We[n] * ye[n] * n ** (2 * k) for n in range(5)) for k in range(4)]
    odd_moments = [sum(n * wo[n - 1] * n ** (2 * k) for n in range(1, 6)) for k in range(4)]
    pf = []
    for z in (Fraction(1, 3), Fraction(5, 2), Fraction(7), Fraction(-1, 2), Fraction(11, 13)):
        lhs_e = sum(Fraction(We[n] * ye[n]) / (z + n * n) for n in range(5))
        rhs_e = Fraction(40320) / (z * (z + 1) * (z + 4) * (z + 9) * (z + 16))
        lhs_o = sum(Fraction(n * wo[n - 1]) / (z + n * n) for n in range(1, 6))
        rhs_o = Fraction(362880) / ((z + 1) * (z + 4) * (z + 9) * (z + 16) * (z + 25))
        pf.append({'z': str(z), 'even': lhs_e == rhs_e, 'odd': lhs_o == rhs_o})
    return {'even_seed': ye, 'odd_seed': wo, 'even_seed_moments_M0_M2_M4_M6': even_moments,
            'odd_seed_moments_M1_M3_M5_M7': odd_moments, 'partial_fractions': pf,
            'label': 'NOT_ZETA comparison-density seeds; exact algebra only'}


def causal_rational_model(lam: Fraction) -> dict:
    """MP21 with delta = 0: E(t) = -lam (a e^-t + b t e^-t + c e^-lam t), exact L2 norm."""
    check(lam > 0 and lam != 1, 'lambda must be positive and differ from 1')
    a, b, c = -1 / (1 - lam) ** 2, 1 / (lam - 1), 1 / (1 - lam) ** 2
    # residues of 1/((z+1)^2 (z+lam)) are (a, b) at z = -1 and c at z = -lam
    norm = lam * lam * (a * a / 2 + b * b * Fraction(2, 8) + c * c / (2 * lam) + 2 * a * b / 4 +
                        2 * a * c / (1 + lam) + 2 * b * c / (1 + lam) ** 2)
    closed = lam * (lam + 2) / (4 * (lam + 1) ** 2)
    # first variation: lim E/lam at lam -> 0 has coefficients a -> -1, b -> -1, c -> 1
    return {'lambda': str(lam), 'norm_sq': str(norm), 'closed_form': str(closed), 'equal': norm == closed,
            'first_variation': '-1 + (1 + t) e^-t (tends to -1: not L2)'}


def causal_growing_residue(lam: Fraction, delta: Fraction) -> dict:
    """MP21 with 0 < lam <= delta: the residue at z = delta - lam is nonzero."""
    res = -lam * (1 + delta) / (1 + delta - lam) ** 2
    return {'lambda': str(lam), 'delta': str(delta), 'residue': str(res), 'nonzero': res != 0,
            'pole_real_part': str(delta - lam), 'nondecaying': delta - lam >= 0}


def boundary_layer_constant(m: int) -> Fraction:
    """MP22: int_0^inf |phi_m(u)|^2 du, exactly."""
    from math import comb, factorial
    coeff = [Fraction((-1) ** k * comb(m, k), factorial(k - 1)) for k in range(1, m + 1)]  # u^(k-1)
    total = Fraction(0)
    for i, ci in enumerate(coeff):
        for j, cj in enumerate(coeff):
            n = i + j  # int_0^inf u^n e^-2u du = n! / 2^(n+1)
            total += ci * cj * Fraction(factorial(n), 2 ** (n + 1))
    return total


def run() -> dict:
    mu = mobius_table(200)
    rows = [product_vs_lcm(N, mu) for N in range(1, 101)]
    for r in rows:
        check(r['product_kernel'] == r['identity_rhs'], 'identity (9.1) fails at N=%d' % r['N'])
        check(r['lcm_kernel'] == r['lcm_gram_sum_of_squares'] and r['lcm_kernel'] >= 0,
              'lcm Gram identity fails at N=%d' % r['N'])
    n10 = rows[9]
    check((n10['N'], n10['Y'], n10['product_kernel'], n10['lcm_kernel']) == (10, 3, -1, 4), 'N=10 values differ')
    negative = [r['N'] for r in rows if r['product_kernel'] < 0]
    aligned = [aligned_scalar(m, Fraction(1, 3)) for m in (2, 5, 6, 7, 12, 40)]
    for r in aligned:
        check(r['eigenvector_check'] and r['reverse_bound_r_plus_le_eigen_magnitude'], 'aligned scalar control fails')
    check([r['regime_s_gt_a_plus_2b'] for r in aligned] == [False, False, True, True, True, True],
          'regime boundary differs from m >= 6')
    family = []
    for k in range(1, 11):
        r = aligned_scalar(4 ** k, Fraction(1, 2 ** k), dense=k <= 4)
        check(r['eigenvector_check'] and Fraction(r['eigenvalue']) == -Fraction(4 ** k - 1, 2 ** k) and
              Fraction(r['b_squared']) == 1, 'exponential aligned family fails at k=%d' % k)
        family.append({'k': k, 'm': 4 ** k, 'a': r['a'], 'b_squared': r['b_squared'], 'eigenvalue': r['eigenvalue']})
    dets = [determinant_identity([Fraction(n, d) for n, d in Bs], u) for Bs, u in (
        ([(1, 2), (-3, 4), (2, 5)], Fraction(1, 7)),
        ([(-1, 1), (-1, 1), (-1, 1), (-1, 1)], Fraction(-1, 3)),
        ([(5, 3), (-2, 9), (7, 11), (-4, 5), (1, 6)], Fraction(2, 13)))]
    for r in dets:
        check(r['holds'], 'determinant identity fails')
    two = [two_by_two(Fraction(M)) for M in (1, 7, 1000)]
    for r in two:
        check(r['commutator_identity'] and r['diagonal'] == ['0', '0'], 'two-by-two control fails')
    seeds = comparison_seeds()
    check(seeds['even_seed_moments_M0_M2_M4_M6'] == [0, 0, 0, 0] and seeds['odd_seed_moments_M1_M3_M5_M7'] ==
          [0, 0, 0, 0] and all(r['even'] and r['odd'] for r in seeds['partial_fractions']), 'comparison seeds fail')
    causal = [causal_rational_model(Fraction(n, d)) for n, d in ((1, 1000), (1, 10), (1, 2), (3, 1), (7, 4))]
    check(all(r['equal'] for r in causal), 'causal rational norm differs')
    growing = [causal_growing_residue(Fraction(n, d), Fraction(1, 4)) for n, d in ((1, 100), (1, 8), (1, 4))]
    check(all(r['nonzero'] and r['nondecaying'] for r in growing), 'growing residue control fails')
    layers = {m: boundary_layer_constant(m) for m in range(1, 13)}
    check(layers[1] == Fraction(1, 2) and layers[2] == Fraction(5, 4) and all(v > 0 for v in layers.values()),
          'boundary-layer constants differ')
    return {'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN',
            'authority': 'EXACT_FINITE_CONTROLS_OF_SUBSTITUTIONS_NOT_COUNTEREXAMPLES_TO_NATIVE_ROUTES',
            'MP15_product_vs_lcm': {'checked_N': [1, 100], 'identity_9_1_holds': True, 'lcm_gram_nonnegative': True,
                                    'N10': n10, 'negative_product_kernel_N': negative},
            'MP14_aligned_scalar_nonbacktracking': {'cases': aligned, 'exponential_family': family,
                                                    'determinant_identity': dets},
            'MP18_two_by_two': two,
            'MP20_comparison_density_seeds': seeds,
            'MP21_causal_rational_model': {'delta_zero': causal, 'delta_positive_growing': growing},
            'MP22_boundary_layer_constants': {str(m): str(v) for m, v in layers.items()}}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(argv)
    record = run()
    record['tool_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'N10': record['MP15_product_vs_lcm']['N10'],
                      'negative_N': record['MP15_product_vs_lcm']['negative_product_kernel_N'][:12]}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
