"""Floating-point-free acceptance kernel for the arithmetic frontier (Increment 2B).

Every acceptance or falsification decision of the frontier engine passes through
this module. It uses only python-flint balls, exact dyadic/rational endpoints
and the standard library, so it runs in the hash-locked CI environment.

Status semantics (BUDGET_SCHEMA dispositions):

* ``CERTIFIED``: an accepted certificate of the exact stated inequality.
* ``FALSIFIED_BOUND``: an exact (dyadic) vector whose enclosed quadratic value
  violates the exact stated bound.
* ``UNKNOWN_PRECISION``: neither; a failed factorization, an unresolved pivot,
  equality at a non-strict bound or a floating estimate never falsifies.
* ``NOT_ELIGIBLE``: a precondition of the certificate family is not certified.

Invalid arguments raise ``InvalidCertificateInput``. Floating code may *propose*
factors, vectors and inverse actions; only their exact values enter here.

This is research certification, not Lean authority. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import hashlib
import math
from fractions import Fraction

from flint import arb, arb_mat, ctx, fmpq

DISPOSITIONS = ('CERTIFIED', 'FALSIFIED_BOUND', 'UNKNOWN_PRECISION', 'RESOURCE_STOP', 'NOT_ELIGIBLE')
FAMILIES = {
    'SCALAR_GAP': 'D - a^-1 C C^T >= 0 with A >= a I > 0 certified',
    'GEOMETRIC_TAIL': 'D - C P_m(A) C^T - (q^m/a) C C^T >= 0, P_m(A) = b^-1 sum_{j<m} (I - A/b)^j exact, q = 1 - a/b, a I <= A <= b I certified (DERIVED sufficiency)',
    'INVERSE_RESIDUAL': 'D - C X - X^T C^T + X^T A X - a^-1 R^T R >= 0, R = C^T - A X, any exact X, A >= a I > 0 certified (Lean: blockEnergy_nonneg_of_inverse_residual_certificate)',
}


class InvalidCertificateInput(ValueError):
    """A declared precondition of a certificate routine is violated."""


# ----------------------------------------------------------------------------- exact numbers

def q(x) -> arb:
    """Exact ball of a rational (Fraction, int or decimal string)."""
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


def dyadic(value: float) -> Fraction:
    """Exact rational value of a finite binary float."""
    if not isinstance(value, (int, float)) or not math.isfinite(value):
        raise InvalidCertificateInput('non-finite proposal entry')
    return Fraction(value)


def exact_value(x: arb) -> Fraction:
    if not x.is_exact():
        raise InvalidCertificateInput('ball is not exact')
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Fraction(m) * Fraction(2) ** e if e >= 0 else Fraction(m, 2 ** (-e))


def endpoints(x: arb) -> tuple[Fraction, Fraction]:
    """Exact rational endpoints of the stored ball [mid - rad, mid + rad]."""
    if not x.is_finite():
        raise InvalidCertificateInput('non-finite ball')
    m, r = exact_value(x.mid()), exact_value(x.rad())
    return m - r, m + r


def upper(x: arb) -> Fraction:
    return endpoints(x)[1]


def lower(x: arb) -> Fraction:
    return endpoints(x)[0]


def certainly_negative(x: arb) -> bool:
    return x.is_finite() and upper(x) < 0


def certainly_positive(x: arb) -> bool:
    return x.is_finite() and lower(x) > 0


def exact_str(v: Fraction) -> str:
    """Exact compact rendering: 'm*2^e' for dyadic values, 'p/q' otherwise."""
    d = v.denominator
    if d & (d - 1) == 0:
        return '%d*2^%d' % (v.numerator, -(d.bit_length() - 1))
    return str(v)


def ball_record(x: arb) -> dict:
    lo, hi = endpoints(x)
    return {'lower_exact': exact_str(lo), 'upper_exact': exact_str(hi), 'display': x.str(10)}


def float_str(v: Fraction) -> str:
    """Display only: a decimal rendering of an exact endpoint (never acceptance data)."""
    if v == 0:
        return '0'
    e = math.floor(math.log10(abs(v.numerator)) - math.log10(v.denominator))
    return '%se%d' % (format(float(v / Fraction(10) ** e), '.12g'), e)


# ----------------------------------------------------------------------------- matrices

def exact_matrix(rows) -> arb_mat:
    """Exact ball matrix from rationals or finite floats."""
    out = []
    for row in rows:
        r = []
        for x in row:
            if isinstance(x, float):
                if not math.isfinite(x):
                    raise InvalidCertificateInput('non-finite proposal entry')
                r.append(arb(x))  # exact binary conversion
            else:
                r.append(q(x))
        out.append(r)
    return arb_mat(out)


def identity(n: int, scale=1) -> arb_mat:
    s = scale if isinstance(scale, arb) else q(scale)
    return arb_mat([[s if i == j else arb(0) for j in range(n)] for i in range(n)])


def require_square(A: arb_mat) -> int:
    if A.nrows() != A.ncols():
        raise InvalidCertificateInput('matrix is not square')
    return A.nrows()


def require_symmetric(A: arb_mat) -> None:
    """Reject inputs whose two triangles are not enclosures of one symmetric matrix."""
    n = require_square(A)
    for i in range(n):
        for j in range(i + 1, n):
            if not A[i, j].overlaps(A[j, i]):
                raise InvalidCertificateInput('nonsymmetric input: entries (%d,%d) and (%d,%d) are disjoint' % (i, j, j, i))
    for i in range(n):
        for j in range(n):
            if not A[i, j].is_finite():
                raise InvalidCertificateInput('non-finite entry')


def symmetrized(A: arb_mat) -> arb_mat:
    """Union of the two triangles: still encloses the exact symmetric matrix."""
    n = require_square(A)
    return arb_mat([[A[i, j].union(A[j, i]) for j in range(n)] for i in range(n)])


def frobenius_sq(E: arb_mat) -> arb:
    total = arb(0)
    for row in E.tolist():
        for x in row:
            total += x * x
    return total


def mid_cholesky(A: arb_mat):
    """Midpoint Cholesky proposal (exact midpoints); None if a pivot is not positive."""
    n = A.nrows()
    M = [[x.mid() for x in row] for row in A.tolist()]
    R = [[arb(0)] * n for _ in range(n)]
    for j in range(n):
        s = M[j][j]
        for k in range(j):
            s -= R[j][k] * R[j][k]
        s = s.mid()
        if not (s > 0):
            return None
        d = s.sqrt().mid()
        R[j][j] = d
        for i in range(j + 1, n):
            t = M[i][j]
            for k in range(j):
                t -= R[i][k] * R[j][k]
            R[i][j] = (t / d).mid()
    return arb_mat(R)


def certify_shifted(A: arb_mat, tau, R: arb_mat | None = None) -> dict:
    """Shifted factor certificate: A - tau I - R R^T = E, ||E||_F < tau, tau > 0 => A > 0.

    ``R`` is any exact proposal (for instance an exact dyadic floating Cholesky
    factor); without it a midpoint Cholesky is computed here. The bound
    A >= (tau - ||E||_F) I uses R R^T >= 0 and ||E||_2 <= ||E||_F.
    """
    tau = Fraction(tau)
    if not tau > 0:
        raise InvalidCertificateInput('shift tau must be a finite positive rational')
    n = require_square(A)
    require_symmetric(A)
    if n == 0:
        return {'status': 'CERTIFIED', 'tau': str(tau), 'dimension': 0, 'vacuous': True}
    t = q(tau)
    if R is None:
        R = mid_cholesky(A - identity(n, t))
        if R is None:
            return {'status': 'UNKNOWN_PRECISION', 'reason': 'midpoint shifted factorization failed', 'tau': str(tau)}
    if R.nrows() != n:
        raise InvalidCertificateInput('factor has the wrong dimension')
    if not all(x.is_exact() for row in R.tolist() for x in row):
        raise InvalidCertificateInput('factor proposal must be exact')
    E = A - R * R.transpose() - identity(n, t)
    fro2 = frobenius_sq(E)
    hi = upper(fro2)
    ok = hi < tau * tau
    out = {'status': 'CERTIFIED' if ok else 'UNKNOWN_PRECISION', 'tau': str(tau), 'dimension': n,
           'residual_frobenius_sq_upper': exact_str(hi)}
    if ok:
        s = upper(q(hi).sqrt()) if hi > 0 else Fraction(0)
        out['certified_lower_eigenvalue_coordinates'] = exact_str(tau - s) if (tau - s).denominator & ((tau - s).denominator - 1) == 0 else str(tau - s)
        out['certified_lower_eigenvalue_display'] = float_str(tau - s)
    return out


def certify_ldl(A: arb_mat) -> dict:
    """Interval LDL^T of a symmetric enclosure: every pivot certainly positive => A > 0."""
    n = require_square(A)
    require_symmetric(A)
    M = symmetrized(A).tolist()
    for k in range(n):
        p = M[k][k]
        if not certainly_positive(p):
            return {'status': 'UNKNOWN_PRECISION', 'failed_pivot': k, 'dimension': n}
        for i in range(k + 1, n):
            f = M[i][k] / p
            for j in range(k + 1, i + 1):
                M[i][j] = M[i][j] - f * M[j][k]
                M[j][i] = M[i][j]
    return {'status': 'CERTIFIED', 'dimension': n, 'method': 'INTERVAL_LDL'}


def certify_block_ldl(A: arb_mat, block: int = 96) -> dict:
    """Blocked interval Schur elimination: certify A11 > 0, recurse on A22 - A21 A11^-1 A12."""
    n = require_square(A)
    require_symmetric(A)
    rows = symmetrized(A).tolist()
    level = 0
    while rows:
        k = min(block, len(rows))
        A11 = arb_mat([r[:k] for r in rows[:k]])
        lead = certify_ldl(A11)
        if lead['status'] != 'CERTIFIED':
            return {'status': 'UNKNOWN_PRECISION', 'failed_block': level, 'dimension': n, 'method': 'BLOCK_INTERVAL_SCHUR'}
        if k == len(rows):
            break
        A12 = arb_mat([r[k:] for r in rows[:k]])
        A22 = arb_mat([r[k:] for r in rows[k:]])
        S = A22 - A12.transpose() * A11.solve(A12)
        m = S.nrows()
        rows = [[S[i, j].union(S[j, i]) for j in range(m)] for i in range(m)]
        level += 1
    return {'status': 'CERTIFIED', 'dimension': n, 'method': 'BLOCK_INTERVAL_SCHUR', 'block': block, 'levels': level + 1}


# ----------------------------------------------------------------------------- vectors and witnesses

def exact_vector(values) -> arb_mat:
    return exact_matrix([[v] for v in values])


def quadratic(A: arb_mat, v: arb_mat) -> arb:
    if v.ncols() != 1 or v.nrows() != A.nrows():
        raise InvalidCertificateInput('vector has the wrong dimension')
    if not all(v[i, 0].is_exact() for i in range(v.nrows())):
        raise InvalidCertificateInput('witness vector must be exact')
    return (v.transpose() * A * v)[0, 0]


def rayleigh(A: arb_mat, v: arb_mat, G: arb_mat | None = None) -> arb:
    """Enclosed Rayleigh quotient with an enclosed denominator (identity or the given Gram)."""
    den = quadratic(G, v) if G is not None else quadratic(identity(A.nrows()), v)
    if not certainly_positive(den):
        raise InvalidCertificateInput('witness norm is not certainly positive')
    return quadratic(A, v) / den


def refute_lower(A: arb_mat, a, v: arb_mat, G: arb_mat | None = None) -> dict:
    """FALSIFIED_BOUND for A >= a G (G = I by default) iff v^T (A - a G) v < 0 is certified."""
    Gm = G if G is not None else identity(A.nrows())
    val = quadratic(A - q(a) * Gm, v)
    return {'bound': 'A >= %s G' % Fraction(a), 'witness_value': ball_record(val),
            'status': 'FALSIFIED_BOUND' if certainly_negative(val) else 'NOT_REFUTED_BY_THIS_WITNESS'}


def refute_upper(A: arb_mat, b, v: arb_mat, G: arb_mat | None = None) -> dict:
    Gm = G if G is not None else identity(A.nrows())
    val = quadratic(q(b) * Gm - A, v)
    return {'bound': 'A <= %s G' % Fraction(b), 'witness_value': ball_record(val),
            'status': 'FALSIFIED_BOUND' if certainly_negative(val) else 'NOT_REFUTED_BY_THIS_WITNESS'}


def certify_lower(A: arb_mat, a, tau, G: arb_mat | None = None, R: arb_mat | None = None) -> dict:
    """CERTIFIED for A >= a G via a shifted certificate of A - a G."""
    Gm = G if G is not None else identity(A.nrows())
    return {'bound': 'A >= %s G' % Fraction(a), **certify_shifted(A - q(a) * Gm, tau, R)}


def certify_upper(A: arb_mat, b, tau, G: arb_mat | None = None, R: arb_mat | None = None) -> dict:
    Gm = G if G is not None else identity(A.nrows())
    return {'bound': 'A <= %s G' % Fraction(b), **certify_shifted(q(b) * Gm - A, tau, R)}


# ----------------------------------------------------------------------------- carriers

def corrected_basis(Z: arb_mat, C: arb_mat, pivots: list[int]) -> arb_mat:
    """Enclosure of Y_* = Z - E_P (C E_P)^-1 C Z for the exact constraint matrix C.

    C Y_* = C Z - (C E_P)(C E_P)^-1 C Z = 0 holds algebraically once C E_P is
    invertible; the solve certifies invertibility (it raises on a singular or
    unresolved pivot block). The interval check C Y in 0 is only a consistency
    check of the enclosure.
    """
    r = C.nrows()
    if len(pivots) != r or len(set(pivots)) != r or not all(0 <= p < C.ncols() for p in pivots):
        raise InvalidCertificateInput('pivot set must name r distinct columns')
    if Z.nrows() != C.ncols():
        raise InvalidCertificateInput('proposal has the wrong row dimension')
    if not all(x.is_exact() for row in Z.tolist() for x in row):
        raise InvalidCertificateInput('proposal must be exact')
    CP = arb_mat([[C[i, p] for p in pivots] for i in range(r)])
    try:
        delta = CP.solve(C * Z)
    except ZeroDivisionError as exc:
        raise InvalidCertificateInput('pivot block not certified invertible') from exc
    rows = Z.tolist()
    for k, p in enumerate(pivots):
        rows[p] = [rows[p][j] - delta[k, j] for j in range(Z.ncols())]
    Y = arb_mat(rows)
    if not in_kernel(C, Y):
        raise InvalidCertificateInput('corrected enclosure is inconsistent with C Y = 0')
    return Y


def in_kernel(C: arb_mat, Y: arb_mat) -> bool:
    P = C * Y
    return all(P[i, j].contains(0) for i in range(P.nrows()) for j in range(P.ncols()))


def realification_adapter() -> str:
    return ('Real constraints define a real slice whose complexification is the complex slice; for a real symmetric '
            'form, Q(u + i v) = Q(u) + Q(v) and ||u + i v||^2 = ||u||^2 + ||v||^2, so a real certificate of '
            'Q + eps ||.||^2 >= 0 is the complex statement.')


# ----------------------------------------------------------------------------- block certificate families

def _blocks(B: arb_mat, k: int):
    n = require_square(B)
    if not 0 < k < n:
        raise InvalidCertificateInput('block split must be proper')
    rows = B.tolist()
    D = arb_mat([r[:k] for r in rows[:k]])
    C = arb_mat([r[k:] for r in rows[:k]])
    A = arb_mat([r[k:] for r in rows[k:]])
    return D, C, A


def _f(factors, key):
    return (factors or {}).get(key)


def precondition_tau(a: Fraction) -> Fraction:
    return min(a / 64, Fraction(1, 1024))


def family_scalar_gap(B: arb_mat, k: int, a, tau, factors: dict | None = None) -> dict:
    D, C, A = _blocks(B, k)
    a = Fraction(a)
    pre = certify_lower(A, a, tau=precondition_tau(a), R=_f(factors, 'lower'))
    if pre['status'] != 'CERTIFIED':
        return {'family': 'SCALAR_GAP', 'status': 'NOT_ELIGIBLE', 'precondition': pre}
    S = D - C * C.transpose() * (1 / q(a))
    return {'family': 'SCALAR_GAP', 'a': str(a), 'precondition': pre, **certify_shifted(S, tau, _f(factors, 'S'))}


def refute_scalar_gap_for_all(B: arb_mat, k: int, w_high: arb_mat, v_low: arb_mat) -> dict:
    """Refute D - a^-1 C C^T >= 0 for every admissible a in (0, lambda_min(A)].

    rho is the enclosed Rayleigh quotient of the exact vector w_high in A (an
    upper bound on lambda_min(A)); its exact upper endpoint rho_hi is used. For
    a <= lambda_min(A) <= rho_hi, D - CC^T/a <= D - CC^T/rho_hi, so one certified
    negative value of the latter at v_low refutes every admissible scalar gap.
    """
    D, C, A = _blocks(B, k)
    rho = rayleigh(A, w_high)
    rho_hi = upper(rho)
    if not rho_hi > 0:
        return {'family': 'SCALAR_GAP', 'status': 'NOT_ELIGIBLE', 'reason': 'no positive Rayleigh bound'}
    val = quadratic(D - C * C.transpose() * (1 / q(rho_hi)), v_low)
    return {'family': 'SCALAR_GAP', 'quantifier': 'every a with 0 < a <= lambda_min(A)',
            'rho_upper_exact': exact_str(rho_hi), 'rho_upper_display': float_str(rho_hi), 'witness_value': ball_record(val),
            'status': 'FALSIFIED_BOUND' if certainly_negative(val) else 'NOT_REFUTED_BY_THIS_WITNESS'}


def inverse_residual_form(B: arb_mat, k: int, a, X: arb_mat) -> arb_mat:
    D, C, A = _blocks(B, k)
    res = C.transpose() - A * X
    CX = C * X
    return D - CX - CX.transpose() + X.transpose() * A * X - res.transpose() * res * (1 / q(a))


def geometric_tail_form(B: arb_mat, k: int, a, b, m: int) -> arb_mat:
    D, C, A = _blocks(B, k)
    a, b = Fraction(a), Fraction(b)
    P = polynomial_action(A, b, m)
    return D - C * P * C.transpose() - C * C.transpose() * q((1 - a / b) ** m / a)


def family_inverse_residual(B: arb_mat, k: int, a, X: arb_mat, tau, factors: dict | None = None) -> dict:
    D, C, A = _blocks(B, k)
    a = Fraction(a)
    pre = certify_lower(A, a, tau=precondition_tau(a), R=_f(factors, 'lower'))
    if pre['status'] != 'CERTIFIED':
        return {'family': 'INVERSE_RESIDUAL', 'status': 'NOT_ELIGIBLE', 'precondition': pre}
    if not all(x.is_exact() for row in X.tolist() for x in row):
        raise InvalidCertificateInput('inverse action proposal must be exact')
    res = C.transpose() - A * X
    S = inverse_residual_form(B, k, a, X)
    return {'family': 'INVERSE_RESIDUAL', 'a': str(a), 'precondition': pre,
            'residual_frobenius_sq_upper': float_str(upper(frobenius_sq(res))), **certify_shifted(S, tau, _f(factors, 'S'))}


def polynomial_action(A: arb_mat, b, m: int) -> arb_mat:
    """Enclosure of the exact P_m(A) = b^-1 sum_{j<m} (I - A/b)^j."""
    n = A.nrows()
    T = identity(n) - A * (1 / q(b))
    P, term = identity(n, 0), identity(n)
    for _ in range(m):
        P = P + term
        term = term * T
    return P * (1 / q(b))


def family_geometric_tail(B: arb_mat, k: int, a, b, m: int, tau, factors: dict | None = None) -> dict:
    D, C, A = _blocks(B, k)
    a, b = Fraction(a), Fraction(b)
    if not 0 < a < b:
        raise InvalidCertificateInput('require 0 < a < b')
    lo = certify_lower(A, a, tau=precondition_tau(a), R=_f(factors, 'lower'))
    hi = certify_upper(A, b, tau=Fraction(1, 1024), R=_f(factors, 'upper'))
    if lo['status'] != 'CERTIFIED' or hi['status'] != 'CERTIFIED':
        return {'family': 'GEOMETRIC_TAIL', 'status': 'NOT_ELIGIBLE', 'lower': lo, 'upper': hi}
    S = geometric_tail_form(B, k, a, b, m)
    return {'family': 'GEOMETRIC_TAIL', 'a': str(a), 'b': str(b), 'degree': m, 'q_power_over_a': float((1 - a / b) ** m / a),
            'lower': lo, 'upper': hi, **certify_shifted(S, tau, _f(factors, 'S'))}


# ----------------------------------------------------------------------------- hashing

def enclosure_sha256(M: arb_mat) -> str:
    """Hash of the exact stored enclosure (midpoint and radius mantissa/exponent pairs)."""
    h = hashlib.sha256()
    h.update(b'%d %d\n' % (M.nrows(), M.ncols()))
    for row in M.tolist():
        for x in row:
            m1, e1 = x.mid().man_exp()
            m2, e2 = x.rad().man_exp()
            h.update(('%d %d %d %d\n' % (int(m1), int(e1), int(m2), int(e2))).encode())
    return h.hexdigest()


def rational_sha256(values) -> str:
    return hashlib.sha256('\n'.join(str(Fraction(v)) for v in values).encode()).hexdigest()


def quartic_cutoff(L) -> int:
    p = Fraction(L) ** 4
    return -((-p.numerator) // p.denominator)


def validate_state(L, K: int, Q: int, prime_powers: list[int]) -> None:
    """Reject wrong cutoffs and altered prime-power lists for a quartic target."""
    L = Fraction(L)
    if K != quartic_cutoff(L):
        raise InvalidCertificateInput('cutoff is not originalDetectorQuarticCutoff(L)')
    ctx_prec = ctx.prec
    try:
        ctx.prec = 128
        La = q(L)
        if not (arb(Q).log() < La and La < arb(Q + 1).log()):
            raise InvalidCertificateInput('aperture not certified in the prime cell of Q')
    finally:
        ctx.prec = ctx_prec
    expect = []
    for n in range(2, Q + 1):
        m, p = n, 2
        while p * p <= m and m % p:
            p += 1
        p = m if p * p > m else p
        while m % p == 0:
            m //= p
        if m == 1:
            expect.append(n)
    if list(prime_powers) != expect:
        raise InvalidCertificateInput('prime-power list differs from all prime powers up to Q')
