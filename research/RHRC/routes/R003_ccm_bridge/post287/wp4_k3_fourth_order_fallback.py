#!/usr/bin/env python3
"""WP4 rev4: *predeclared* fourth-order K=3 fixed-unit Arb Taylor alternative.

This is the sole permitted alternative after the frozen second-order gate
fails. It keeps EXACTLY the production equation-(4.4) canonical matrix,
with its original pole, regularized archimedean + wCorrection (ONCE),
and all finite von Mangoldt prime-power atoms for a frozen cutoff Q.

We evaluate analytic Taylor coefficients by FLINT acb_series at either an
exact rational centre or a rigorously enlarged ball of apertures. Coefficients
of the fixed-unit integral are integrated using Arb's validated complex
quadrature, independently at orders 0...4. In particular, the fourth-order
remainder is an enclosure on the WHOLE aperture interval, not a finite
difference estimate or an empirical global Lipschitz constant.

The carrier uses the EXISTING exact [predecessor|shell] parity basis,
and requires a>0 and determinant Δ=ad-b²>0. No division by a is used.
If anything cannot be evaluated or resolved within the frozen gate, output
UNRESOLVED and stop. Never replace this with a positive numerical guess.

This standalone instrument is research evidence, not a Lean theorem,
and not a proof of RH.  It must pass independent tests and an actual
GitHub CI run before any interval data can be accepted.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, acb_series, arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path[:0] = [str(BASE), str(BASE / "post285")]
import canonical_source_arb as C
from post166_fb05_cell_interval import _arb_matrix_from_sympy, cell_coordinate_L_arb
from post169_fb05_schur_visibility import one_step_geometry

FIXTURE = BASE / "fixtures" / "post175_fb05_q13_fixed_unit_enclosure_v1.json"
ORDER = 4
K = 3
RH_STATUS = "RH_OPEN"


def Q(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def _coeffs(s: acb_series) -> list[acb]:
    a = list(s.coeffs())
    return (a + [acb(0)] * (ORDER + 1 - len(a)))[:ORDER + 1]


def _jet(L: arb) -> acb_series:
    return acb_series([acb(L), acb(1)], prec=ORDER + 1)


def _constant(a) -> acb_series:
    return acb_series([acb(a)], prec=ORDER + 1)


def _sinhc(z: acb_series) -> acb_series:
    # sinh(z)/z = 0F1(;3/2; z^2/4), ENTIRE even at z=0.
    return acb_series.hypgeom([], [_constant(arb(3) / 2)], z * z / 4)


def _R(z: acb_series) -> acb_series:
    # Exact fixed-unit regularized archimedean scale R(z).
    return (z / 2).exp() / (2 * _sinhc(z))


def _exp_slope(z: acb_series) -> acb_series:
    # Exact removable (exp(z)-1)/z.
    return (z / 2).exp() * _sinhc(z / 2)


def _integrated_coefficients(factory) -> list[arb]:
    result = []
    for k in range(ORDER + 1):
        def integrand(t, analytic):
            # The entire special functions and fixed positive-L denominators
            # are analytic on the path. Failure propagates instead of masking it.
            return _coeffs(factory(t))[k]
        value = acb.integral(integrand, acb(0), acb(1))
        if not value.imag.contains(0):
            raise ArithmeticError("real source derivative integral not enclosed")
        result.append(value.real)
    return result


def _primitive_jets(L: arb) -> dict:
    X = _jet(L)
    pi = acb(arb.pi())
    w = (arb.const_euler() + (4 * arb.pi()).log()) / 2
    wseries = _constant(w) - (((X.exp() + 1) / (X.exp() - 1)).log() / 2)
    wco = [c.real for c in _coeffs(wseries)]
    alpha, beta, gamma = {}, {}, {}
    for n in range(K + 1):
        u = 2 * pi * n
        if n == 0:
            a = [arb(0)] * (ORDER + 1)
        else:
            a = [2*n*t for t in _integrated_coefficients(
                lambda t: _constant((u*t).sinc()) * _R(X*t))]
        b = _integrated_coefficients(
            lambda t: _constant((u*t).cos()) * _R(X*t))
        g = _integrated_coefficients(
            lambda t: (_constant(u*C._cos_slope(u*t)) +
                       X/2 * _exp_slope(-X*t/2)) * _R(X*t))
        g = [g[j] + wco[j] for j in range(ORDER + 1)]
        for m in ([0] if n == 0 else [-n, n]):
            alpha[m] = [((-1 if m < 0 else 1) * v) for v in a]
            beta[m] = b
            gamma[m] = g
    return {"alpha": alpha, "beta": beta, "gamma": gamma}


def _pole_series(n: int, m: int, X: acb_series) -> acb_series:
    pi = arb.pi()
    sn = ((X / 4).exp() - (-X / 4).exp()) / 2
    return (32 * X * sn * sn * (X*X - 16*pi*pi*n*m) /
           ((X*X + 16*pi*pi*m*m) * (X*X + 16*pi*pi*n*n)))


def _prime_series(n: int, m: int, X: acb_series, q: int) -> acb_series:
    y = acb(arb(q).log())
    z = y / X
    pi = acb(arb.pi())
    if n == m:
        return 2 * (1-z) * (2*pi*n*z).cos()
    return ((2*pi*n*z).sin() - (2*pi*m*z).sin()) / (pi*(m-n))


def full_matrix_jets(L: arb, cutoff: int) -> list[arb_mat]:
    """M_j(L) = (d^j M/dL^j)/j!  (j=0,...,4), all with rigorous Arb balls.

    For an interval-valued base L this encloses the derivative at EVERY
    point in the interval, because every operation and every integral is
    interval-enclosed; exact fixed-Q prime sums are used throughout.
    """
    if cutoff < 1:
        raise ValueError("cutoff must be >= 1")
    prior = ctx.cap
    ctx.cap = ORDER + 1
    try:
        X = _jet(L)
        arch = _primitive_jets(L)
        primes = [(q, C.von_mangoldt(q) / arb(q).sqrt())
                  for q in range(2, cutoff + 1)]
        primes = [(q, w) for q, w in primes if not w.is_zero()]
        inds = list(range(-K, K+1))
        rows = [[[arb(0) for _ in inds] for _ in inds]
                for _ in range(ORDER + 1)]
        for i,n in enumerate(inds):
            for j in range(i,len(inds)):
                m = inds[j]
                pole = _coeffs(_pole_series(n,m,X))
                p_sum = [_constant(0)][0]
                for q,w in primes:
                    p_sum += w * _prime_series(n,m,X,q)
                pp = _coeffs(p_sum)
                for k in range(ORDER + 1):
                    a = ((arch["alpha"][m][k] - arch["alpha"][n][k]) /
                         (n-m) if n != m else
                         2 * arch["gamma"][n][k] - 2 * arch["beta"][n][k])
                    val = pole[k] - acb(a) - pp[k]
                    if not val.imag.contains(0):
                        raise ArithmeticError("matrix jet has a nonreal enclosure")
                    rows[k][i][j] = rows[k][j][i] = val.real
        return [arb_mat(M) for M in rows]
    finally:
        ctx.cap = prior


def compressed_jets(mats: list[arb_mat], parity: str) -> list[arb_mat]:
    B = _arb_matrix_from_sympy(one_step_geometry(2,parity).step_basis_exact)
    out = [B.transpose()*M*B for M in mats]
    if any(M.nrows()!=2 or M.ncols()!=2 for M in out):
        raise AssertionError("wrong K3 legal parity dimension")
    return out


def coeffs_of_a_and_delta(mats: list[arb_mat]) -> tuple[list[arb],list[arb]]:
    a = [M[0,0] for M in mats]
    b = [M[0,1] for M in mats]
    d = [M[1,1] for M in mats]
    determinant = []
    for k in range(ORDER + 1):
        determinant.append(sum(a[j]*d[k-j] - b[j]*b[k-j]
                               for j in range(k+1)))
    return a, determinant


def taylor_lower(center: list[arb], fourth_interval: arb, radius: arb) -> arb:
    """Exact Taylor through degree three + interval fourth derivative/4!.

    Absolute-value bounds here are *only* on the derivative corrections,
    not on the full source channels. Cancellation is retained in the exact
    centre coefficients and in the interval fourth derivative.
    """
    lb = center[0].lower()
    for k in range(1, ORDER):
        lb -= abs(center[k]).upper() * radius**k
    return (lb - abs(fourth_interval).upper()*radius**ORDER).lower()


def check_box(c:arb, r:arb, cutoff:int, parity:str,
              allow_frozen_extension:bool=False) -> dict:
    start = time.monotonic()
    interval = arb(c, r)
    if not bool(interval > 0):
        raise ValueError("aperture interval touches nonpositive L")
    # The Q-frozen complete Eq(4.4) expression is analytic slightly across
    # each prime seam. Full-cover rational bounds intentionally enclose the
    # logarithmic seam from both sides; positivity of this analytic extension
    # implies positivity only on its INTERSECTION with the physical Q-cell.
    # At the frozen Q14 primary gate the physical membership is still strict.
    if not allow_frozen_extension:
        if not C.fixed_cell_membership(cutoff, c)["certified"]:
            raise ValueError("centre not inside requested physical cutoff cell")
        if not C.fixed_cell_membership(cutoff, interval)["certified"]:
            raise ValueError("interval crosses physical cutoff cell")
    cj=compressed_jets(full_matrix_jets(c,cutoff),parity)
    ij=compressed_jets(full_matrix_jets(interval,cutoff),parity)
    ac,dc=coeffs_of_a_and_delta(cj)
    ai,di=coeffs_of_a_and_delta(ij)
    lower_a=taylor_lower(ac,ai[ORDER],r)
    lower_det=taylor_lower(dc,di[ORDER],r)
    return {"parity":parity,
            "a_lower":C.ball_record(lower_a,38),
            "delta_lower":C.ball_record(lower_det,38),
            "a_positive":bool(lower_a>0),
            "delta_positive":bool(lower_det>0),
            "verdict":"PASS" if lower_a>0 and lower_det>0 else "UNRESOLVED",
            "duration_s":round(time.monotonic()-start,2)}


def frozen_boxes():
    fixture=json.loads(FIXTURE.read_text())
    rows=[]
    for q in fixture["primary_Q14_centers"]:
        t=Fraction(str(q["t"]))
        for k in fixture["primary_radius_bits"]:
            for parity in ("even","odd"):
                rows.append((14,t,Fraction(1,2**k),parity,"primary"))
    for q in fixture["control_boxes"]:
        for parity in ("even","odd"):
            rows.append((q["Q"],Fraction(str(q["t"])),
                         Fraction(1,2**q["radius_bit"]),parity,"control"))
    return rows


def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--precision-bits",type=int,default=384)
    p.add_argument("--max-boxes",type=int,default=0,
                   help="0 means every frozen primary and control box")
    p.add_argument("--seconds",type=int,default=1200)
    args=p.parse_args()
    C.set_precision(args.precision_bits)
    ctx.prec=args.precision_bits
    boxes=frozen_boxes()
    chosen=boxes[:args.max_boxes] if args.max_boxes else boxes
    started=time.monotonic()
    result=[]
    for q,t,w,parity,kind in chosen:
        if time.monotonic()-started>=args.seconds:
            break
        try:
            c=cell_coordinate_L_arb(q,Q(t))
            left=cell_coordinate_L_arb(q,Q(t-w))
            right=cell_coordinate_L_arb(q,Q(t+w))
            radius=max(abs(right-c).upper(),abs(c-left).upper())
            o=check_box(c,radius,q,parity)
        except Exception as exc:
            o={"verdict":"UNRESOLVED","error":repr(exc)}
        result.append({"Q":q,"t":[t.numerator,t.denominator],
                       "halfwidth":[w.numerator,w.denominator],
                       "parity":parity,"kind":kind,**o})
        print(json.dumps({"Q":q,"parity":parity,
                          "verdict":o["verdict"]}),flush=True)
    good=(len(result)==len(boxes) and
          all(o["verdict"]=="PASS" for o in result))
    payload={"schema":"post287.wp4.fourth_order.v1",
             "method":"genuine 4th-order fixed-unit Arb Taylor, full Eq4.4",
             "status":"INTERVAL_EVIDENCE" if good else "UNRESOLVED",
             "terminal_claim":RH_STATUS,"frozen_boxes":len(boxes),
             "tested_boxes":len(result),"boxes":result,
             "gate":"PASS" if good else "UNRESOLVED",
             "all_aperture_K3_positivity":False,
             "next_on_failure":"STOP; publish unresolved boxes, do not reparameterize",
             "not_proved":["RH","global K3 positivity","all cutoff cells",
                           "Lean validated numerical certificate"]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(payload,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"gate":payload["gate"],"tested":len(result),
                      "required":len(boxes),"RH":RH_STATUS}))
    return 0   # Research status is represented in JSON, not by exit code.


if __name__=="__main__":
    raise SystemExit(main())
