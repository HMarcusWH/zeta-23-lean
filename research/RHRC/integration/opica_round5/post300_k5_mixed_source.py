#!/usr/bin/env python3
"""K=5 quartic-parity quotient / canonical-source probe (research only).

No proof of RH, no new Lean theorem, and no universal arithmetic estimate.
Uses the repository's production equation-(4.4) Arb backend. All sign
decisions come from outward Arb enclosures; floats never decide signs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

K = 5
BASE_COMMIT = "df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
SCHEMA = "RHRC_POST300_K5_MIXED_SOURCE_RESEARCH_V1"
CAP = "EXPERIMENTAL_SIGNAL_ONLY"
CENTER = {0: F(1), 1: -F(4,5), 2: F(2,5), 3: -F(4,35), 4: F(1,70), 5: F(0)}
ODD = {1: F(42), 2: F(-48), 3: F(27), 4: F(-8), 5: F(1)}
R003 = Path(__file__).resolve().parents[2] / "routes" / "R003_ccm_bridge"


def center(n: int) -> F:
    return CENTER[abs(n)]


def shift(n: int) -> F:
    # T(v)_n = n*v_n; both n and v change sign under reversal.
    return F(abs(n)) * ODD.get(abs(n), F(0))


def moment(f, degree: int) -> F:
    return sum((F(n**degree) * f(n) for n in range(-K, K+1)), F(0))


def gram_poly(f, g) -> tuple[F, F, F]:
    """Coefficients of beta^0,beta^1,beta^2 for D=(beta+n^2)."""
    terms = [(f(n)*g(n), n*n) for n in range(-K, K+1)]
    return (
        sum((a*j*j for a,j in terms), F(0)),
        sum((2*a*j for a,j in terms), F(0)),
        sum((a for a,j in terms), F(0)),
    )


def poly_mul(p, q):
    result = [F(0)] * (len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            result[i+j] += x*y
    return tuple(result)


def poly_sub(p, q):
    return tuple(x-y for x,y in zip(p,q))


def fstr(x: F) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def exact_geometry() -> dict:
    require(all(moment(center, r) == 0 for r in (0,2,4,6)),
            "center lift escaped even quartic seed")
    odd=lambda n: F(0) if n == 0 else (ODD[abs(n)] if n > 0 else -ODD[abs(n)])
    require(all(moment(odd, r) == 0 for r in (1,3,5,7)),
            "odd vector escaped odd quartic seed")
    require(all(moment(shift, r) == 0 for r in (0,2,4,6)),
            "odd-to-even moment shift failed")
    require(center(0) == 1 and shift(0) == 0,
            "center quotient frame degenerate")
    a, b, c = gram_poly(shift,shift), gram_poly(shift,center), gram_poly(center,center)
    require(a == tuple(F(44)*x for x in (43565,10426,845)),
            "odd-derived physical Gram polynomial mismatch")
    require(b == tuple(-F(88,35)*x for x in (1205,442,65)),
            "mixed physical Gram polynomial mismatch")
    require(c == tuple(F(33,2450)*x for x in (640,416,195)),
            "center lift physical Gram polynomial mismatch")
    det = poly_sub(poly_mul(a,c),poly_mul(b,b))
    require(det == tuple(F(3146,49)*x for x in (114400,124000,88785,16354,1105)),
            "physical Gram determinant polynomial mismatch")
    require(all(v > 0 for v in det),
            "physical Gram strict positivity failed")
    return {
        "K": K, "frame_order": ["T5_odd", "center_lift"],
        "moments": {"center_even_0_2_4_6": ["0"]*4, "odd_1_3_5_7": ["0"]*4},
        "gram_polynomials_ascending_beta": {
            "11": list(map(fstr,a)), "12": list(map(fstr,b)),
            "22": list(map(fstr,c)), "det": list(map(fstr,det))
        },
        "gram_determinant_coefficientwise_positive": True,
        "mixed_gram_strictly_negative_for_beta_positive": True,
        "center_eval": {"T5_odd": "0", "center_lift": "1"},
        "authority": "EXACT_RATIONAL_ALGEBRA_NOT_LEAN_PROOF",
    }

def _arb_backend():
    from flint import arb, arb_mat, ctx
    sys.path.insert(0, str(R003))
    import canonical_source_arb as ca
    from post247_remainder_budget_ratio_scout import planted_increment
    return arb, arb_mat, ctx, ca, planted_increment


def _record(z):
    if not z.is_finite():
        return {"sign": "UNRESOLVED_NONFINITE"}
    sign = ("CERTIFIED_POSITIVE" if bool(z > 0) else
            "CERTIFIED_NEGATIVE" if bool(z < 0) else
            "CERTIFIED_ZERO" if z.is_zero() else "UNRESOLVED_CONTAINS_ZERO")
    return {"sign":sign, "lower":z.lower().str(32,radius=False),
            "upper":z.upper().str(32,radius=False)}


def _dot(A, x, y, arb):
    return sum((x[i] * A[i,j] * y[j] for i in range(2*K+1) for j in range(2*K+1)), arb(0))


def _block(A, x, y, arb):
    a, b, c = _dot(A,x,x,arb),_dot(A,x,y,arb),_dot(A,y,y,arb)
    result = {"odd_derived": _record(a), "mixed": _record(b), "center": _record(c),
              "determinant": _record(a*c-b*b)}
    if bool(a > 0):
        s = c - b*b/a
        t = arb(1)/3
        bt, ct = b+t*a, c+2*t*b+t*t*a
        result["schur"] = _record(s)
        result["lift_invariance_residual"] = _record((ct-bt*bt/a)-s)
        result["schur_definition"] = "center - mixed^2 / odd_derived, only when odd_derived certified positive"
    else:
        result["schur"] = {"sign":"NOT_EVALUATED_ODD_DERIVED_NOT_CERTIFIED_POSITIVE"}
    return result


def probe(L_num:int=2,L_den:int=1,cutoff:int=7,prec:int=192,
          gamma_num:int=5,gamma_den:int=1,delta_num:int=1,delta_den:int=4) -> dict:
    if (L_num<=0 or L_den<=0 or cutoff<2 or prec<80 or
            gamma_num<=0 or gamma_den<=0 or delta_num<0 or delta_den<=0):
        raise ValueError("positive aperture, cutoff>=2 and precision>=80 required")
    arb,arb_mat,ctx,ca,planted_increment = _arb_backend()
    ca.set_precision(prec)
    L = ca.to_arb_rational(L_num,L_den)
    if not ca.fixed_cell_membership(cutoff,L)["certified"]:
        raise ValueError("requested Q is not the certified prime-power cutoff cell")
    beta=(L/(4*arb.pi()))**2
    idx=list(range(-K,K+1))
    x=[ca.to_arb_rational(shift(n).numerator,shift(n).denominator)*(beta+n*n) for n in idx]
    y=[ca.to_arb_rational(center(n).numerator,center(n).denominator)*(beta+n*n) for n in idx]
    M=ca.canonical_source_matrix(L,K,cutoff)
    G=arb_mat([[arb(1) if i==j else arb(0) for j in range(2*K+1)] for i in range(2*K+1)])
    atom_q=next((q for q in range(cutoff,1,-1)
                 if not ca.von_mangoldt(q).is_zero()),None)
    if atom_q is None:
        raise ValueError("no included prime-power atom available for control")
    weight=ca.von_mangoldt(atom_q)
    weight=weight/arb(atom_q).sqrt()
    atom=arb_mat([[weight*ca.q_basis(n,m,arb(atom_q).log(),L) for m in idx] for n in idx])
    # Removing the entering prime-power atom from the negative prime channel
    # adds back that atom. Modified weight adds a further -1/4 of the atom.
    gamma=ca.to_arb_rational(gamma_num,gamma_den)
    delta=ca.to_arb_rational(delta_num,delta_den)
    plant_on=planted_increment(L,K,gamma,arb(0))
    plant_off=planted_increment(L,K,gamma,delta)
    alternatives={
        "canonical":M,
        "entering_prime_removed":M+atom,
        "entering_prime_weight_plus_quarter":M-atom*(arb(1)/4),
        "synthetic_on_line":M-plant_on,
        "synthetic_off_line":M-plant_off,
    }
    out={}
    for name,A in alternatives.items():
        out[name]={"raw":_block(A,x,y,arb),
                   "epsilon_1_over_10":_block(A+G*(arb(1)/10),x,y,arb)}
    Gram=arb_mat([[arb(0) for _ in idx] for _ in idx])
    for i in range(len(idx)):Gram[i,i]=arb(1)
    gram=_block(Gram,x,y,arb)
    # No automatic source-sign promotion; all rows are finite experimental probes.
    return {
        "schema":SCHEMA, "claim_cap":CAP,"RH":"OPEN","Step4":"OPEN",
        "source_base_commit":BASE_COMMIT,
        "native_backend":"canonical_source_arb.canonical_source_matrix",
        "aperture":f"{L_num}/{L_den}","cutoff_Q":cutoff,
        "control_prime_power":atom_q,"gamma":f"{gamma_num}/{gamma_den}",
        "off_line_delta":f"{delta_num}/{delta_den}",
        "K":K,"precision_bits":prec,
        "physical_gram":gram,"controls":out,
        "synthetic_control_warning":"Planted zeros are not globally self-consistent alternate zeta functions.",
        "interpretation":"Finite Arb enclosures; absence of negative sign on this grid does not prove positivity or RH.",
    }


def main() -> int:
    p=argparse.ArgumentParser()
    p.add_argument("--exact-only",action="store_true")
    p.add_argument("--L-num",type=int,default=2)
    p.add_argument("--L-den",type=int,default=1)
    p.add_argument("--cutoff",type=int,default=7)
    p.add_argument("--precision",type=int,default=192)
    p.add_argument("--gamma-num",type=int,default=5)
    p.add_argument("--gamma-den",type=int,default=1)
    p.add_argument("--delta-num",type=int,default=1)
    p.add_argument("--delta-den",type=int,default=4)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    payload={"schema":SCHEMA, "claim_cap":CAP,"RH":"OPEN","Step4":"OPEN",
             "exact_geometry":exact_geometry()}
    if not args.exact_only:
        payload["finite_probe"]=probe(args.L_num,args.L_den,args.cutoff,args.precision,
            args.gamma_num,args.gamma_den,args.delta_num,args.delta_den)
    content=json.dumps(payload,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(content,encoding="utf-8")
    else:
        print(content,end="")
    return 0


if __name__=="__main__":
    raise SystemExit(main())
