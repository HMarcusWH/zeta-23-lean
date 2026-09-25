"""R002-D historical bridge diagnostic (post-268 portable replay).

The legacy conjecture quoted below is historical, not current authority.
The later canonical normalization includes a scalar correction; this script
retains the old diagnostic to expose that discrepancy, not to revive it.
The zero and archimedean tails remain uncertified. The only pass gate added
here is the independent finite transform regression. Original R=400,
80 panels and 200 positive zeros are retained by default.

Established in v1 (exact to 10 digits, all tested (n,m)):
    h_{nm}(i/2) + h_{nm}(-i/2) = 2 * pole_component(n,m,L)
    sum_k Lambda(k) k^{-1/2} (K(log k) + K(-log k)) = 2 * prime_component(n,m,L)
where K_{nm}(y) := q_basis(n,m,|y|,L) (even, supported |y| <= L) and
h_{nm}(z) = int K e^{izy} dy = 2 int_0^L q(n,m,y,L) cos(zy) dy.

Remaining: the archimedean channel.  Conjecture:
    (1/2pi) int h_{nm}(r) [Re psi(1/4 + i r/2) - log pi] dr = -2 * arch_component(n,m,L)
which would give the exact bridge
    Zero-side Weil sum  sum_rho m_rho h_{nm}(gamma_rho)
      = Pole_lit - Prime_lit + Arch_lit
      = 2*(pole - prime - arch) ... sign check below
      = 2 * M_{nm}.
Careful quadrature: h decays like 1/r^2 (K continuous, piecewise C^1),
bracket grows like log r.  Integrate on a finite window with a tail estimate.
"""
import math, sys
from pathlib import Path
from functools import lru_cache
import argparse
import json
import mpmath as mp

ROUTES = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUTES / "R004_prolate_v2"))
sys.path.insert(0, str(ROUTES / "R003_ccm_bridge"))
from finite_transform_quadrature import h_mp, finite_arch_integral, validate_transform
from run_commutator_gauntlet_v2 import (pole_component, arch_component,
                                        prime_component, q_basis, von_mangoldt)

mp.mp.dps = 20


def h_nm(n, m, z, L):
    return h_mp(n, m, z, L)


def bracket(r):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * r / 2)) - mp.log(mp.pi)


def arch_lit(n, m, L, R=400, pieces=80):
    """(1/2pi) int_{-R}^{R} h(r) bracket(r) dr, h even => 2*int_0^R."""
    value, _estimated_error = finite_arch_integral(n, m, float(L), float(R), pieces)
    return mp.mpf(value)


@lru_cache(maxsize=None)
def zero_ordinate(j):
    return mp.im(mp.zetazero(j))


def zero_side(n, m, L, NZ):
    """sum over nontrivial zeros of h(gamma_rho); h real even => 2*sum_{gamma>0}."""
    tot = mp.mpf(0)
    for j in range(1, NZ + 1):
        g = zero_ordinate(j)
        tot += 2 * h_nm(n, m, g, L)
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zero-count", type=int, default=200)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if args.zero_count < 1:
        ap.error("zero-count must be positive")
    validations = [validate_transform(2*math.log(lam)) for lam in (2.,3.)]
    arch_rows, zero_rows = [], []
    for lam, N in [(2.0, 2), (3.0, 2)]:
        L = 2 * math.log(lam)
        print(f"\n===== lambda={lam}  L={L:.6f}  X=e^L={math.exp(L):.2f} =====")
        print(" (n,m)   arch_component     (1/2pi)Int h*bracket      ratio")
        for (n, m) in [(0, 0), (1, 0), (1, 1), (2, 1), (-1, 1), (2, -2)]:
            ac = arch_component(n, m, L)
            al = arch_lit(n, m, L)
            arch_rows.append({"lambda":lam,"n":n,"m":m,"arch_component":ac,
                              "finite_arch_integral":float(al),"R":400,"pieces":80})
            ratio = al / ac if abs(ac) > 1e-12 else mp.mpf('nan')
            print(f" ({n:2d},{m:2d}) {ac: .12f}   {mp.nstr(al, 12):>18}   {mp.nstr(ratio, 8)}")
    print("\n===== assembly test: zero-side Weil sum vs 2*M_nm =====")
    lam, L = 2.0, 2 * math.log(2.0)
    NZ = args.zero_count
    for (n, m) in [(0, 0), (1, 0), (1, 1)]:
        M = pole_component(n, m, L) - arch_component(n, m, L) - prime_component(n, m, L)
        zs = zero_side(n, m, L, NZ)
        zero_rows.append({"n":n,"m":m,"legacy_twice_M":2*M,
                          "finite_zero_sum":float(zs),"zero_count":NZ,
                          "difference":float(zs-2*M)})
        print(f" (n,m)=({n},{m})  2*M_nm={2*M: .8f}   zero_sum({NZ})={mp.nstr(zs, 8)}"
              f"   diff={mp.nstr(zs - 2*M, 4)}")

    result = {"status":"EXECUTED", "claim_cap":"FINITE_DIAGNOSTIC_NOT_A_BRIDGE_PROOF",
              "normalization_warning":"Legacy WeilGram=2*M conjecture omits the later scalar correction; see R003 CCM_NORMALIZATION_LOCK_v1.json",
              "tail_status":"BOTH_ZERO_AND_ARCHIMEDEAN_TAILS_UNCERTIFIED",
              "transform_validations":validations,"arch_rows":arch_rows,"zero_rows":zero_rows}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("transform_validations",)},indent=2))


if __name__ == '__main__':
    main()
