"""R002-D bridge check v2 (finite numerical diagnostic only).

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
import mpmath as mp

sys.path.insert(0, '/home/user/zeta-23-lean/research/RHRC/routes/R004_prolate_v2')
from run_commutator_gauntlet_v2 import (pole_component, arch_component,
                                        prime_component, q_basis, von_mangoldt)

mp.mp.dps = 20


def h_nm(n, m, z, L):
    f = lambda y: 2 * q_basis(n, m, float(y), L) * mp.cos(z * y)
    return mp.quad(f, [0, L])


def bracket(r):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * r / 2)) - mp.log(mp.pi)


def arch_lit(n, m, L, R=400, pieces=80):
    """(1/2pi) int_{-R}^{R} h(r) bracket(r) dr, h even => 2*int_0^R."""
    pts = [mp.mpf(k) * R / pieces for k in range(pieces + 1)]
    f = lambda r: h_nm(n, m, r, L) * bracket(r)
    tot = mp.quad(f, pts)
    return 2 * tot / (2 * mp.pi)


def zero_side(n, m, L, NZ):
    """sum over nontrivial zeros of h(gamma_rho); h real even => 2*sum_{gamma>0}."""
    tot = mp.mpf(0)
    for j in range(1, NZ + 1):
        g = mp.im(mp.zetazero(j))
        tot += 2 * h_nm(n, m, g, L)
    return tot


def main():
    for lam, N in [(2.0, 2), (3.0, 2)]:
        L = 2 * math.log(lam)
        print(f"\n===== lambda={lam}  L={L:.6f}  X=e^L={math.exp(L):.2f} =====")
        print(" (n,m)   arch_component     (1/2pi)Int h*bracket      ratio")
        for (n, m) in [(0, 0), (1, 0), (1, 1), (2, 1), (-1, 1), (2, -2)]:
            ac = arch_component(n, m, L)
            al = arch_lit(n, m, L)
            ratio = al / ac if abs(ac) > 1e-12 else mp.mpf('nan')
            print(f" ({n:2d},{m:2d}) {ac: .12f}   {mp.nstr(al, 12):>18}   {mp.nstr(ratio, 8)}")
    print("\n===== assembly test: zero-side Weil sum vs 2*M_nm =====")
    lam, L = 2.0, 2 * math.log(2.0)
    NZ = 200
    for (n, m) in [(0, 0), (1, 0), (1, 1)]:
        M = pole_component(n, m, L) - arch_component(n, m, L) - prime_component(n, m, L)
        zs = zero_side(n, m, L, NZ)
        print(f" (n,m)=({n},{m})  2*M_nm={2*M: .8f}   zero_sum({NZ})={mp.nstr(zs, 8)}"
              f"   diff={mp.nstr(zs - 2*M, 4)}")


if __name__ == '__main__':
    main()
