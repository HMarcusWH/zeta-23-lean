# Numerical falsification for the generic forced profile (F3, BoundaryAmplitude) at generic
# parameters (not zeros of zeta), where kappa = rho(1 - rho) is nonreal and off the cut.
# Not interval certified (mpmath cell quadrature to L with analytic power tails).
#   (1) the growing homogeneous parts cancel: h = 1 - S/b is not L2 at infinity, h~ = h - A x^(rho-1) is;
#   (2) the tail h~ = -(zeta(1-rho)/b) x^(-rho) + kappa B2({x})/(2 x^2) + O(x^-3);
#   (3) the F2 quotient off the cut: F_log psi~(xi) = int_0^oo h~(x) x^(-1/2 - i xi) dx equals
#       kappa zeta(1/2 + i xi)/(a(xi) - kappa), computed directly from the finite sums;
#   (4) falsification: the transform of h (without the boundary term) does not converge -- its
#       truncations drift from the quotient like |A| X^(Re rho - 1/2)/|rho - s| -- and the plateau
#       fails (h~ != 1 on (0, 1)) because zeta(rho) != 0.
import mpmath as mp, sys
mp.mp.dps = 15
L = int(sys.argv[1]) if len(sys.argv) > 1 else 200
for rho in [mp.mpc(0.75, 10), mp.mpc(0.6, 3)]:
    kappa = rho * (1 - rho); b = (1 - 2*rho) / kappa
    A = mp.zeta(rho) / b
    c = -mp.zeta(1 - rho) / b
    Asum = [mp.mpc(0)] * (L + 2); Bsum = [mp.mpc(0)] * (L + 2)
    for k in range(1, L + 2):
        Asum[k] = Asum[k-1] + mp.mpf(k) ** (rho - 1); Bsum[k] = Bsum[k-1] + mp.mpf(k) ** (-rho)
    S = lambda n, x: mp.mpc(0) if n == 0 else x ** (-rho) * Asum[n] - x ** (rho - 1) * Bsum[n]
    h = lambda n, x: 1 - S(n, x) / b
    ht = lambda n, x: h(n, x) - A * x ** (rho - 1)
    print("rho = %s: kappa = %s, |zeta(rho)| = %s, boundary amplitude A = zeta(rho)/b = %s"
          % (mp.nstr(rho, 6), mp.nstr(kappa, 8), mp.nstr(abs(mp.zeta(rho)), 6), mp.nstr(A, 8)))
    # (4a) plateau fails
    print("  plateau: h~(1/2) = %s (1 - A 2^(1-rho) = %s), not 1" % (mp.nstr(ht(0, mp.mpf(0.5)), 8),
          mp.nstr(1 - A * mp.mpf(0.5) ** (rho - 1), 8)))
    # (1) L2 growth: int_1^X |h|^2 vs |h~|^2
    for X in [50, L]:
        Ih = mp.fsum(mp.quad(lambda x: abs(h(n, x))**2, [n, n + 1]) for n in range(1, X))
        It = mp.fsum(mp.quad(lambda x: abs(ht(n, x))**2, [n, n + 1]) for n in range(1, X))
        print("  int_1^%d |h|^2 = %s (grows like X^(2 Re rho - 1)),  int_1^%d |h~|^2 = %s" % (X, mp.nstr(Ih, 8), X, mp.nstr(It, 8)))
    # (2) tail
    for x in [mp.mpf('10.3'), mp.mpf('50.7'), mp.mpf('190.2')]:
        n = int(mp.floor(x))
        u = x - n; B2 = u**2 - u + mp.mpf(1)/6
        res = ht(n, x) - (c * x ** (-rho) + kappa * B2 / (2 * x**2))
        print("  tail x = %6s: h~ = %s, residual * x^3 = %s" % (mp.nstr(x, 5), mp.nstr(ht(n, x), 8), mp.nstr(abs(res) * x**3, 6)))
    # (3) the quotient
    def cells(f, s, X):
        return mp.fsum(mp.quad(lambda x: f(n, x) * x ** (-s), [n, n + 1]) for n in range(1, X))
    for xi in [mp.mpf(0), mp.mpf(4), mp.mpf(9.5), mp.mpf(17)]:
        s = mp.mpf(1)/2 + 1j * xi
        q = kappa * mp.zeta(s) / (xi**2 + mp.mpf(1)/4 - kappa)
        # h~: exact head on (0, 1), cells to L, analytic tail of the retained term c x^(-rho)
        Ft = 1 / (1 - s) - A / (rho - s) + cells(ht, s, L) + c * mp.mpf(L) ** (1 - rho - s) / (rho + s - 1)
        # control: truncated transforms of h on (0, X), no tail (the integral does not converge)
        d50 = abs(1 / (1 - s) + cells(h, s, 50) - q)
        dL = abs(1 / (1 - s) + cells(h, s, L) - q)
        pred = abs(A) * mp.mpf(L) ** (rho.real - mp.mpf(1)/2) / abs(rho - s)
        print("  (3) xi = %5s: F_log psi~ = %s, kappa zeta/(a - kappa) = %s, rel diff %s;  control h truncated at 50 / %d: |diff| = %s / %s (predicted drift scale %s)"
              % (mp.nstr(xi, 4), mp.nstr(Ft, 8), mp.nstr(q, 8), mp.nstr(abs(Ft - q) / abs(q), 3), L,
                 mp.nstr(d50, 4), mp.nstr(dL, 4), mp.nstr(pred, 4)))
