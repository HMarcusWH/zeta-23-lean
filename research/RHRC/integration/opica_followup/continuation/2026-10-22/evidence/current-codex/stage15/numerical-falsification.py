# Numerical falsification for the F2 native resolvent (NativeResolvent) at the first two zeta zeros.
# Not interval certified (mpmath cell quadrature to L with leading tails). The first zeros lie on the
# critical line, so kappa = 1/4 + gamma^2 is on the cut: the off-cut roots are not tested here. What
# is tested is everything the module proves for every actual zero in the strip:
#   (1) summation by parts b = sum h(n) - 1/2 = int_0^oo {x} h'(x) dx (cell endpoint terms);
#   (2) the same pairing in log variables, int w (psi' - psi/2) dt (independent t-quadrature);
#   (3) the H^-1-H^1 bound |b| <= ||w||_2 (int |psi'|^2 + 1/4 int |psi|^2)^(1/2) = sqrt((log 2pi - g) Q);
#   (4) the undivided Fourier identity (xi^2 + 1/4 - kappa) F_log psi(xi) = kappa zeta(1/2 + i xi),
#       with F_log psi(xi) = int_0^oo h(x) x^(-1/2 - i xi) dx computed from h directly;
# plus EXPERIMENTAL SIGNAL: the removable value F_log psi(gamma) = kappa i zeta'(1/2 + i gamma)/(2 gamma)
# and falsification controls (endpoint h(n), multiplier a + kappa).
import mpmath as mp, sys
mp.mp.dps = 15
L = int(sys.argv[1]) if len(sys.argv) > 1 else 200
zs = [mp.zetazero(1), mp.zetazero(2)]
def make(rho, L):
    kappa = rho * (1 - rho); b = 1/rho - 1/(1 - rho)
    A = [mp.mpc(0)] * (L + 2); B = [mp.mpc(0)] * (L + 2)
    for k in range(1, L + 2):
        A[k] = A[k-1] + mp.mpf(k) ** (rho - 1); B[k] = B[k-1] + mp.mpf(k) ** (-rho)
    h = lambda n, x: mp.mpc(1) if n == 0 else 1 - (x ** (-rho) * A[n] - x ** (rho - 1) * B[n]) / b
    dh = lambda n, x: mp.mpc(0) if n == 0 else -(-rho * x ** (-rho - 1) * A[n] - (rho - 1) * x ** (rho - 2) * B[n]) / b
    return kappa, h, dh
B0 = mp.log(2 * mp.pi) - mp.euler
print("cutoff L =", L, "; ||w||_2^2 = log(2 pi) - gamma =", mp.nstr(B0, 10))
for idx, rho in enumerate(zs):
    kappa, h, dh = make(rho, L)
    g = rho.imag
    print("zero %d: gamma = %s, kappa = %s (on the cut; off-cut roots not tested)" % (idx + 1, mp.nstr(g, 10), mp.nstr(kappa.real, 10)))
    # sample by the definition, with the Stage 12 tail kappa/12 (1/L - 1/(2L^2))
    S = mp.fsum(h(n, mp.mpf(n)) for n in range(1, L + 1)) + kappa / 12 * (1 / mp.mpf(L) - 1 / (2 * mp.mpf(L) ** 2))
    b = S - mp.mpf(1) / 2
    # (1) int_0^L {x} h'(x) dx cell by cell, tail int_L^oo {x} kappa ({x} - 1/2)/x^2 ~ kappa/(12 L) - kappa/(24 L^2)
    I1 = mp.fsum(mp.quad(lambda x: (x - n) * dh(n, x), [n, n + 1]) for n in range(1, L))
    I1 += kappa * (1 / (12 * mp.mpf(L)) - 1 / (24 * mp.mpf(L) ** 2))
    print("  (1) b = sum h(n) - 1/2 = %s;  int_0^oo {x} h' dx = %s;  |diff| = %s" % (mp.nstr(b.real, 10), mp.nstr(I1.real, 10), mp.nstr(abs(b - I1), 3)))
    # (2) log variables: w(t) (psi'(t) - psi(t)/2) = {e^t} e^t h'(e^t), t in [0, log L], same tail
    I2 = mp.fsum(mp.quad(lambda t: (mp.exp(t) - n) * mp.exp(t) * dh(n, mp.exp(t)), [mp.log(n), mp.log(n + 1)]) for n in range(1, L))
    I2 += kappa * (1 / (12 * mp.mpf(L)) - 1 / (24 * mp.mpf(L) ** 2))
    print("  (2) int w (psi' - psi/2) dt = %s;  |diff from b| = %s" % (mp.nstr(I2.real, 10), mp.nstr(abs(b - I2), 3)))
    # (3) H^-1-H^1 bound with Q = logForm = int x^2 |h'|^2 (leading tail kappa^2/(12 L))
    Q = mp.fsum(mp.quad(lambda x: x**2 * abs(dh(n, x))**2, [n, n + 1]) for n in range(1, L)) + abs(kappa)**2 / (12 * L)
    bound = mp.sqrt(B0 * Q)
    print("  (3) |b| = %s <= ||w|| sqrt(Q) = %s (Q = %s)" % (mp.nstr(abs(b), 8), mp.nstr(bound, 8), mp.nstr(Q, 10)))
    # (4) undivided Fourier identity, F_log psi(xi) = int_0^1 x^(-1/2-i xi) dx + sum_cells
    def Fpsi(xi):
        s = mp.mpf(1) / 2 + 1j * xi
        head = 1 / (1 - s)          # int_0^1 x^(-s) dx with h = 1 on (0, 1)
        return head + mp.fsum(mp.quad(lambda x: h(n, x) * x ** (-s), [n, n + 1]) for n in range(1, L))
    for xi in [mp.mpf(0), mp.mpf(5), mp.mpf(10), g + 3, mp.mpf(30)]:
        F = Fpsi(xi)
        lhs = (xi**2 + mp.mpf(1)/4 - kappa) * F
        rhs = kappa * mp.zeta(mp.mpf(1)/2 + 1j * xi)
        bad = (xi**2 + mp.mpf(1)/4 + kappa) * F
        print("  (4) xi = %6s: (a - kappa) F = %s, kappa zeta = %s, |diff|/|kappa zeta| = %s;  control (a + kappa) F: rel. diff %s"
              % (mp.nstr(xi, 5), mp.nstr(lhs, 8), mp.nstr(rhs, 8), mp.nstr(abs(lhs - rhs) / abs(rhs), 3), mp.nstr(abs(bad - rhs) / abs(rhs), 3)))
    Fg = Fpsi(g)
    pred = kappa * 1j * mp.zeta(mp.mpf(1)/2 + 1j * g, derivative=1) / (2 * g)
    print("  EXPERIMENTAL SIGNAL: at xi = gamma, F_log psi = %s vs removable value kappa i zeta'(rho)/(2 gamma) = %s (rel. diff %s)"
          % (mp.nstr(Fg, 8), mp.nstr(pred, 8), mp.nstr(abs(Fg - pred) / abs(pred), 3)))
    # falsification: endpoint h(n) instead of h(n + 1) in every cell
    Sbad = mp.fsum(h(n, mp.mpf(n)) for n in range(0, L)) - mp.fsum(mp.quad(lambda x: h(n, x), [n, n + 1]) for n in range(0, L))
    print("  falsification: endpoint h(n) in every cell gives %s, off from b by %s (h(0) = 1 enters)"
          % (mp.nstr(Sbad.real, 8), mp.nstr(abs(Sbad - I1), 6)))
