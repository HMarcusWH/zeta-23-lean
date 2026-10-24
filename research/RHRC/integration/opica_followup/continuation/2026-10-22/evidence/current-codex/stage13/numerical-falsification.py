# Numerical falsification for the sawtooth force (F1). Not interval certified (mpmath).
import mpmath as mp
mp.mp.dps = 30
fr = lambda x: x - mp.floor(x)
# (F1.3) Mellin identity at several strip points, cellwise with exact tail
def mellin(s, L=4000):
    tot = mp.quad(lambda x: x ** (-s), [0, 1])
    tot += mp.fsum(mp.quad(lambda x: (x - n) * x ** (-s - 1), [n, n + 1]) for n in range(1, L))
    # tail int_L^oo {x} x^(-s-1): {x} = 1/2 + B1, mean part exact, B1 part O(L^(-s-1))
    tot += mp.mpf(1) / 2 * L ** (-s) / s
    return tot
for s in [mp.mpf('0.5'), mp.mpc('0.3', '2.0'), mp.mpc('0.5', '14.134725141734693')]:
    m = mellin(s); z = -mp.zeta(s) / s
    print("s=%s  int {x}x^(-s-1) = %s   -zeta(s)/s = %s   |diff| = %s" % (mp.nstr(s, 8), mp.nstr(m, 10), mp.nstr(z, 10), mp.nstr(abs(m - z), 3)))
# exact finite cell identity at L = 1, 5, 40
for L in [1, 5, 40]:
    lhs = mp.quad(lambda x: 1, [0, 1]) + mp.fsum(mp.quad(lambda x: (x - n)**2 / x**2, [n, n + 1]) for n in range(1, L))
    rhs = 2*L - mp.harmonic(L) - 2*(L - 1)*mp.log(L) + 2*mp.loggamma(L)
    print("L=%3d  int_0^L {x}^2/x^2 = %s   closed form = %s" % (L, mp.nstr(lhs, 15), mp.nstr(rhs, 15)))
print("limit log(2pi) - gamma =", mp.nstr(mp.log(2*mp.pi) - mp.euler, 15))
# (F1.1) on a compact test: int w (phi' - phi/2) = sum n^(-1/2) phi(log n) - int e^(t/2) phi
a, c = mp.mpf('-0.7'), mp.mpf('1.9')   # contains log 1, log 2, ..., log 6
phi = lambda t: mp.exp(-1 / ((t - a) * (c - t))) if a < t < c else mp.mpf(0)
dphi = lambda t: phi(t) * (-(2*t - a - c) / ((t - a) * (c - t)) ** 2) if a < t < c else mp.mpf(0)
w = lambda t: mp.exp(-t / 2) * fr(mp.exp(t))
pts = [a] + [mp.log(n) for n in range(1, 7) if a < mp.log(n) < c] + [c]
lhs = mp.fsum(mp.quad(lambda t: w(t) * (dphi(t) - phi(t) / 2), [pts[i], pts[i+1]]) for i in range(len(pts) - 1))
atoms = mp.fsum(mp.mpf(n) ** (-0.5) * phi(mp.log(n)) for n in range(1, 7))
cont = mp.quad(lambda t: mp.exp(t / 2) * phi(t), [a, c])
print("compact test: <g,phi> = %s   sum n^(-1/2) phi(log n) - int e^(t/2) phi = %s   |diff| = %s" % (mp.nstr(lhs, 15), mp.nstr(atoms - cont, 15), mp.nstr(abs(lhs - atoms + cont), 3)))
print("              without atoms: %s ; with atom weights n^(+1/2): %s" % (mp.nstr(-cont, 8), mp.nstr(mp.fsum(mp.mpf(n) ** 0.5 * phi(mp.log(n)) for n in range(1, 7)) - cont, 8)))
