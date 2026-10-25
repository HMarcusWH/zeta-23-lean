# EXPERIMENTAL SIGNAL (not a gate, not interval certified): the F2.4 norm formulas at the first zero,
# ||h||^2 = |kappa|^2 int d omega/|a-kappa|^2 and int x^2 |h'|^2 = |kappa|^2 int a d omega/|a-kappa|^2,
# compared with the R2-S2 values N_11 and Q_11 (numerical-falsification.log, L = 400). On the critical
# line the quotients are removable at xi = gamma (paper, remark after F2.5).
import mpmath as mp, sys
mp.mp.dps = 20
X = int(sys.argv[1]) if len(sys.argv) > 1 else 400
g = mp.zetazero(1).imag
kappa = mp.mpf(1)/4 + g**2
N_ref, Q_ref = mp.mpf('73.68138905'), mp.mpf('17319.71783')
zs = [mp.zetazero(k).imag for k in range(1, 40) if mp.zetazero(k).imag < X]
pts = sorted(set([mp.mpf(0)] + zs + [mp.mpf(t) for t in range(5, X + 1, 5)]))
def integ(f):
    return mp.fsum(mp.quad(f, [pts[i], pts[i+1]]) for i in range(len(pts) - 1))
z2 = lambda x: abs(mp.zeta(mp.mpf(1)/2 + 1j*x))**2
a = lambda x: x**2 + mp.mpf(1)/4
IN = integ(lambda x: z2(x) / (a(x) - kappa)**2) / mp.pi
IQ = integ(lambda x: a(x) * z2(x) / (a(x) - kappa)**2) / mp.pi
tailQ = (mp.log(X / (2*mp.pi)) + 2*mp.euler + 1) / X / mp.pi   # a/(a-kappa)^2 ~ 1/x^2
print("cutoff X = %d: kappa^2 int d omega/(a-kappa)^2 = %s vs N_11 = %s (ratio %s)"
      % (X, mp.nstr(kappa**2 * IN, 10), mp.nstr(N_ref, 10), mp.nstr(kappa**2 * IN / N_ref, 8)))
print("              kappa^2 int a d omega/(a-kappa)^2 = %s vs Q_11 = %s (ratio %s)"
      % (mp.nstr(kappa**2 * (IQ + tailQ), 10), mp.nstr(Q_ref, 10), mp.nstr(kappa**2 * (IQ + tailQ) / Q_ref, 8)))
