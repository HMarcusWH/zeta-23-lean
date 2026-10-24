# EXPERIMENTAL SIGNAL (not a gate, not interval certified): does the R2-S2 sample defect b of an
# actual on-line zero match kappa M(kappa), M(kappa) = (1/2pi) int |zeta(1/2+i xi)|^2/(xi^2+1/4-kappa) d xi
# (the F2 Stieltjes function, stated in the frozen contract only off the cut [1/4, oo))? On the
# critical line kappa = 1/4 + gamma^2 lies on the cut; the double zero of |zeta|^2 at xi = gamma
# cancels the pole, so the integral converges absolutely there.
import mpmath as mp, sys
mp.mp.dps = 20
Xs = [int(a) for a in sys.argv[1:]] or [400]
gam = [mp.zetazero(k).imag for k in (1, 2)]
b_ref = [mp.mpf('12.89968693'), mp.mpf('6.184275184')]   # L = 400 values from numerical-falsification.log
def M(g, X):
    kappa = mp.mpf(1)/4 + g**2
    f = lambda x: abs(mp.zeta(mp.mpf(1)/2 + 1j*x))**2 / (x**2 + mp.mpf(1)/4 - kappa)
    zs = [mp.zetazero(k).imag for k in range(1, 40) if mp.zetazero(k).imag < X]
    pts = sorted(set([mp.mpf(0)] + zs + [mp.mpf(t) for t in range(5, X + 1, 5)]))
    I = mp.fsum(mp.quad(f, [pts[i], pts[i+1]]) for i in range(len(pts) - 1))
    # mean-value tail for |zeta|^2 ~ log(x/2pi) + 2 gamma_E: int_X^oo (log(x/2pi) + 2 gamma_E)/x^2
    tail = (mp.log(X / (2*mp.pi)) + 2*mp.euler + 1) / X
    return kappa, (I + tail) / mp.pi
for X in Xs:
  print("cutoff X =", X, "(mean-value tail beyond X)")
  for g, bref in zip(gam, b_ref):
    kappa, m = M(g, X)
    print("gamma = %s kappa = %s: kappa M(kappa) = %s, sampled b = %s, ratio = %s"
        % (mp.nstr(g, 10), mp.nstr(kappa, 10), mp.nstr(kappa * m, 8), mp.nstr(bref, 10), mp.nstr(kappa * m / bref, 6)))
