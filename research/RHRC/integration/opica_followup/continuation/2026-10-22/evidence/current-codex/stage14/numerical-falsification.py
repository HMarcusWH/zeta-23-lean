# Numerical falsification for the arithmetic Stieltjes function (F2, WeightedSpectralMeasure).
# Not interval certified: mpmath zeta on shared Gauss-Legendre nodes over |xi| < X, mean-value tail beyond X.
import sys
import numpy as np
import mpmath as mp
mp.mp.dps = 15
X = int(sys.argv[1]) if len(sys.argv) > 1 else 400
nodes, weights = np.polynomial.legendre.leggauss(24)
xs, ws = [], []
for k in range(X):                      # [k, k+1], k = 0..X-1, even integrand doubled
    xs.extend(k + (nodes + 1) / 2); ws.extend(weights / 2)
xs, ws = np.array(xs), np.array(ws)
z2 = np.array([float(abs(mp.zeta(mp.mpf(0.5) + 1j * mp.mpf(x))) ** 2) for x in xs])
dens = z2 / (2 * np.pi)                 # d omega / d xi
a = xs ** 2 + 0.25
def integ(f):                           # int over R of f(xi) d omega(xi), f even in xi
    return 2 * np.sum(ws * dens * f)
tail_inv_a = (np.log(X / (2 * np.pi)) + 2 * np.euler_gamma + 1) / X / np.pi   # int_{|xi|>X} d omega / xi^2
budget = np.log(2 * np.pi) - np.euler_gamma
print("cutoff X = %d, %d nodes" % (X, len(xs)))
print("weighted moment int d omega/a = %.10f (+ tail %.2e) vs log(2 pi) - gamma = %.10f"
      % (integ(1 / a) + tail_inv_a, tail_inv_a, budget))
def M(k):
    return integ(1 / (a - k)) + tail_inv_a
for k in [-1.0 + 0j, 1j, 1 + 5j, 0.2 + 0.01j, 200 + 3j]:
    m = M(k)
    s = integ(1 / np.abs(a - k) ** 2)
    print("kappa = %s: M = %s" % (k, np.round(m, 10)))
    if k.imag != 0:
        C = 1 + abs(k) / abs(k.imag)
        print("   Im M/Im kappa = %.10f vs int d omega/|a-kappa|^2 = %.10f  (diff %.1e)"
              % (m.imag / k.imag, s, abs(m.imag / k.imag - s)))
        print("   |M| = %.6f <= (1+|k|/|Im k|) budget = %.6f;  int d omega/|a-k|^2 = %.6f <= %.6f"
              % (abs(m), C * budget, s, C * budget / abs(k.imag)))
        print("   falsification: -int d omega/|a-k|^2 = %.6f has the wrong sign; |k|/|Im k| budget = %.6f"
              % (-s, abs(k) / abs(k.imag) * budget))
    h = 1e-4
    fd = (M(k + h) - M(k - h)) / (2 * h)
    print("   M'(kappa): finite difference %s vs int d omega/(a-kappa)^2 = %s"
          % (np.round(fd, 8), np.round(integ(1 / (a - k) ** 2), 8)))
