# Numerical falsification for the square defect (R2-S3) at the first zeta zero.
# Not interval certified (double precision grid, FFT autocorrelation, cutoff L).
import numpy as np, mpmath as mp
rho = complex(mp.zetazero(1)); kappa = rho * (1 - rho); b = 1/rho - 1/(1 - rho)
L, dx = 400.0, 0.0025
x = np.arange(-L, L + dx/2, dx)
ax = np.abs(x); n = np.floor(ax).astype(int)
N = int(L) + 2
k = np.arange(1, N + 1)
A = np.concatenate([[0], np.cumsum(k ** (rho - 1))]); B = np.concatenate([[0], np.cumsum(k ** (-rho))])
with np.errstate(divide='ignore', invalid='ignore'):
    S = np.where(n >= 1, ax ** (-rho) * A[n] - ax ** (rho - 1) * B[n], 0)
h = (1 - S / b).real   # on the critical line h is real
print("kappa =", kappa, " max|Im h| =", np.max(np.abs((1 - S / b).imag)))
norm2 = np.sum(h**2) * dx
# autocorrelation d = h * h - h^2 (h real and even)
m = len(x); F = np.fft.rfft(h, 2*m)
conv = np.fft.irfft(F * F, 2*m)[m//2: m//2 + m] * dx   # (h*h)(x) on the same grid (centered)
d = conv - h**2
i0 = m // 2
print("d(0) = %.6f   ||h||^2 - 1 = %.6f   (tail of ||h||^2 beyond L ~ 2 kappa^2/(240 L^3) negligible)" % (d[i0], norm2 - 1))
# anti-self-duality: <d, Gaussian> = 0 for the self-dual Gaussian e^{-pi x^2}
g = np.exp(-np.pi * x**2)
print("int d(x) e^{-pi x^2} dx = %.3e   (int |d| e^{-pi x^2} = %.3f)" % (np.sum(d * g) * dx, np.sum(np.abs(d) * g) * dx))
# S3.1 on a non-self-dual Gaussian phi = e^{-pi x^2 / a}, F phi = sqrt(a) e^{-pi a xi^2}
def tau(phi_vals, phi_fn):
    dens = np.sum((1 - h)**2 * phi_vals) * dx
    comb = sum(phi_fn(j) for j in range(-60, 61) if j != 0)
    return dens - comb
for a in [2.0, 0.3]:
    phi = lambda t, a=a: np.exp(-np.pi * t**2 / a)
    Fphi = lambda t, a=a: np.sqrt(a) * np.exp(-np.pi * a * t**2)
    lhs = tau(Fphi(x), Fphi) - tau(phi(x), phi)
    rhs = np.sum(d * phi(x)) * dx
    print("a=%.1f: tau(F phi) - tau(phi) = %.6f   int d phi = %.6f   |diff| = %.2e" % (a, lhs, rhs, abs(lhs - rhs)))
# positivity of d near 0 (inside the old gap)
for t in [0.0, 0.25, 0.5, 0.75]:
    j = i0 + int(round(t / dx))
    print("d(%.2f) = %.4f" % (t, d[j]))
# EXPERIMENTAL SIGNAL: the positive interval about 0 is short; first sign change of d on the grid
pos = d[i0:] > 0
j1 = int(np.argmin(pos)) if not pos.all() else None
if j1 is not None:
    print("first sign change of d at x ~ %.4f (grid step %.4f); 1/gamma = %.4f, pi/gamma = %.4f"
          % (x[i0 + j1], dx, 1 / rho.imag, np.pi / rho.imag))
# falsification: dropping the complex conjugation (h * h instead of h * conj h) is invisible here,
# because h is real on the critical line; the conjugation is exercised formally (A = 0 and complex A).
