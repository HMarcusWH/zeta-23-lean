import mpmath as mp
mp.mp.dps = 20
rho = mp.zetazero(1)
kappa = rho * (1 - rho)
b = 1/rho - 1/(1 - rho)
N = 600
A = [mp.mpc(0)] * (N + 2); B = [mp.mpc(0)] * (N + 2)
for k in range(1, N + 2):
    A[k] = A[k-1] + mp.mpf(k) ** (rho - 1)
    B[k] = B[k-1] + mp.mpf(k) ** (-rho)
def S_cell(n, x):
    return x ** (-rho) * A[n] - x ** (rho - 1) * B[n]
def h(x):
    x = abs(mp.mpf(x)); n = int(mp.floor(x))
    if n == 0: return mp.mpc(1)
    return 1 - S_cell(n, x) / b
def h_cell(n, x):
    return mp.mpc(1) if n == 0 else 1 - S_cell(n, x) / b
def B2(x):
    u = x - mp.floor(x); return u*u - u + mp.mpf(1)/6
# half-line integral, cell by cell
half = mp.fsum(mp.quad(lambda x: h_cell(n, x), [n, n + 1]) for n in range(0, N))
print("rho1 =", mp.nstr(rho, 12), " kappa =", mp.nstr(kappa, 12))
print("int_0^%d h = %s   (target 1/2; truncation O(N^-2))" % (N, mp.nstr(half, 10)))
# Fourier self-duality: Fh(xi) = 2 int_0^oo h(x) cos(2 pi x xi) dx for even h
for xi in [mp.mpf('0.4'), mp.mpf('1.7'), mp.mpf('3.25'), mp.mpf('6.6')]:
    F = 2 * mp.fsum(mp.quad(lambda x: h_cell(n, x) * mp.cos(2*mp.pi*x*xi), [n, n + 1]) for n in range(0, N))
    print("xi=%-5s Fh=%s  h=%s  |diff|=%s" % (mp.nstr(xi, 4), mp.nstr(F, 8), mp.nstr(h(xi), 8), mp.nstr(abs(F - h(xi)), 3)))
# jump of h' at n from one-sided cell derivatives (finite differences inside the cells)
for n in [1, 3, 10]:
    eps = mp.mpf('1e-8')
    dR = (h_cell(n, n + eps) - h_cell(n, n)) / eps
    dL = (h_cell(n - 1, mp.mpf(n)) - h_cell(n - 1, n - eps)) / eps
    print("n=%-3d (h'(n+) - h'(n-)) = %s   -kappa/n^2 = %s" % (n, mp.nstr(dR - dL, 8), mp.nstr(-kappa / n**2, 8)))
# tail
for x in [mp.mpf('5.5'), mp.mpf('20.25'), mp.mpf('80.7'), mp.mpf('300.1')]:
    d = h(x) - kappa * B2(x) / (2 * x**2)
    print("x=%-7s x^3 |h - kappa B2/(2x^2)| = %s" % (mp.nstr(x, 6), mp.nstr(abs(d) * x**3, 6)))
