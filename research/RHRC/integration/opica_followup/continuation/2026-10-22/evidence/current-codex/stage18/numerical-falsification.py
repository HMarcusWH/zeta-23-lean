"""R2-H1 numerical falsification (mpmath, not interval certified).

At the first zeta zero rho0 (simple, m = 1), kappa0 = rho0 (1 - rho0):
(1) the kappa-family g_kappa(y) = kappa sum_(k <= y) e^(-u/2)/k Sh(1/4 - kappa, u) equals S_rho(y)/b_rho;
(2) the order-zero jet tail: g_kappa0(y) - (1 - kappa0 B2({y})/(2 y^2)) = O(y^-3);
(3) sharpness beyond the multiplicity (k = 1 = m): the first kappa-jet of the density has the
    predicted power-term derivative of size y^(-1/2), so the O(y^-2) tail claimed for k < m fails here;
    the first jet of the construction on a gap test is A'(kappa0) H(rho0) != 0 (gap lost);
(4) the differentiated forced chain for h1 = -d/dkappa g at kappa0: on a cell
    -(x^2 h1')' - kappa0 h1 = h0 - 1, and x^2 h1' jumps by -1 at each integer;
(5) the two branches through rho0 and 1 - rho0 are reflections of each other.
"""
import mpmath as mp
mp.mp.dps = 30

rho0 = mp.zetazero(1)
tau0 = rho0 - mp.mpf(1) / 2
kap0 = rho0 * (1 - rho0)

def Sh(w, u):
    if w == 0:
        return mp.mpf(u)
    s = mp.sqrt(w)
    return mp.sinh(s * u) / s

def g(kap, y):
    y = abs(mp.mpf(y))
    tot = 0
    for k in range(1, int(mp.floor(y)) + 1):
        u = mp.log(y / k)
        tot += mp.exp(-u / 2) / k * Sh(mp.mpf(1) / 4 - kap, u)
    return kap * tot

def S(rho, y):
    N = int(mp.floor(y))
    A = mp.fsum(mp.power(n, rho - 1) for n in range(1, N + 1))
    B = mp.fsum(mp.power(n, -rho) for n in range(1, N + 1))
    return mp.power(y, -rho) * A - mp.power(y, rho - 1) * B

def b(rho):
    return (1 - 2 * rho) / (rho * (1 - rho))

def B2(y):
    f = y - mp.floor(y)
    return f * f - f + mp.mpf(1) / 6

def branch(r0, kap):
    t0 = r0 - mp.mpf(1) / 2
    return mp.mpf(1) / 2 + t0 * mp.sqrt(1 + (r0 * (1 - r0) - kap) / t0 ** 2)

print('rho0 =', mp.nstr(rho0, 15), ' kappa0 =', mp.nstr(kap0, 15))
zp = mp.zeta(rho0, derivative=1)
print('|zeta(rho0)| =', mp.nstr(abs(mp.zeta(rho0)), 3), ' zeta\'(rho0) =', mp.nstr(zp, 10), ' (simple zero, m = 1)')

print('(1) family identity g_kappa(y) = S_rho(y)/b_rho at a generic parameter rho = 0.7 + 5i')
rg = mp.mpc(0.7, 5)
for y in [1.5, 7.3, 42.9]:
    d = g(rg * (1 - rg), y) - S(rg, y) / b(rg)
    print('  y = %6.1f: |g - S/b| = %s' % (y, mp.nstr(abs(d), 3)))

print('(2) order-zero jet tail at rho0: residual * y^3')
for y in [10.4, 55.7, 230.2, 900.6]:
    y = mp.mpf(y)
    r = g(kap0, y) - (1 - kap0 * B2(y) / (2 * y ** 2))
    print('  y = %7.1f: |residual| * y^3 = %s' % (y, mp.nstr(abs(r) * y ** 3, 6)))

print('(3) beyond the multiplicity (k = 1 = m): first kappa-jet of the density')
dr = -1 / (2 * tau0)                        # d rho / d kappa at kappa0
zp1 = mp.zeta(1 - rho0, derivative=1)
b0 = b(rho0)
for y in [10.4, 55.7, 230.2]:
    y = mp.mpf(y)
    j1 = mp.diff(lambda kk: g(kk, y), kap0)
    dT = (-zp1 * dr * mp.power(y, -rho0) - zp * dr * mp.power(y, rho0 - 1)) / b0
    pred = dT - B2(y) / (2 * y ** 2)
    print('  y = %6.1f: |jet1| * y^(1/2) = %s   |jet1 - (dT - B2/(2y^2))| * y^3 = %s' % (
        y, mp.nstr(abs(j1) * mp.sqrt(y), 6), mp.nstr(abs(j1 - pred) * y ** 3, 6)))
A1 = zp * dr / b0
phi = lambda x: mp.exp(-1 / (1 - 4 * x * x)) if abs(x) < mp.mpf(1) / 2 else mp.mpf(0)
H0 = 2 * mp.quad(lambda x: mp.power(x, rho0 - 1) * phi(x), [0, mp.mpf(1) / 4, mp.mpf(1) / 2])
print('  gap test supported in (-1/2, 1/2): first construction jet A\'(kappa0) H(rho0) =', mp.nstr(A1 * H0, 8),
      ' |.| =', mp.nstr(abs(A1 * H0), 4), '(nonzero: the gap is lost at k = m)')

print('(4) differentiated forced chain for h1 = -d g/d kappa at kappa0')
h0 = lambda x: 1 - g(kap0, x)
h1 = lambda x: -mp.diff(lambda kk: g(kk, x), kap0)
for x in [mp.mpf('2.37'), mp.mpf('5.61')]:
    q = lambda t: t ** 2 * mp.diff(h1, t)
    lhs = -mp.diff(q, x) - kap0 * h1(x)
    print('  x = %s: |-(x^2 h1\')\' - kappa0 h1 - (h0 - 1)| = %s' % (mp.nstr(x, 4), mp.nstr(abs(lhs - (h0(x) - 1)), 3)))
for n in [2, 5]:
    e = mp.mpf('1e-8')
    dl = mp.diff(h1, n - e)
    dr_ = mp.diff(h1, n + e)
    print('  n = %d: jump of x^2 h1\' = %s (predicted -1)' % (n, mp.nstr(n ** 2 * (dr_ - dl), 8)))

print('(5) reflected branch: rho(kappa) through 1 - rho0 equals 1 - rho(kappa) through rho0')
for dk in [mp.mpc(0.3, 0.1), mp.mpc(-1.2, 0.7)]:
    kk = kap0 + dk
    print('  kappa0 + %s: |branch(1 - rho0) - (1 - branch(rho0))| = %s, kappa(branch) - kappa = %s' % (
        mp.nstr(dk, 3), mp.nstr(abs(branch(1 - rho0, kk) - (1 - branch(rho0, kk))), 3),
        mp.nstr(abs(branch(rho0, kk) * (1 - branch(rho0, kk)) - kk), 3)))
