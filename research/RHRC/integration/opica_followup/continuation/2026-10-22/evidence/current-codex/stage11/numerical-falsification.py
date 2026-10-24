# Numerical falsification for the forced Euler equation (R2-S1b) at the first zeta zero.
# Not interval certified (mpmath, tanh-sinh quadrature on cells).
import mpmath as mp
mp.mp.dps = 30
rho = mp.zetazero(1)
kappa = rho * (1 - rho)
b = 1/rho - 1/(1 - rho)
A = [mp.mpc(0)] * 12; B = [mp.mpc(0)] * 12
for k in range(1, 12):
    A[k] = A[k-1] + mp.mpf(k) ** (rho - 1)
    B[k] = B[k-1] + mp.mpf(k) ** (-rho)
def h_cell(n, x):
    return mp.mpc(1) if n == 0 else 1 - (x ** (-rho) * A[n] - x ** (rho - 1) * B[n]) / b
def dh_cell(n, x):
    if n == 0: return mp.mpc(0)
    return -(-rho * x ** (-rho - 1) * A[n] - (rho - 1) * x ** (rho - 2) * B[n]) / b
def bump(a, c):
    phi = lambda x: mp.exp(-1 / ((x - a) * (c - x))) if a < x < c else mp.mpf(0)
    dphi = lambda x: phi(x) * (-(2*x - a - c) / ((x - a) * (c - x)) ** 2) if a < x < c else mp.mpf(0)
    return phi, dphi
def cells(a, c):
    pts = [a] + [mp.mpf(n) for n in range(int(mp.ceil(a)), int(mp.floor(c)) + 1) if a < n < c] + [c]
    return [(pts[i], pts[i+1], int(mp.floor((pts[i] + pts[i+1]) / 2))) for i in range(len(pts) - 1)]
def run(a, c):
    a, c = mp.mpf(a), mp.mpf(c)
    phi, dphi = bump(a, c)
    psi = lambda x: x**2 * dphi(x)
    dpsi = lambda x: mp.diff(psi, x)
    lhs_ae = mp.fsum(mp.quad(lambda x: x**2 * dh_cell(n, x) * dphi(x), [l, r]) for l, r, n in cells(a, c))
    lhs_dist = -mp.fsum(mp.quad(lambda x: h_cell(n, x) * dpsi(x), [l, r]) for l, r, n in cells(a, c))
    cont = mp.fsum(mp.quad(lambda x: (h_cell(n, x) - 1) * phi(x), [l, r]) for l, r, n in cells(a, c))
    atoms = mp.fsum(phi(mp.mpf(n)) for n in range(1, 12))
    homog = mp.fsum(mp.quad(lambda x: h_cell(n, x) * phi(x), [l, r]) for l, r, n in cells(a, c))
    rhs = kappa * (cont + atoms)
    print("test on (%s, %s): atoms sum = %s" % (mp.nstr(a, 3), mp.nstr(c, 3), mp.nstr(atoms, 10)))
    print("  <x^2 h', phi'>      = %s" % mp.nstr(lhs_ae, 14))
    print("  -<h, (x^2 phi')'>    = %s" % mp.nstr(lhs_dist, 14))
    print("  kappa(<h-1,phi>+sum) = %s   |diff| = %s" % (mp.nstr(rhs, 14), mp.nstr(abs(lhs_ae - rhs), 3)))
    print("  without atoms        = %s   |diff| = %s" % (mp.nstr(kappa * cont, 10), mp.nstr(abs(lhs_ae - kappa * cont), 3)))
    print("  homogeneous kappa<h,phi> = %s   |diff| = %s" % (mp.nstr(kappa * homog, 10), mp.nstr(abs(lhs_ae - kappa * homog), 3)))
print("rho1 =", mp.nstr(rho, 12), " kappa =", mp.nstr(kappa, 12))
run('0.6', '3.7')   # three atoms
run('1.2', '1.9')   # inside one cell: no atom
run('2.5', '6.4')   # four atoms, far cells
# shrinking scaled bumps at 1, phi_w(x) = Phi((x-1)/w), Phi(u) = exp(1 - 1/(1-u^2)), phi_w(1) = 1:
# <x^2 h', phi_w'> = kappa <h-1, phi_w> + kappa, and the continuum term -> 0, so the atom kappa survives
Phi = lambda u: mp.exp(1 - 1 / (1 - u**2)) if abs(u) < 1 else mp.mpf(0)
dPhi = lambda u: Phi(u) * (-2*u / (1 - u**2)**2) if abs(u) < 1 else mp.mpf(0)
for w in ['0.4', '0.1', '0.02', '0.004']:
    w = mp.mpf(w)
    phi = lambda x: Phi((x - 1) / w); dphi = lambda x: dPhi((x - 1) / w) / w
    lhs = mp.fsum(mp.quad(lambda x: x**2 * dh_cell(n, x) * dphi(x), [l, r]) for l, r, n in cells(1 - w, 1 + w))
    cont = mp.fsum(mp.quad(lambda x: (h_cell(n, x) - 1) * phi(x), [l, r]) for l, r, n in cells(1 - w, 1 + w))
    print("bump at 1, radius %-6s: <x^2h',phi'> - kappa<h-1,phi> = %s (kappa = %s); kappa<h-1,phi> = %s" %
          (mp.nstr(w, 3), mp.nstr((lhs - kappa * cont).real, 14), mp.nstr(kappa.real, 14), mp.nstr((kappa * cont).real, 6)))
