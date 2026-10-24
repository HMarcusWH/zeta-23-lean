# Numerical falsification for the sampling compatibility law (R2-S2) at the first two zeta zeros.
# Not interval certified (mpmath; cell quadrature to L, Hurwitz-zeta tail for Q, leading tail for S).
# Usage: numerical-falsification.py L [L ...]; then three falsification checks run once.
import mpmath as mp
mp.mp.dps = 20
import sys
Ls = [int(a) for a in sys.argv[1:]] or [200, 400]
zs = [mp.zetazero(1), mp.zetazero(2)]
def make(rho, L):
    kappa = rho * (1 - rho); b = 1/rho - 1/(1 - rho)
    A = [mp.mpc(0)] * (L + 2); B = [mp.mpc(0)] * (L + 2)
    for k in range(1, L + 2):
        A[k] = A[k-1] + mp.mpf(k) ** (rho - 1); B[k] = B[k-1] + mp.mpf(k) ** (-rho)
    h = lambda n, x: mp.mpc(1) if n == 0 else 1 - (x ** (-rho) * A[n] - x ** (rho - 1) * B[n]) / b
    dh = lambda n, x: mp.mpc(0) if n == 0 else -(-rho * x ** (-rho - 1) * A[n] - (rho - 1) * x ** (rho - 2) * B[n]) / b
    return kappa, h, dh
def main(L):
    global P
    print("cutoff L =", L)
    P = [make(r, L) for r in zs]
    def gram(i, j):
        ki, hi, dhi = P[i]; kj, hj, dhj = P[j]
        N = mp.fsum(mp.quad(lambda x: hi(n, x) * mp.conj(hj(n, x)), [n, n + 1]) for n in range(L))
        Q = mp.fsum(mp.quad(lambda x: x**2 * dhi(n, x) * mp.conj(dhj(n, x)), [n, n + 1]) for n in range(L))
        # leading tail of Q: h' = kappa B1({x})/x^2 + O(x^-4), so x^2 h_i' conj h_j' = kappa_i conj kappa_j B1^2/x^2 + O(x^-4)
        # sum_{n >= L} int_0^1 (u - 1/2)^2 / (n + u)^2 du, expanded in Hurwitz zeta values (no cancellation)
        I = lambda m: mp.mpf(1)/(m + 3) - mp.mpf(1)/(m + 2) + mp.mpf(1)/(4*(m + 1))
        T = mp.fsum((-1)**m * (m + 1) * I(m) * mp.zeta(m + 2, L) for m in range(40))
        Q += ki * mp.conj(kj) * T
        return N, Q
    def sample(i):
        k, h, dh = P[i]
        S = mp.fsum(h(n, mp.mpf(n)) for n in range(1, L + 1))
        # tail: h(n) ~ kappa B2(0)/(2 n^2) = kappa/(12 n^2), sum_{n > L} 1/n^2 ~ 1/L - 1/(2L^2)
        return S + k / 12 * (1 / mp.mpf(L) - 1 / (2 * mp.mpf(L) ** 2))
    S = [sample(0), sample(1)]
    b = [s - mp.mpf(1)/2 for s in S]
    print("kappa_1 =", mp.nstr(P[0][0], 12), " kappa_2 =", mp.nstr(P[1][0], 12))
    print("b_1 =", mp.nstr(b[0], 10), " b_2 =", mp.nstr(b[1], 10))
    for i in range(2):
        for j in range(2):
            N, Q = gram(i, j)
            r1 = P[i][0] * (N + mp.conj(b[j])); r2 = mp.conj(P[j][0]) * (N + b[i])
            print("(i,j)=(%d,%d) N=%s Q=%s  |Q - k_i(N+conj b_j)|=%s  |Q - conj k_j(N+b_i)|=%s  L^2 |res|/|k_i k_j| = %s"
                  % (i+1, j+1, mp.nstr(N, 10), mp.nstr(Q, 10), mp.nstr(abs(Q - r1), 3), mp.nstr(abs(Q - r2), 3),
                     mp.nstr(L**2 * abs(Q - r1) / abs(P[i][0] * P[j][0]), 4)))
            if i == j:
                print("   Q_ii - N_ii/4 = %s (>= 0), N_ii = %s (> 0)" % (mp.nstr((Q - N/4).real, 10), mp.nstr(N.real, 10)))
    N12, _ = gram(0, 1)
    M = [b[0] / P[0][0], b[1] / P[1][0]]
    print("divided difference N_12/(k1 conj k2) = %s vs (M1 - conj M2)/(k1 - conj k2) = %s"
          % (mp.nstr(N12 / (P[0][0] * mp.conj(P[1][0])), 10), mp.nstr((M[0] - mp.conj(M[1])) / (P[0][0] - mp.conj(P[1][0])), 10)))


for L in Ls:
    main(L)

print("falsification 1: dropping the continuum term -1/2 (b = S instead of S - 1/2) at L = 200")
L = 200
P = [make(r, L) for r in zs]
k1, h1, dh1 = P[0]
N11 = mp.fsum(mp.quad(lambda x: h1(n, x) * mp.conj(h1(n, x)), [n, n + 1]) for n in range(L))
S1 = mp.fsum(h1(n, mp.mpf(n)) for n in range(1, L + 1)) + k1 / 12 * (1 / mp.mpf(L) - 1 / (2 * mp.mpf(L) ** 2))
Q11 = mp.fsum(mp.quad(lambda x: x**2 * dh1(n, x) * mp.conj(dh1(n, x)), [n, n + 1]) for n in range(L))
Im = lambda m: mp.mpf(1)/(m + 3) - mp.mpf(1)/(m + 2) + mp.mpf(1)/(4*(m + 1))
Q11 += k1 * mp.conj(k1) * mp.fsum((-1)**m * (m + 1) * Im(m) * mp.zeta(m + 2, L) for m in range(40))
print("  |Q_11 - k_1(N_11 + conj(S_1 - 1/2))| = %s;  |Q_11 - k_1(N_11 + conj S_1)| = %s (= |k_1|/2 = %s)"
      % (mp.nstr(abs(Q11 - k1 * (N11 + mp.conj(S1 - mp.mpf(1)/2))), 3), mp.nstr(abs(Q11 - k1 * (N11 + mp.conj(S1))), 10),
         mp.nstr(abs(k1) / 2, 10)))
print("  on-line zeros have real kappa and real b, so the conjugations in (S2.1) are not numerically visible here")

print("falsification 2: the paper's finite countercontrol h_i = kappa_i (A - kappa_i)^(-1) g with nonreal kappa")
a = [mp.mpf(1), mp.mpf(2), mp.mpf(3)]; g = [mp.mpf(1), mp.mpf(-1), mp.mpf(2)]
ks = [mp.mpc(1, 2), mp.mpc(0.5, -1), mp.mpc(-2, 0.25)]
hv = [[k * g[m] / (a[m] - k) for m in range(3)] for k in ks]
bv = [mp.fsum(g[m] * hv[i][m] for m in range(3)) for i in range(3)]
Nm = mp.matrix(3, 3); Qm = mp.matrix(3, 3); res = 0
for i in range(3):
    for j in range(3):
        Nm[i, j] = mp.fsum(hv[i][m] * mp.conj(hv[j][m]) for m in range(3))
        Qm[i, j] = mp.fsum(a[m] * hv[i][m] * mp.conj(hv[j][m]) for m in range(3))
        res = max(res, abs(Qm[i, j] - ks[i] * (Nm[i, j] + mp.conj(bv[j]))), abs(Qm[i, j] - mp.conj(ks[j]) * (Nm[i, j] + bv[i])))
eN = mp.eighe(Nm)[0]; eQ = mp.eighe(Qm)[0]
print("  max (S2.1) residual = %s; eig N = %s; eig Q = %s; Im kappa = %s"
      % (mp.nstr(res, 3), [mp.nstr(e, 6) for e in eN], [mp.nstr(e, 6) for e in eQ], [mp.nstr(k.imag, 3) for k in ks]))

print("falsification 3: without the zero hypothesis (rho = 3/4) the sample sum diverges")
rho = mp.mpf(3) / 4; bb = 1/rho - 1/(1 - rho)
for Lc in (100, 400, 1600):
    A = mp.mpf(0); B = mp.mpf(0); Ssum = mp.mpf(0)
    for n in range(1, Lc + 1):
        A += mp.mpf(n) ** (rho - 1); B += mp.mpf(n) ** (-rho)
        Ssum += 1 - (mp.mpf(n) ** (-rho) * A - mp.mpf(n) ** (rho - 1) * B) / bb
    print("  L = %d: sum_{n <= L} h(n) = %s, sum / L^(3/4) = %s" % (Lc, mp.nstr(Ssum, 8), mp.nstr(Ssum / mp.mpf(Lc) ** 0.75, 6)))
print("  predicted growth constant (4/3) zeta(3/4)/b = %s (h(n) ~ zeta(rho) n^(rho-1)/b)" % mp.nstr(mp.mpf(4) / 3 * mp.zeta(rho) / bb, 6))
