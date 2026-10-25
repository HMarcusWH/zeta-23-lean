import mpmath as mp
mp.mp.dps = 30
def fr(x): return x - mp.floor(x)
def B1(x): return fr(x) - mp.mpf(1)/2
def B2(x): u = fr(x); return u*u - u + mp.mpf(1)/6
def B3(x): u = fr(x); return u**3 - mp.mpf(3)/2*u*u + u/2
def S(s, x): return mp.fsum(mp.mpf(n)**(-s) for n in range(1, int(mp.floor(x))+1))
def tail(s, x, N=600):
    # ∫_x^∞ B3(t) t^(-s-3) dt, exact cells up to N, then neglected tail (|.| ≤ 0.05 N^(-σ-2)/(σ+2))
    pts = [x] + [mp.mpf(k) for k in range(int(mp.floor(x))+1, N+1)]
    tot = mp.mpf(0)
    for a, b in zip(pts[:-1], pts[1:]):
        n = int(mp.floor(a))
        tot += mp.quad(lambda t: ((t-n)**3 - mp.mpf(3)/2*(t-n)**2 + (t-n)/2) * t**(-s-3), [a, b])
    return tot
def R(s, x): return -(s*(s+1)/6)*B3(x)*x**(-s-2) + s*(s+1)*(s+2)/6*tail(s, x)
def main_terms(s, x):
    return mp.zeta(s) + x**(1-s)/(1-s) - B1(x)*x**(-s) - s*B2(x)*x**(-s-1)/2
worst = 0
for s in [mp.mpf(1)/2, mp.mpc(0.3, 14), mp.mpc(0.8, -3.5), mp.mpf(2), mp.mpc(0.5, 21.022)]:
    for x in [mp.mpf(1), mp.mpf(7.5), mp.mpf(10), mp.mpf(10) - mp.mpf('1e-12'), mp.mpf(23.3)]:
        lhs = S(s, x); rhs = main_terms(s, x) + R(s, x)
        err = abs(lhs - rhs); worst = max(worst, err)
        C = abs(s)*(abs(s)+1)/6 + abs(s)*(abs(s)+1)*(abs(s)+2)/12
        bound_ok = abs(R(s, x)) <= C * x**(-mp.re(s)-2) + mp.mpf('1e-8')
        print(f"s={mp.nstr(s,6):>18} x={mp.nstr(x,14):>16} |lhs-rhs|={mp.nstr(err,3):>9} |R|={mp.nstr(abs(R(s,x)),4):>10} boundOK={bound_ok}")
print("worst identity error", mp.nstr(worst, 3))
print("R(1/2,1) =", mp.nstr(R(mp.mpf(1)/2, mp.mpf(1)), 10), " predicted 1-zeta(1/2)-5/2+1/24 =", mp.nstr(1-mp.zeta(0.5)-2.5+mp.mpf(1)/24, 10))
# left-endpoint falsification: with the left-closed sum the identity fails at integers
s = mp.mpc(0.3, 14); x = mp.mpf(10)
print("left-closed sum error at x=10:", mp.nstr(abs(S(s, x) - 10**(-s) - main_terms(s, x) - R(s, x)), 4))
# S_rho tail at the first actual zero
rho = mp.zetazero(1)
b = 1/rho - 1/(1-rho)
for x in [mp.mpf(5.5), mp.mpf(20.25), mp.mpf(80.7), mp.mpf(300.1)]:
    Srho = x**(-rho)*S(1-rho, x) - x**(rho-1)*S(rho, x)
    d = Srho - b - (2*rho-1)*B2(x)/(2*x**2)
    print(f"rho1: x={mp.nstr(x,6):>8} |S-b-(2rho-1)B2/(2x^2)|*x^3 = {mp.nstr(abs(d)*x**3,6)}")
