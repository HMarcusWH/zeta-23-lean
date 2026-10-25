import mpmath as mp
mp.mp.dps = 20
# Gaussian: f(t) = exp(-t^2); logFourier f(xi) = sqrt(pi) exp(-xi^2/4)
f = lambda t: mp.e**(-t*t)
lhs = mp.quad(lambda t: f(t)**2, [-mp.inf, mp.inf])
LF = lambda xi: mp.quad(lambda t: mp.e**(-1j*xi*t) * f(t), [-mp.inf, mp.inf])
print("Gaussian: logFourier(1.3) =", mp.nstr(LF(1.3), 12), " closed form", mp.nstr(mp.sqrt(mp.pi)*mp.e**(-1.69/4), 12))
rhs = mp.quad(lambda xi: abs(mp.sqrt(mp.pi)*mp.e**(-xi*xi/4))**2, [-mp.inf, mp.inf]) / (2*mp.pi)
print("Gaussian Plancherel: int|f|^2 =", mp.nstr(lhs, 12), " (1/2pi) int|LF|^2 =", mp.nstr(rhs, 12))
# F1.4 source budget: (1/2pi) int |zeta(1/2+i xi)|^2/(xi^2+1/4) = int_0^oo {x}^2/x^2 dx = log(2pi) - gamma
budget = mp.log(2*mp.pi) - mp.euler
w2 = 1 + mp.fsum(mp.quad(lambda x: (x - n)**2 / x**2, [n, n + 1]) for n in range(1, 4000)) + mp.mpf(1)/(3*4000)
print("||w||^2 (cells to 4000 + tail 1/(3L)) =", mp.nstr(w2, 10), " log(2pi)-gamma =", mp.nstr(budget, 10))
X = 400
zint = 2 * mp.quad(lambda xi: abs(mp.zeta(mp.mpf(1)/2 + 1j*xi))**2 / (xi*xi + mp.mpf(1)/4), mp.linspace(0, X, 81))
tail = 2 * mp.quad(lambda xi: (mp.log(xi/(2*mp.pi)) + 2*mp.euler) / (xi*xi), [X, mp.inf])
print("(1/2pi) int_|xi|<%d |zeta|^2/a = %s ; + mean-value tail estimate = %s" % (X, mp.nstr(zint/(2*mp.pi), 8), mp.nstr((zint + tail)/(2*mp.pi), 8)))
