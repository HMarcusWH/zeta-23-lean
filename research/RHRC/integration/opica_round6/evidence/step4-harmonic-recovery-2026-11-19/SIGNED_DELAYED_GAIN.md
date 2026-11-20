# Each sign of the delayed gain detects the rightmost zero exponent

**DERIVED on paper.** Either sign alone in the positive arithmetic mean of delayed replays has exact exponent \((B-1/2)/4\) at every sufficiently large horizon, where \(B=\sup_\rho\Re\rho\). This strengthens the absolute-gain result by combining its finite source identity with the positive xi kernel. An independent cofinal subpower upper on one of these means is still needed to close Step 4.

Use the notation of [the delayed-gain proof](DELAYED_GAIN.md). In particular \(v(x)=\sum_{q\le x}\mu_6(q)g(x/q)\), \(g(y)=\mathbf1_{[1,1/a)}(y)\cos(2\pi c y)/y\), \(a=24/25,\ c=21/20\), and \(G(s)=\int_1^{1/a} g(y)y^{-s-1}dy\). Extend \(V(t)=v(e^t)\) by zero on \(t<0\). At a fixed nontrivial zero \(\rho=\beta+i\gamma\) of multiplicity \(l\), equation (3) of that proof gives at every sufficiently large \(T\)
\[
 \int_0^T |V(t)|dt\gg_\rho e^{\beta T}T^{\,l-1}.                         \tag{1}
\]

## Positivity and the two full histories

Let \(K\) be the strictly positive even kernel with bilateral Laplace transform \(\int_{\mathbb R} K(u)e^{-zu}du=\xi(1/2+z)\) and bound \(K(u)\ll\exp(-c_0 e^{2|u|})\). Put \(k(u)=e^{u/2}K(u)\); then \(k>0\), \(\int_\mathbb R k(u)e^{-su}du=\xi(s)\), and \(k(u)\ll\exp(-c_1 e^{2|u|})\) with some \(c_1>0\). This is the positive kernel already used with the integrated prime discrepancy. [Project kernel, normalization and bound](../step4-area-runs-2026-11-19/XI_AREA_ECHO.md) · [Rodgers and Tao, equations (1)–(3)](https://arxiv.org/pdf/1801.05914#page=2)

Take \(Y(t)=\int_\mathbb R k(t-u)V(u)du\). The elementary bound \(|V(u)|\ll e^u\) for \(u\ge0\) gives absolute convergence and also rapid decay as \(t\to-\infty\). For \(\Re s>1\), finite-source Dirichlet expansion followed by absolute convergence gives the bilateral transform
\[
 \int_\mathbb R e^{-st}Y(t)dt
 =\frac{\xi(s)G(s)}{\zeta(s)(1-2^{-s})(1-3^{-s})}
 =\frac{s(s-1)\pi^{-s/2}\Gamma(s/2)G(s)}
 {2(1-2^{-s})(1-3^{-s})}.                                               \tag{2}
\]
The last expression is analytic on \(\Re s>0\). On every compact vertical strip inside this half-plane the two inverse Euler factors are bounded, \(G\) is bounded by its compact defining integral, and the gamma factor decays exponentially in \(|\Im s|\) times a fixed power. Inverting (2) on a line \(>1\) and shifting to any fixed \(\epsilon>0\) therefore gives \(|Y(t)|\ll_\epsilon e^{\epsilon t}\). The inversion is pointwise since the convolution is continuous. In particular \(\int_{-\infty}^S |Y(t)|dt\ll_\epsilon e^{\epsilon S}\).

Write \(V_\pm(t)=[\pm V(t)]_+\). For \(T\) large put \(h=(\log T)/2+C\) with \(C\) a fixed constant chosen below, and set \(S=T-h\). Tonelli's theorem gives
\[
 J_\pm=\int_{-\infty}^{S}(k*V_\pm)(t)dt
 =\int_0^\infty V_\pm(u)\left(\int_{-\infty}^{S-u} k(v)dv\right)du .
\]
For \(0\le u\le S\) the inner mass is at least the positive constant \(\int_{-\infty}^0 k\). Thus \(J_++J_-\gg_\rho e^{\beta S} S^{l-1}\) by (1). Meanwhile \(|J_+-J_-|\le\int_{-\infty}^{S}|Y(t)|dt\ll_\epsilon e^{\epsilon S}\). Choose \(0<\epsilon<\beta\) once. Each \(J_\pm\) is then \(\gg_\rho e^{\beta S} S^{l-1}\).

To transfer the lower to the native history through \(T\), the contribution of **all** \(u>T\) in \(J_\pm\) is at most
\[
 C_1 e^T\int_0^\infty e^r\exp(-c_2e^{2(h+r)})\,dr
 \ll e^T\exp(-c_3e^{2h}).
\]
Here the integrated left tail of \(k\) satisfies the same double-exponential bound after decreasing its constant. Choose \(C\) with \(c_3e^{2C}>2\), so the displayed cost tends to zero. On \(u\le T\) the inner mass is at most \(\|k\|_1\). Substitution of \(S=T-(\log T)/2-C\) yields
\[
 \boxed{\quad
 \int_1^X[\pm v(y)]_+\,\frac{dy}{y}
 \gg_\rho X^\beta(\log X)^{l-1-\beta/2}
 \quad\text{for each sign, at every sufficiently large }X .
 \quad}                                                                \tag{3}
\]
The \(\beta/2\) log loss accounts for the finite terminal memory of the bilateral filter. This bound permits zeros on either side of the critical line and does not assume that \(B\) is attained.

## The finite positive mean for one sign

The unit-cell estimate \(v(y)=v(n)+O(1)\) for \(n\le y<n+1\) transfers (3) to \(\sum_{n\le X}[\pm v(n)]_+/n\), with additive \(O(\log(2X))\). Both sums are \(X^{B+o(1)}\) at every integer \(X\) by the earlier native upper and by taking \(\beta\) arbitrarily close to \(B\).

For each large \(n\) take \(m=1+\lfloor n^{1/4}\rfloor\), the complete signed middle \(R(n)\) of the fourth-root replay, and \(H_\mathbb N(u)=1+\max_{1\le j\le u}|v(j)|/\sqrt j\). Define \(G_\pm(n)=[\pm R(n)]_+/(\sqrt n\,H_\mathbb N(n/m))\), setting the finitely many small gains to zero. From \(R(n)=-v(n)+O(\sqrt n)\), positive-part contraction gives
\[
 \big|[\pm R(n)]_+-[\mp v(n)]_+\big|\ll\sqrt n .
\]
For \(b=B-1/2>0\), summing with \(1/n\) loses only \(O(\sqrt X)\), strictly smaller than \(X^{B+o(1)}\). As \(H_\mathbb N(n/m)\le X^{3b/4+o(1)}\) for \(n\le X\), this proves \(\sum_{n\le X}G_\pm(n)/\sqrt n\ge X^{1/2+b/4-o(1)}\) for each sign at every large \(X\). The earlier pointwise upper \(G_\pm(n)\le n^{b/4+o(1)}\) matches it. Terms \(n\le X^d\), \(d<1\) fixed, contribute at most \(X^{d(1/2+b/4)+o(1)}\) to the weighted sum. On the remaining range multiply by \(\sqrt n\ge X^{d/2}\); first take the lower limit in \(X\), then let \(d\uparrow1\). For \(b=0\) the baseline one and the pointwise upper suffice. Hence
\[
 \boxed{\quad
 1+X^{-1/2}\sum_{n\le X}G_\pm(n)/\sqrt n
 =X^{b/4+o(1)},\qquad
 1+X^{-1}\sum_{n\le X}G_\pm(n)=X^{b/4+o(1)}
 \quad}                                                                \tag{4}
\]
separately for each sign. In particular a proof that \(1+X^{-1}\sum_{n\le X}G_+(n)\le X^\eta\) at arbitrarily large integer \(X\) for every \(\eta>0\) suffices for RH. The same holds for \(G_-\). These are means over genuine signed replays with a finite native denominator. Their independent subpower bound, Step 4 and RH remain **OPEN**.
