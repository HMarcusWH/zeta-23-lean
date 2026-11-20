# A fixed contrast of complete dyadic prime windows sees every zeta zero

**DERIVED on paper, 19 November 2026.** Use the two existing distributed calibrations and their native arithmetic labels **before** adaptive selection. A fixed finite collection of outer-prime windows of ratio two, each extending past the first correction threshold \(2L\), cannot all have independently square-scale signed totals. This is a statement about full windows at the same real \(x\), including all calibration terms, primes, repeated factors and signs. There is also an obstruction involving only complete buffers with upper endpoints strictly between \(2L\) and \(3L\). Step 4 remains open.

## Two deterministic tests

Use \(L=\lfloor x^\lambda\rfloor\), with \(\lambda=.11\) for the factorial projection and \(\lambda=.37\) for the eta projection, and put \(P=x/L\). In each case write \(C(s)=1/H(s)=\sum c(n)n^{-s}\), with \(H=\zeta\) or \(H(s)=\zeta(s)\eta(2s)\eta(3s)\) respectively. The four exceptional terms at \(4^k R\) use the equal-weight average over integers \(2L<R\le3L,\ 9\mid R\). For a bounded test \(g\), the actual sum is

\[
 D_g(x)=\sum_{q\ {\rm prime}}(\log q)g(q/P)\sum_{j\le x/q}(x-qj)r_i(j).
\]

All \(q\) used below belong to the respective native outer range for large \(x\). These tests use the exact filters in [All prime cofactors](ALL_PRIME_COFACTORS.md), without using its data-dependent matching choices.

Take \(d=(3/2)^{1/10}\), \(t_j=d^{j+1}/3\), \(0\le j\le8\). Every \(t_j\) lies strictly between \(1/3\) and \(1/2\). Define the degree-seven real polynomial

\[
 B_0(z)=\prod_{\kappa\in(0,-1,2,2,3/2,1,4/3)}(z-d^{1-\kappa})
        =\sum_{j=0}^7 b_jz^j .
\]

Set \(G(t)=\sum_{j=0}^7 b_j\mathbf1_{[t_j,t_{j+1})}(t)\) and \(J(t)=G(t)-G(t/2)\). Write \(\Delta_j\) for the jumps of \(G\) at \(t_j\), including both outer endpoints. Then exactly

\[
 J(t)=\sum_{j=0}^8\Delta_j\,\mathbf1_{[t_j,2t_j)}(t).
\]

Each term in \(D_J\) is a full dyadic window \(Y=x/q\in(L/(2t_j),L/t_j]\). Independently, \(D_G\) is the sum with coefficients \(\Delta_j\) of the nine full buffers \(L\le Y\le L/t_j\). To see the latter, use \(G(t)=\sum_j\Delta_j\mathbf1_{[t_j,\infty)}(t)\), \(\sum_j\Delta_j=0\), and that the residual vanishes for \(Y\le L\). Thus the upper endpoints of *all* these buffers lie strictly between \(2L\) and \(3L\).

The two results are the following. Put \(\beta_*=\sup_{\zeta(\rho)=0,\ 0<\Re\rho<1}\Re\rho\) and assume \(\beta_*<1\), as given by the project's pinned ceiling. For each \(g=G,J\), with \(D_+=\max(D,0),\,D_-=\max(-D,0)\),

\[
 \limsup_{x\to\infty}\frac{\log(1+(D_g(x))_+)}{\log x}
 =\limsup_{x\to\infty}\frac{\log(1+(D_g(x))_-)}{\log x}
 =2-\lambda(1-\beta_*).                                                   \tag{1}
\]

In particular at least one fixed buffer in the stated list and at least one fixed dyadic window each has absolute limsup exponent at least the right-hand side. That exponent is at least \(1.945\) for the factorial filter and \(1.815\) for eta. The positive and negative sequences in (1) concern the contrasts. A specific individual window need not witness both. [Pinned input and prime/Mertens transfer](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)

## Undoing every distributed correction in the continuum

Define \(\Phi(v)=\int G(t)(1-vt)_+\,dt\). The geometric intervals give

\[
 \int G(t)t^{-s}dt=B_0(d^{1-s})\int_{t_0}^{t_1}t^{-s}dt,\qquad
 W(s)=\int_0^\infty\Phi(v)v^{s-1}dv=\frac{\int G(t)t^{-s}dt}{s(s+1)}.
\]

The last equality starts in \(\Re s>0\) by integration. The zero mass and zero first moment of \(G\), given by \(\kappa=0,-1\), imply \(\Phi(v)=0\) until the first ramp breakpoint and after the last, so its support lies in a compact subinterval of \((2,3)\). It is Lipschitz and \(W\) is entire. Its zeros include \(2\) to order at least two, \(3/2,1,4/3\). Moreover \(W\) is nonzero for every \(0<\Re s<1\). All roots of \(B_0(d^{1-s})\) have real part one of the listed \(\kappa\). The integral over a single interval can vanish only on \(\Re s=1\) by its explicit antiderivative.

Write \(h(n)\) for the coefficients of \(H\), so \(h(1)=h(2)=1\) for both choices. To evaluate the continuum source use the coefficient identity \(1-H D=H(C-D)\), where \(D\) agrees with \(C\) through \(L\), then has only its exceptional coefficients. Its coefficient at \(4^kR\) in the component for a fixed centre is \(-4^kR\,a_{k,R}\). In the continuum \(q\)-integral of \(D_G\), every ramp with product index \(j\) contributes \(xP\Phi(j/L)\). Since \(2<j/L<3\), the native tail \(h(m)c(n)\) with \(n>L\) can have only \(m=1,2\), and both resulting sums can be extended over all \(n\) by support. In the calibration correction only \(k=0,m=1\) can participate, with sign \(+R a_{0,R}\). This is the entire correction prefix, including every active \(9\)-divisible centre.

For both four-node systems the original moment equations give exactly

\[
 a_{0,R}=A_L+B_L\log(R/L)+E_L(R/L)^{-1/2}+F_L(R/L)^{-\gamma},
 \qquad \gamma=1\ {\rm or}\ 2/3
\]

respectively, with coefficients \(O(\log^2(2L))\). Indeed the fixed inverse has rows \(1,k,2^k,4^{\gamma k}\). The logarithmic equation has right side a scalar minus \(\log R\) times the value equation; the two power rows have fixed numerators divided by \(R^{1/2},R^\gamma\). Replacing \(R\) by \(L(R/L)\) gives the displayed span. The estimates follow from \(\sum_{n\le L}|c(n)|\ll L\) by partial summation in the four equations. This argument keeps the original interpolation values. [Factorial moment equations](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) · [Eta moment equations](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md)

Writing \(v=R/L\), the integral over \(2\le v\le3\) of \(v\,a_{0,Lv}\Phi(v)\), using the displayed expression to extend it to real \(v\), is exactly zero. The four relevant moments are \(W(2),W'(2),W(3/2),W(2-\gamma)\). Its Lipschitz norm is \(O_G(\log^2(2L))\). The average over the \(L/9+O(1)\) allowed integers therefore differs from the integral by \(O_G(\log^2(2L)/L)\) by the mesh-\(9/L\) Riemann estimate. The averaged term \(R a_{0,R}\Phi(R/L)\) contributes only \(O_G(\log^2(2L))\) inside the continuum sum. This is a quantified error for the actual discrete calibration.

For \(G(t/2)\) the ramp integral is \(2\Phi(2v)\), supported in \(1<v<3/2\). The native tail there has only \(m=1\) and no corrections. Thus the two continuum integrals are \(x^2 S_g(L)+O_G(x^2\log^2(2L)/L)\), where for any real \(y\ge1\)

\[
 S_G(y)=y^{-1}\sum_n c(n)\{\Phi(n/y)+\Phi(2n/y)\},\qquad
 S_J(y)=y^{-1}\sum_n c(n)\{\Phi(n/y)-\Phi(2n/y)\}.                       \tag{2}
\]

## Transfer to the true discrete primes and proof of the growth exponents

Take any \(\beta_*<v<1\). The external zero ceiling and the zero-free transfer give \(\vartheta(U)-U=O_v(U^v)\) and \(\sum_{n\le U}c(n)=O_v(U^v)\). For the latter on eta use \(c=\mu*d_0\), with \(d_0\) absolutely summable at every Dirichlet weight \(v>1/2\). The absolute sum of \(|c(n)|\) to \(U\) is \(O(U)\). On indices \(j\le3L\) the native tail absolute mass is \(O(L)\) by the finite \(m\)-sum. The absolute calibration mass there is \(O(L\log^2(2L))\) even before cancellation of its integral. Each individual ramp has supremum plus total variation \(O(x)\) on these \(q\)-intervals. The fixed finitely many jumps and coefficients in \(g(q/P)\) change this by a constant. Stieltjes summation, with one-sided values for every endpoint, therefore yields

\[
 D_g(x)=x^2 S_g(L)
  +O_{g,v}\big(x^2 L^{-1}\log^2(2L)+xL P^v\log^2(2L)\big).              \tag{3}
\]

An endpoint atom may equally be bounded by \(O(xL\log^2(2L)\log P)\). For \(v\) sufficiently close to \(\beta_*\), both powers in (3) are strictly below \(2-\lambda(1-\beta_*)\). For the second error the limiting gap is \((1-2\lambda)(1-\beta_*)>0\). Partial summation in (2) gives \(S_g(y)=O_v(y^{v-1})\) since its kernels are compactly supported and Lipschitz.

For \(\Re z>0\), direct Mellin integration of (2) gives

\[
 \int_0^\infty S_g(y)y^{-z-1}dy
   =W(1+z)\,C(1+z)\big(1\mathbin{\pm}2^{-(1+z)}\big),
\]

with plus for \(G\) and minus for \(J\). Both elementary factors are nonzero for \(\Re(1+z)>0\). Every nontrivial zero \(\rho\) of zeta therefore gives a genuine pole at \(\rho-1\); additional eta zeros can only increase the order. There is no real pole for \(z>-1\), since \(\zeta(s)\ne0\) there for real \(s>0\), and both eta factors are positive at positive real arguments. The inverse zeta extends through \(s=1\).

For clarity, if either sign of \(S_g(y)\) were eventually at most \(C y^d\) for some \(-1<d<\Re\rho-1\), the eventually nonnegative density \(C y^d\mp S_g(y)\) would have Mellin transform holomorphic on the real line \(z>d\), up to the irrelevant integral over a bounded initial interval. By Landau's theorem its abscissa of convergence is at most \(d\). This contradicts the pole at \(\rho-1\). Here the initial part near zero is entire since (2) vanishes there. Lipschitz continuity and \(\sum_{n\le c y}|c(n)|\ll y\) give \(S_g(y)-S_g(\lfloor y\rfloor)=O_g(y^{-1})\), which is smaller than \(y^d\). Both signs therefore occur on unbounded integer cutoff sequences. Taking \(x=N^{1/\lambda}\) on each sequence makes \(L=N\) exactly. Choose zeros with real part arbitrarily close to \(\beta_*\), then \(d\) just below the corresponding real part minus one, and \(v>\beta_*\) close enough for the errors in (3) to be smaller than \(x^{2+\lambda d}\). This proves (1), using the upper bound for \(S_g\) for the reverse inequality. [Landau argument and source-normalized first-window comparison](../step4-area-runs-2026-11-19/FIRST_BAND_OSCILLATION.md)

The conclusion concerns the original distributed calibration on complete fixed windows. Adaptive pairing or cancellation across windows remains possible. No source assumption giving square-scale control of their full sum was established by this test.
