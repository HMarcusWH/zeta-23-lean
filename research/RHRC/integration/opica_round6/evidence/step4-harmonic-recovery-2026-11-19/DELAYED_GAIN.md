# Every-horizon energy of the actual Möbius harmonic and its delayed gain

**DERIVED on paper.** The signed Möbius harmonic has a lower bound on its total absolute response at **every sufficiently large horizon**. A zero \(\rho=\beta+i\gamma\) of multiplicity \(l\) gives an explicit power \(X^\beta\) and a factor \((\log X)^{l-1}\). The fourth-root delay then has an exact amplification exponent \((B-1/2)/4\), where \(B\) is the supremum of nontrivial zeta-zero real parts. A cofinal subpower bound on a positive arithmetic mean of actual gains would suffice for RH. That independent upper remains open.

## The true input and the finite integral that detects a zero

Use \(a=24/25,\ c=21/20\), and let
\[
 g(y)=\mathbf1_{1\le y<1/a}\frac{\cos(2\pi c y)}y,\qquad
 v(x)=\sum_{q\le x}\mu_6(q)\,g(x/q),\qquad
 \mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}.
\]
Set \(v(x)=0\) for \(0<x<1\). For \(s\in\mathbb C\) put
\[
 G(s)=\int_1^{1/a}g(y)y^{-s-1}dy .
\]
In the earlier unnormalized notation this is \(m(1+s)\). At a nontrivial zero \(\rho\), \(G(\rho)\ne0\). Indeed, writing \(y=e^t\), it is the Fourier integral at \(\gamma\) of \(w(t)=e^{-(1+\beta)t}\cos(2\pi c e^t)\) on \(0\le t\le\log(1/a)\). This positive density is strictly decreasing, since \(1<c e^t\le35/32<9/8\). If the integral vanished at a nonzero frequency, integration by parts would express \(w(0)\) as a sum of \(w(\log(1/a))e^{-i\gamma\log(1/a)}\) and the integral of \((-w')e^{-i\gamma t}\). Their absolute masses sum to \(w(0)\), but the second has strictly varying phase on a positive interval. At zero frequency positivity suffices. [One-harmonic source and zero detector](../step4-native-residual-2026-11-19/ONE_HARMONIC_ZERO_DETECTOR.md)

Put \(e_6(k)=\mathbf1_{(k,6)=1}\), \(\alpha=1/3\), \(A_6(u)=\sum_{k\le u}e_6(k)=\alpha u+O(1)\), and \(Z_6(s)=\zeta(s)(1-2^{-s})(1-3^{-s})\). Because \(e_6*\mu_6=\delta_1\) under Dirichlet convolution,
\[
 \sum_{k\le x} e_6(k) v(x/k)=g(x).
\]
Integrate this identity over \(1\le x\le X\) against \(x^{-s-1}dx\). All finite sums can be interchanged, giving for \(X>1/a\)
\[
 G(s)=\int_1^X v(y)y^{-s-1}S(X/y;s)\,dy,\qquad
 S(t;s)=\sum_{k\le t} e_6(k)k^{-s}.
\]
Take also the identity at \(X/2\), requiring \(X>2/a\). Subtract it after multiplication by \(2^{1-s}\), then multiply by \(X^s\). Exactly,
\[
 X^s (1-2^{1-s})G(s)
 =\int_1^X v(y)K_s(X/y)\,\frac{dy}{y},\qquad
 K_s(t)=t^s\{S(t;s)-2^{1-s}S(t/2;s)\}.                          \tag{1}
\]
For \(t<2\) the second sum is empty. The subtraction removes the full leading continuum of the coprime-integer source at a common cutoff.

Write \(E(u)=A_6(u)-\alpha u\). Partial summation, initially at \(\Re s>1\) and then by continuation to \(\Re s>0,\ s\ne1\), gives for \(t\ge1\)
\[
 t^s S(t;s)= t^s Z_6(s)+\frac{\alpha t}{1-s}
       +E(t)-s\int_1^\infty E(tw)w^{-s-1}dw.                       \tag{2}
\]
The last two terms form an analytic function of \(s\) bounded uniformly in \(t\) on each compact disk in \(\Re s>0\). The corresponding uniform derivative bounds hold by Cauchy's formula. For \(t\ge2\), (2) applied at \(t,t/2\) yields
\[
 K_s(t)=(1-2^{1-s})t^s Z_6(s)+O(1)
\]
uniformly on compact disks in \(0<\Re s<1\), with an analytic bounded remainder. For \(1\le t<2\), both \(K\) and its fixed-order derivatives are directly bounded on each such disk. Hence, if \(Z_6\) vanishes with multiplicity \(l\) at \(\rho\), then \(\sup_{t\ge1}|\partial_s^j K_\rho(t)|<\infty\) for \(0\le j<l\). Both Euler factors are nonzero at \(\rho\), so \(l\) is its zeta multiplicity.

Differentiate (1) exactly \(l-1\) times, holding \(X\) fixed. The finite-range integral permits differentiation. The leading coefficient on the left is \((1-2^{1-\rho})G(\rho)\ne0\), since \(\beta<1\). The other terms have lower logarithmic degree. Taking the modulus gives the following at every sufficiently large real \(X\), with a threshold depending on the chosen zero:
\[
 \boxed{\ \int_1^X |v(y)|\,\frac{dy}y\ \gg_\rho\
 X^\beta(\log X)^{l-1} .\ }                                         \tag{3}
\]
In particular, Cauchy–Schwarz against \(dy\) gives
\[
 \int_1^X |v(y)|^2\frac{dy}{y^2}
 \gg_\rho X^{2\beta-1}(\log X)^{2l-2}.
\]
No integrability on the full positive half-line was assumed.

## The envelope, including integer samples

Put \(F(X)=\sup_{1\le y\le X}|v(y)|/\sqrt y\), \(H(X)=1+F(X)\), and \(b=B-1/2\ge0\). Equation (3) and \(\int_1^X y^{-1/2}dy<2\sqrt X\) give the lower \(F(X)\gg_\rho X^{\beta-1/2}(\log X)^{l-1}\). For the upper, if \(B<1\), the inverse-zeta estimate and sharp Perron bound on any line strictly to the right of \(B\) give \(M(u)=O_\epsilon(u^{B+\epsilon})\). Removing multiples of 2 and 3 uses \(\sum_{2^i3^j\le u}M(u/(2^i3^j))\), of the same order. Partial summation against the compact native kernel, which has bounded total variation, gives \(v(y)=O_\epsilon(y^{B+\epsilon})\). When \(B=1\), absolute counting gives \(v(y)=O(y)\). [Zero-free reciprocal and sharp-cutoff argument](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md)

Choose a fixed actual zero with real part arbitrarily near \(B\), establish its lower for every large \(X\), and only then let its real part approach \(B\). If \(B=1/2\) one may use any critical-line zero. This proves
\[
 H(X)=X^{b+o(1)},\qquad \int_1^X |v(y)|\,dy/y=X^{B+o(1)}
 \quad\text{at every horizon.}                                       \tag{4}
\]
The same conclusions hold for integer samples. Uniformly for \(n\le y<n+1\), \(v(y)=v(n)+O(1)\): the two moving support endpoints add or remove only \(O(1)\) bounded labels, and the common terms change by \(O(1/q)\) each on \(q\asymp n\). Thus the continuous and integer normalized envelopes differ by \(O(1)\). Also
\[
 \int_1^X |v(y)|\,dy/y=\sum_{n\le X}|v(n)|/n+O(\log(2X))
\]
for integer \(X\), using \(|v(n)|\ll n\) for the unit-cell weight error (the last integer contributes \(O(1)\)). We can use \(H_\mathbb N(U)=1+\max_{1\le j\le U}|v(j)|/\sqrt j\) in all gain statements below, since \(H_\mathbb N\) and \(H\) are within fixed factors.

## Exact delayed replay and independent tail payment

For each integer \(n\) sufficiently large set \(Y=\lfloor n^{1/4}\rfloor,\ m=Y+1,\ K=\lfloor Y\sqrt n\rfloor\). Freeze these for that row. Define
\[
 b_d^{(n)}=\mu_6(d)\ (d\le Y),\quad b_m^{(n)}=-m\sum_{d\le Y}\frac{\mu_6(d)}d,
 \qquad w_n=b^{(n)}*e_6,
\]
with all other \(b_d^{(n)}=0\). Then \(w_n(1)=1,\ w_n(k)=0\) for \(2\le k\le Y\). Since \(e_6*\mu_6=\delta_1\), the full replay is \(\sum_d b_d^{(n)}g(n/d)=0\) once \(n>m/a\). This need not constrain the parity of \(m\).

The exact identity \(1=\sum_{d\le Y}\mu_6(d)A_6(Y/d)\) and the bounded integer discrepancy give \(\sum_{d\le Y}\mu_6(d)/d=O(1)\), so \(\sum|b_d^{(n)}|=O(Y)\). By construction \(\sum b_d^{(n)}/d=0\). For every real \(t>0\),
\[
 \left|\sum_{k\le t}w_n(k)\right|
 =\left|\sum_{d\le m} b_d^{(n)} (A_6(t/d)-\alpha t/d)\right|\ll Y.
\]
For \(Y'>1\), the total variation of \(v\) on \((0,Y']\) is \(O(Y')\), by adding the variation of the bounded-jump \(g(y/q)\) over \(q\le Y'\). Abel summation therefore bounds the entire \(k>K\) tail in absolute value by \(O(Y n/K)=O(\sqrt n)\), including boundary terms. With the actual signed middle replay
\[
 R(n)=\sum_{m\le k\le K} w_n(k)v(n/k)
\]
one has \(R(n)=-v(n)+O(\sqrt n)\), uniformly. The summands use genuine source values between \(n/K\) and \(n/m\). These finite sums and the integer-sample envelope can be calculated solely from the original input.

## The sharp gain and the cofinal mean criterion

Set \(\mathcal G(n)=|R(n)|/(\sqrt n\,H_\mathbb N(n/m))\) for all sufficiently large \(n\), taking the finitely many smaller gains as zero. From (4), \(H_\mathbb N(n/m)=n^{3b/4+o(1)}\). The upper for \(v\) gives
\[
 1+\mathcal G(n)\le n^{b/4+o(1)}.                                    \tag{5}
\]
The convention in (5) is an upper logarithmic exponent. If \(b>0\), the source has limsup \(\log(1+|v(n)|/\sqrt n)/\log n=b\), either by (3) or by the native signed-row detector. Along a sequence approaching this exponent the \(O(\sqrt n)\) tail is smaller by a fixed power. If \(b=0\), use \(1+\mathcal G\ge1\). Thus
\[
 \limsup_{n\to\infty}\frac{\log(1+\mathcal G(n))}{\log n}=\frac b4.
\]
If one uses the project's external bound \(B\le0.873346\), (5) gives the independent ceiling \(\mathcal G(n)\ll_\epsilon n^{0.0933365+\epsilon}\). The fraction \(b/4\) above uses no such ceiling. [External theorem and its qualification](../step4-height-window-2026-11-19/STEP4_HEIGHT_AND_GRAPH_RESULTS.md)

There is also an every-horizon result for the **positive mean of the actual gains**:
\[
 \boxed{\quad
 1+\frac1{\sqrt X}\sum_{n\le X}\frac{\mathcal G(n)}{\sqrt n}
 =X^{b/4+o(1)},\qquad
 1+\frac1X\sum_{n\le X}\mathcal G(n)=X^{b/4+o(1)} .
 \quad}                                                               \tag{6}
\]
For the first lower with \(b>0\), sum \(|v(n)|\le |R(n)|+O(\sqrt n)\) with weight \(1/n\). The left has size \(X^{B+o(1)}\) at every horizon by (4), while the total error is \(O(\sqrt X)\). The delayed envelope on this range is at most \(X^{3b/4+o(1)}\), uniformly after absorbing small \(n\). It follows that \(\sum_{n\le X}\mathcal G(n)/\sqrt n\ge X^{1/2+b/4-o(1)}\). The matching upper follows from (5). For the second lower, fix \(0<d<1\): terms \(n\le X^d\) contribute at most \(X^{d(1/2+b/4)+o(1)}\) to the weighted sum, giving a strict power gap. On \(n>X^d\), multiply by \(\sqrt n\ge X^{d/2}\), take the lower limit in \(X\), then send \(d\) to 1. Upper bounds again follow from (5). If \(b=0\), both conclusions follow from (5) and the baseline one.

In particular a proof that either positive mean in (6) is bounded by \(X^\epsilon\) at arbitrarily large integer \(X\), for every \(\epsilon>0\), would imply RH. The stronger pointwise delayed inequality \(|R(n)|\ll_\eta n^{1/2+\eta}H_\mathbb N(n/m)\) at every large \(n\) also suffices directly: for target \(\delta>0\) choose \(\eta<\delta/4\), use \(n/m\le n^{3/4}\), and induct on \(n\) after absorbing the fixed constants and \(O(\sqrt n)\) error. This yields \(v(n)=O_\delta(n^{1/2+\delta})\), contradicting (3) for any zero with \(\beta>1/2\) upon choosing \(\delta<\beta-1/2\).

The finite identities establish both reconstructions and the cost of their tails. The remaining signed arithmetic estimate can be stated as the cofinal positive-mean upper in (6); its growth exponent is now known exactly in terms of the unknown \(B\). Step 4 and RH remain **OPEN**.
