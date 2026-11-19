# A fixed frequency band detects a rightward zero at every large cutoff

**DERIVED on paper.** Put \(\mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}\), and keep the complete Dirichlet polynomial

\[
 D_X(\tau)=\sum_{q\le X}\frac{\mu_6(q)}{\sqrt q}\,e^{-i\tau\log q},
 \qquad I_X(\nu,h)=\int_{\nu-h}^{\nu+h}|D_X(\tau)|^2\,d\tau .
\]

For every actual zeta zero \(\rho=\tfrac12+\delta+i\gamma\) with \(\delta>0\),
\[
                   I_X(\gamma,4)\gg_\rho X^{1.1\delta}                     \tag{1}
\]
at **every** sufficiently large real \(X\). The half-width is four. The center and implicit constant may depend on the zero. A stronger statement below permits any prescribed positive half-width and recovers the rightmost growth exponent up to any fixed loss by selecting a zero sufficiently near the supremum. The independent arithmetic upper remains open.

## The signed covariance being tested

Define \(\operatorname{sinc}(v)=\sin(v)/v\) for \(v\ne0\), with value 1 at zero. Direct integration of every ordered pair gives

\[
 I_X(\nu,h)=2h\sum_{q,r\le X}
 \frac{\mu_6(q)\mu_6(r)}{\sqrt{qr}}\,
 \cos\!\big(\nu\log(q/r)\big)\operatorname{sinc}\!\big(h\log(q/r)\big).
                                                                         \tag{2}
\]

The two ordered terms for distinct indices supply the real cosine. The diagonal is \(2h\sum_{q\le X}\mu_6(q)^2/q\); all signed off-diagonal terms remain. For (1), take \(\nu=\gamma,\ h=4\).

## Every-horizon bound with a compact causal test

Use \(a=24/25,\ c=21/20\), \(g(y)=\mathbf1_{[1,1/a)}(y)\cos(2\pi c y)/y\), and \(G(s)=\int_1^{1/a}g(y)y^{-s-1}dy\). Its source calculation gives \(G(\rho)\ne0\): in log coordinates the integrand after removing the oscillation is positive and strictly decreasing, and integration by parts gives strictness in the triangle inequality at a nonzero frequency. Let \(h_0(t)=e^{-t/2}g(e^t)\), a compact causal kernel. Use the convention \(\widehat f(\tau)=\int_{\mathbb R}e^{-i\tau t}f(t)dt\). [Original harmonic and centered identity](DELAYED_GAIN.md)

For a finite complex measure \(k\) supported on \([0,T]\), define \(h_k=h_0*k\), \(g_k(y)=y^{1/2}h_k(\log y)\), and \(v_k(y)=\sum_{q\le y}\mu_6(q)g_k(y/q)\). Thus \(g_k\) vanishes outside \([1,e^T/a]\), and
\[
 G_k(\rho)=\int_1^\infty g_k(y)y^{-\rho-1}dy
          =G(\rho)\int e^{-(\rho-1/2)t}dk(t).
\]
The kernel may be chosen at a particular cutoff \(X\); keep it fixed when applying the following identity at \(X\) and \(X/2\). The inverse convolution of \(\mu_6\) is \(u(q)=\mathbf1_{(q,6)=1}\). Put \(S(z;s)=\sum_{n\le z}u(n)n^{-s}\), including value zero below one. If \(e^T/a<X/2\), finite integration of \(u*v_k=g_k\) under multiplicative dilations gives
\[
 X^\rho(1-2^{1-\rho})G_k(\rho)=
 \int_1^X v_k(y)K_\rho(X/y)\frac{dy}{y},\qquad
 K_s(z)=z^s\{S(z;s)-2^{1-s}S(z/2;s)\}.
\]
Here \(\sup_{z\ge1}|K_\rho(z)|\ll_\rho1\), independently of \(k,T,X\). In fact \(\sum_{n\le z}u(n)=z/3+O(1)\); partial summation leaves the continuum term, which the difference cancels, and a multiple of \(z^\rho\zeta(\rho)(1-2^{-\rho})(1-3^{-\rho})=0\). The remainder is bounded for \(\Re\rho>0\); the segment \(1\le z<2\) is finite. The proof is linear and applies to complex test kernels. Since \(1-2^{1-\rho}\ne0\), Cauchy–Schwarz with respect to \(dy\) gives
\[
 \int_1^X |v_k(y)|^2\frac{dy}{y^2}
       \gg_\rho X^{2\delta}\left|\int e^{-(\delta+i\gamma)t}dk(t)\right|^2.
                                                                         \tag{3}
\]
The bound uses the identity at the zero itself and holds for every admissible frozen kernel with the same constant. There is no differentiation of a moving family.

Write \(\lambda_X=\sum_{q\le X}\mu_6(q)q^{-1/2}\delta_{\log q}\), where \(\delta_t\) here denotes a point mass. On \(0\le t\le\log X\) the function \(\lambda_X*h_k(t)\) equals \(e^{-t/2}v_k(e^t)\) by causality. Its whole-line squared norm is
\[
              \frac1{2\pi}\int_{\mathbb R}|D_X(\tau)\widehat h_0(\tau)
                                                  \widehat k(\tau)|^2d\tau.
                                                                         \tag{4}
\]
This majorizes (3), including every output after the cutoff in (4).

## The elementary test of half-width four

Take \(N=\lfloor .9\log X\rfloor\) and use for \(k\) the \(N\)-fold convolution of \(e^{i\gamma t}\mathbf1_{[0,1]}(t)dt\). Its total variation is at most 1 and its support is contained in \([0,N]\); thus \(e^N/a<X/2\) for all large \(X\). The Laplace factor in (3) has modulus
\[
       \left(\int_0^1 e^{-\delta t}dt\right)^N\ge e^{-\delta N/2}
\]
by convexity. The right side of (3) is at least a positive constant times \(X^{2\delta}e^{-\delta N}\ge X^{1.1\delta}\).

For \(|\tau-\gamma|\ge4\), direct integration of the box gives \(|\widehat k(\tau)|\le(2/|\tau-\gamma|)^N\le2^{-N}\). The full polynomial satisfies \(|D_X|\le2\sqrt X\). The part of (4) outside the band is at most \(4X\,2^{-2N}\|h_0\|_2^2=O(X^{1-1.8\log 2})\), with a constant to account for the floor. The exponent is strictly negative. On the band, (4) is at most \(\|h_0\|_1^2 I_X(\gamma,4)/(2\pi)\). These two bounds prove (1).

## Arbitrarily narrow fixed bands near the rightmost zeros

Let \(B=\sup_\rho\Re\rho\), \(b=B-1/2>0\). For **every fixed** \(h>0\) and \(0<\eta<2b\) there exists a zero ordinate \(\gamma\), fixed independently of \(X\) but possibly depending on \(h,\eta\), such that
\[
                           I_X(\gamma,h)\gg_{\rho,h,\eta} X^{2b-\eta}
                   \quad\hbox{for every sufficiently large }X .          \tag{5}
\]
The threshold depends on the chosen zero. This quantifier neither assumes \(B\) is attained nor assigns (5) to every rightward zero at that bandwidth.

First, the **whole unfiltered output** with the fixed kernel satisfies
\[
  \frac1{2\pi}\int_{\mathbb R}|D_X(\tau)\widehat h_0(\tau)|^2d\tau
               =\|\lambda_X*h_0\|_2^2\ll_\epsilon X^{2b+\epsilon}.
                                                                         \tag{6}
\]
For \(B<1\), the zero-free half-plane estimate and Perron give \(M(u)=O_\epsilon(u^{B+\epsilon})\). Removing primes 2 and 3 multiplies the Dirichlet series by their inverse local factors, so \(M_6(u)=\sum_{q\le u}\mu_6(q)=\sum_{2^i3^j\le u}M(u/(2^i3^j))=O_\epsilon(u^{B+\epsilon})\). For \(B=1\) elementary counting suffices. At \(y=e^t\) the output is \(y^{-1/2}\sum_{q\le X}\mu_6(q)g(y/q)\), supported in \(1\le y\le X/a\). Partial summation uses the bounded variation of \(q\mapsto g(y/q)\) uniformly in \(y\). On \(1\le y\le X\) it gives \(O_\epsilon(y^{b+\epsilon})\) for the normalized output. On \(X<y\le X/a\) the sum runs only over \(ay<q\le X\); its endpoint term and integral are \(O_\epsilon(X^{B+\epsilon})\) before normalization. The full terminal interval has log length \(\log(1/a)\). Integrating squared magnitude with \(dy/y\) in both regions proves (6) after decreasing the preliminary epsilon. No continuation of the *truncated* output past \(X\) by the infinite arithmetic input was used. [Mertens estimate from the zero supremum](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)

For half-width four, (5) already follows from the unit boxes above with \(N=\lfloor\kappa\log X\rfloor\). The lower exponent is at least \(2\delta-\kappa\delta\); (6) improves the high-tail exponent to \(2b-2\kappa\log 2+\epsilon\). First take \(\kappa>0\) small enough for the requested loss at \(\delta=b\). The gap at \(\delta=b\) before epsilon is \(\kappa(2\log2-b)>0\). Choosing a zero sufficiently near the supremum and then epsilon small preserves it.

For arbitrarily narrow bandwidths use a different compact test. Fix \(0<\kappa<1\), write \(R=\kappa\log X/2\), and let \(U=(U_1,U_2,U_3)\) be uniform on the unit sphere in \(\mathbb R^3\). Tilt this probability by the density \(e^{hR U_2}/J(hR)\), where \(J(w)=\sinh(w)/w,\ J(0)=1\). Push it forward by \(t=R(1+U_1)\in[0,2R]\), and multiply by \(e^{i\gamma t}\) to obtain \(k\). Its total variation is 1, and \(e^{2R}/a<X/2\) eventually. For a real vector \(z\), spherical rotation and the uniform axial coordinate on \([-1,1]\) give \(\mathbb E e^{z\cdot U}=J(\sqrt{z\cdot z})\). Both sides are entire in the components by the power series of the even function \(J\), so the identity continues to the complex arguments used here. Directly,
\[
 \widehat k(\gamma+\xi)=
   e^{-iR\xi}\frac{J(R\sqrt{h^2-\xi^2})}{J(hR)},\qquad
 \int e^{-(\delta+i\gamma)t}dk(t)=
   e^{-\delta R}\frac{J(R\sqrt{h^2+\delta^2})}{J(hR)} .
\]
For \(|\xi|\ge h\) the numerator in the first expression is a real sinc of modulus at most 1. Thus (6) bounds the part of (4) outside the band by
\[
                    O_{\epsilon,h,\kappa}\big((\log X)^2
                                         X^{2b-\kappa h+\epsilon}\big).
\]
For fixed \(h,\delta>0\), the large-positive-real asymptotic \(J(w)\sim e^w/(2w)\) makes the lower (3) at least a positive constant times \(X^{p(\delta)}\), where
\[
                  p(\delta)=2\delta+\kappa(\sqrt{h^2+\delta^2}-h-\delta).
\]
Choose \(\kappa>0\) sufficiently small first so \(p(b)>2b-\eta\). Moreover \(p(b)-(2b-\kappa h)=\kappa(\sqrt{h^2+b^2}-b)>0\). Choose a zero with \(\delta\) sufficiently close to \(b\) to preserve both strict inequalities, then choose the epsilon in (6) small enough to absorb the logarithm and preserve the latter gap. Since \(|\widehat k|\le1\), the in-band part of (4) is at most \(\|h_0\|_1^2 I_X(\gamma,h)/(2\pi)\). This proves (5). For comparison, partial summation with \(M_6(u)\) against \(u^{-1/2-i\tau}\) also gives \(I_X(\nu,h)\ll_{\nu,h,\epsilon} X^{2b+\epsilon}\) on any fixed bounded interval.

## What would close the arithmetic criterion

It suffices to prove the following upper for the literal signed expression (2). For each integer center \(m\), every \(\epsilon>0\), and every \(R_0\), there exists \(X\ge R_0\) with \(I_X(m,5)\le X^\epsilon\). Indeed the nearest integer to any \(\gamma\) has \([\gamma-4,\gamma+4]\subset[m-5,m+5]\). Nonnegativity of the squared integrand plus (1) then contradicts the chosen center's cofinal upper for \(\epsilon<1.1\delta\). Constants depending on \(m,\epsilon\) can be absorbed by decreasing epsilon first. The selected \(X\) may depend on \(m,\epsilon,R_0\); no simultaneous horizon for different centers is required. Conversely RH gives the upper at every large \(X\) for each fixed band by the same partial summation bound with \(B=1/2\). For a prescribed narrow half-width \(h\), a covering lattice of centers \(mh,\ m\in\mathbb Z\), works by applying (5) at half-width \(h/2\) and enclosing its interval around the nearest lattice point.

The proofs supply necessary lower bounds under a hypothetical zero and identify an equivalent target for an independent upper on signed arithmetic pairs. They give no such upper. This is a paper argument and carries no new Lean or CI closure authority.
