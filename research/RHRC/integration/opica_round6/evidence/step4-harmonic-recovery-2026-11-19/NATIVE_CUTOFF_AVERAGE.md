# Averaging the first Möbius ramp over genuine integer cutoffs

**DERIVED on paper.** Write \(E_L(n)\) for the native integer response of the distributed factorial filter, with its actual Möbius coefficients. Averaging over the genuine cutoffs \(N\le L\le2N\) gives a square-scale bound for the initial \(L^{0.85}\) sites for a density-one set of cutoffs, with a power bound on exceptions. The previous all-cutoff result covered \(L^{5/6}\log^K L\). The gain uses the project's external zero ceiling \(r=0.873346\). There is also an obstruction on any fixed-ratio site interval strictly inside the first band. A smoothed sum there detects each zeta zero at once for a whole interval of nearby cutoffs. The full cofinal upper remains open. [Previous all-cutoff result](../step4-matched-fibres-2026-11-19/QUIET_PREFIX_AND_CALIBRATION.md) · [Full native criterion](../step4-matched-fibres-2026-11-19/RESIDUE_GRAPH_CRITERION.md)

## A mean-square upper at the actual observation site

Write \(B=\sup_{\rho}\Re\rho\) over nontrivial zeta zeros. Fix \(B<v<1\) and \(0<e<1/2\). For integers \(2\le H<N-2\) put

\[
 U_H(L)=\sum_{h=1}^H\frac{|E_L(L+h)|}{(L+h)^3},\qquad
 \Delta=(H+2)/N .
\]

Uniformly for \(\Delta\le1\),

\[
 \left(\frac1N\sum_{L=N}^{2N-1}U_H(L)^2\right)^{1/2}
 \ll_{v,e} N^{v-1}\Delta^{5/2-e}+(H+2)^2/N^3.                         \tag{1}
\]

The observation site has phase zero at every cutoff. Since \(L+h<2L\), every proper divisor of a cofactor in \((L,L+h]\) is at most \(L\), and every calibration node exceeds \(2L\). Thus

\[
 E_L(L+h)=\sum_{L<j\le L+h}\mu(j)(L+h-j).
\]

For real \(y\) write \(M(y)=\sum_{j\le y}\mu(j)\), interpreted as zero below one. For real \(u>0\) the multiplicative increment \(A(y,u)=M((1+u)y)-M(y)\) has exact Mellin transform

\[
 \int_0^\infty A(y,u)y^{-s-1}dy=
 \frac{(1+u)^s-1}{s\zeta(s)},\qquad \Re s=v .
\]

Indeed \(M(y)=O_w(y^w)\) for any \(B<w<v\), and for fixed \(u\le1\) the increment vanishes below \(1/2\). The integral therefore converges there; the identity follows from absolute coefficient summation on \(\Re s>1\) and continuation. Mellin Plancherel uses the ordinary Fourier transform in \(\log y\) after multiplying by \(y^{-v}\). The input is square integrable by the same strict exponent margin. On this line the zero-free estimate \(1/\zeta(v+it)\ll_{v,e}(1+|t|)^e\) holds. The other factor has magnitude \(O_v(\min(u,(1+|t|)^{-1}))\), using its integral in \(1+u\) at low heights. Splitting the resulting square integral at \(1/u\) gives

\[
 \left(\frac1N\int_N^{2N}|A(y,u)|^2dy\right)^{1/2}
 \ll_{v,e}N^v u^{1/2-e}\quad(0<u\le1).
\]

This uses only a line strictly to the right of the supplied zero ceiling when \(v>r\). [Analytic proof of the Mertens and reciprocal-zeta inputs](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)

To retain every integer cutoff, let \(L\le y<L+1\) and \(R_y(h)=\sum_{y<j\le y+h}\mu(j)(y+h-j)\) for real \(h\ge0\). At integer \(h\), \(|R_y(h)-E_L(L+h)|\le h+1\) because \(y\) and \(L\) have the same floor. On \(h\le H+1\) the function \(R_y(h)\) has slopes bounded by \(H+2\). Hence

\[
 U_H(L)\ll N^{-3}\left((H+2)^2+\int_0^{H+1}|R_y(h)|dh\right).
\]

Exactly \(R_y(h)=\int_0^h[M(y+t)-M(y)]dt\). Changing variables \(t=yu\) and enlarging the positive integral gives
\(\int_0^{H+1}|R_y(h)|dh\le (H+1)\,2N\int_0^\Delta|A(y,u)|du\).
Take the normalized square norm over \(N\le y<2N\); the left cutoff statistic is constant on each \([L,L+1)\). Minkowski's inequality and the preceding increment bound prove (1).

With \(H\asymp N^\theta\), the right side has exponent at most \(v-1-(1-\theta)(5/2-e)\), apart from the smaller \(H^2/N^3\) term. Therefore every fixed \(\theta<1-(B-1/2)/(5/2)\) has a power saving beyond \(N^{-1/2}\). Concretely choose \(v=.8735,\ e=.001,\ H=\lceil(2N)^{.85}\rceil\). The first exponent is \(-.50135\), the second \(-1.30\). At most \(O(N^{1-.0027})\) of the \(N\) cutoffs have \(U_{\lfloor L^{.85}\rfloor}(L)>N^{-1/2}\), by (1) and the second-moment inequality. This bound applies on every late dyadic scale. It supplies no control of the omitted \(n>L+L^{.85}\) sites for the selected cutoffs.

## A cutoff-independent test on the common interior

Fix \(1<\kappa<c<d<2\). For all \(N\le L\le\kappa N\), sites \(n\) in a compact subinterval of \((cN,dN)\) lie in the first band. At a common site,
\[
 E_L(n)=\sum_{j\le n}\mu(j)(n-j)-n M(L)+\sum_{j\le L}j\mu(j).
\]
Changing the true cutoff therefore changes an affine function of \(n\) exactly. In particular the centered second difference in \(n\) equals \(\mu(n)\) for every such \(L\), including its two adjacent sites for large \(N\).

Choose a real \(C^2\) test \(\phi\) compactly supported in \((c,d)\) whose Mellin transform \(\Phi(s)=\int\phi(u)u^{s-1}du\) is nonzero for \(\Re s>0\). One explicit choice in \(\log u\) is a translated fourfold ordinary convolution of the indicator of \([0,b]\) with itself, with \(b>0\) small enough for this support. Its transform is \(e^{as}((e^{bs}-1)/s)^4\) for the chosen translation \(a\). Put \(Z(y)=y^{-1}\sum_n\mu(n)\phi(n/y)\). Finite summation by parts twice gives for every \(N\le L\le\kappa N\)

\[
 |Z(N)|=\left|\frac1N\sum_n E_L(n)
       [\phi((n+1)/N)-2\phi(n/N)+\phi((n-1)/N)]\right|
 \ll_{\phi,d}\sum_{cN<n<dN}\frac{|E_L(n)|}{n^3}.                        \tag{2}
\]

The kernel in brackets is bounded by \(\|\phi''\|_\infty/N^2\) and stays inside the selected sites for all large \(N\). The same signed witness \(Z(N)\) works at every one of the cutoffs.

For \(\Re z>0\), \(\int_0^\infty Z(y)y^{-z-1}dy=\Phi(1+z)/\zeta(1+z)\). Every nontrivial zero \(\rho\) gives a pole at \(z=\rho-1\); there are no real poles for \(z>-1\). The Landau argument for nonnegative Mellin densities applied to \(Cy^\alpha\mp Z(y)\) shows that both signs of \(Z(y)\) exceed \(Cy^\alpha\) on unbounded sequences, for any \(C>0\) and \(-1<\alpha<\Re\rho-1\). Otherwise such a density would be eventually nonnegative, with real abscissa of convergence at most \(\alpha\) by real analyticity to its right, incompatible with its nonreal pole at \(\rho-1\). The integral for small \(y\) gives an entire correction by compact support away from zero. The bounded derivative of the kernel gives \(Z(y)-Z(\lfloor y\rfloor)=O_\phi(y^{-1})\), so integer scales suffice. [Landau argument with the same normalization](../step4-area-runs-2026-11-19/FIRST_BAND_OSCILLATION.md)

Consequently, for each \(\epsilon>0\), on arbitrarily late integer scales \(N\) the right side of (2) exceeds a fixed positive multiple of \(N^{B-1-\epsilon}\) **simultaneously for every integer cutoff \(N\le L\le\kappa N\)**. Taking the pointwise median or averaging over nearby cutoffs on these scales preserves this localized absolute lower bound. This strengthens the spatial information from the all-cutoff exponent of the *full* statistic: any preassigned compact interior band as above can carry the obstruction. Formula (2) makes no assertion about all scales for that individual band. It also explains why the positive result (1) does not extend to a fixed positive fraction of \(L\) by a routine change of window. No new theorem establishing Step 4 or RH has been obtained.
