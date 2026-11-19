# Unconditional localization of the prime-area anomaly below the five-eighths exponent plus epsilon

**DERIVED on paper.** Let \(A(x)=\int_2^x(\vartheta(t)-t)\,dt\), with ordinary primes and their true logarithmic weights. For any fixed \(0<\lambda<3/8\) and \(0<\kappa<2/5-\lambda\), we construct explicit signed weights \(K_{x,L}\), with \(L=\lfloor x^\lambda\rfloor\), such that

\[
 A(x)+\tfrac23x^{3/2}
 =\sum_{x^\kappa<p<x/(L+1)} K_{x,L}(p)\log p+o(x^{3/2}).                 \tag{1}
\]

This holds for all real \(x\to\infty\) without a zero-free half-plane input. The upper endpoint is \(<x^{1-\lambda}\). Thus it can lie below \(x^{5/8+\epsilon}\) for any fixed \(\epsilon>0\). A concrete choice is \(\lambda=0.37,\ \kappa=0.025\), giving only primes \(x^{0.025}<p<x^{0.63}\). The [factorial localization using the supplied external ceiling](OLD_PRIME_LOCALIZATION.md) observes the same centered area on a **disjoint** prime band, from approximately \(x^{0.64}/(0.11\log x)^2\) to \(x^{0.89}\). Each retains the original prime source through its own exact arithmetic weights. The shared scalar could still be large in both representations.

## The arithmetic filters

Use the entire function \(\eta(s)=(1-2^{1-s})\zeta(s)\), with \(\eta(1)=\log2\), and set

\[
 H(s)=\zeta(s)\eta(2s)\eta(3s),\qquad H_m(s)=(1-m^{1-s})H(s),\qquad m\ge2.
\]

For \(\Re s>1\), write \(H(s)=\sum h(n)n^{-s}\), \(H_m(s)=\sum h_m(n)n^{-s}\) and \(1/H(s)=\sum c(n)n^{-s}\). These are absolutely convergent there. All coefficients are real, \(h(1)=c(1)=1\), and \(h_m(n)=h(n)-m\mathbf1_{m\mid n}h(n/m)\), with the second term omitted when inapplicable. Explicitly, \(h(n)\) sums the coefficient \((1-2\mathbf1_{2\mid b})(1-2\mathbf1_{2\mid d})\) over all ordered factorizations \(n=ab^2d^3\). Define

\[
 J_m(y)=\sum_{n\le y}h_m(n)(y-n),\qquad Q_m(x)=\sum_{p\le x}p\log p\,J_m(x/p).
\]

Both sums are finite at every real input. The continuous ramp evaluates to zero at its integer endpoint.

## Mellin evaluation on the actual prime source

For \(\Re s>1\), the ordinary-prime Dirichlet series has the divisor identity

\[
 P(s)=\sum_p(\log p)p^{-s}=-\sum_{k\ge1}\mu(k)\frac{\zeta'(ks)}{\zeta(ks)} .   \tag{2}
\]

Expanding the logarithmic derivatives counts each prime power with coefficient \(\sum_{k\mid a}\mu(k)\) at \(p^a\), proving (2). The terms \(k=1,2,3\) in (2) have signs \(-,+,+\). There is no \(k=4\) term. On every strip \(\Re s\ge\sigma>1/5\), the remaining \(k\ge5\) sum, denoted \(V(s)\) with the signs in (2), converges absolutely and is bounded. The first term is bounded by absolute convergence at \(5\sigma>1\), and the subsequent terms decay geometrically as \(k\to\infty\).

Multiplication by \(H\) removes all three denominator factors. The meromorphic continuation of \(P(s)H(s)\) on this strip equals

\[
 \begin{aligned}
 &-\zeta'(s)\eta(2s)\eta(3s)\\
 &+\zeta(s)(1-2^{1-2s})\zeta'(2s)\eta(3s)\\
 &+\zeta(s)\eta(2s)(1-2^{1-3s})\zeta'(3s)+H(s)V(s).
 \end{aligned}                                                           \tag{3}
\]

At \(\Re s=2\), Mellin inversion of the ramp gives

\[
 Q_m(x)=\frac1{2\pi i}\int_{(2)}\frac{P(s)H_m(s)x^{1+s}}{s(s+1)}\,ds .   \tag{4}
\]

Take fixed \(1/5<\sigma<1/3\). Classical zeta convexity follows from the functional equation, Stirling and the three-lines theorem. Uniformly for \(\sigma\le u\le2\), \(|t|\ge2\), each factor \(\zeta(j(u+it))\) or its first derivative is \(\ll_{\sigma,\epsilon}(1+|t|)^{(1-ju)_+/2+\epsilon}\), for \(j=1,2,3\). For the derivative take Cauchy estimates on a sufficiently small fixed circle and use the arbitrary epsilon allowance. Thus (3) is bounded by \(O_{\sigma,\epsilon}((1+|t|)^{(3-6\sigma)/2+\epsilon})\). Choose \(\epsilon\) small enough that the exponent is below 1. On the full contour \(|1-m^{1-s}|\le1+m^{1-\sigma}\). The horizontal integrals at height \(\pm T\) are \(O_{\sigma,\epsilon}(m^{1-\sigma}x^3 T^{(3-6\sigma)/2+\epsilon-2})\) and tend to zero for each \(x,m\). The new vertical integral is absolutely \(O_\sigma(m^{1-\sigma}x^{1+\sigma})\) with a constant independent of \(m,x\ge2\). This suffices when \(m\) grows with \(x\), since each shift may first be made at its fixed \(x,m\). [Zeta functional equation](https://dlmf.nist.gov/25.4) · [Stirling expansion](https://dlmf.nist.gov/5.11)

The poles crossed in (4) are \(1,1/2,1/3\). At 1, \((1-m^{1-s})\zeta(s)\to\log m\) and \(P(s)\) has residue 1. At \(s=1/k\), \(k=2,3\), \(P(s)\) has residue \(-1/k\). All other factors there are finite. With the ramp denominator retained, their contributions give exactly

\[
 \begin{aligned}
 Q_m(x)={}&\tfrac12\eta(2)\eta(3)\log(m)x^2\\
 &-\tfrac23\zeta(1/2)\eta(1)\eta(3/2)(1-\sqrt m)x^{3/2}\\
 &-\tfrac34\zeta(1/3)\eta(2/3)\eta(1)(1-m^{2/3})x^{4/3}
 +O_\sigma(m^{1-\sigma}x^{1+\sigma}).                                   \tag{5}
 \end{aligned}
\]

## Finite divisor inversion, including the cube residue

For \(2\le m\le L\) take \(a_m=-c(m)/m\). At the four additional integers \(m=R,4R,16R,64R\), where \(R=2L+1\), choose the unique real coefficients solving

\[
 \sum a_m=1,\quad \sum a_m\log m=\frac1{\eta(2)\eta(3)},\quad
 \sum a_m(1-\sqrt m)=\frac1{\zeta(1/2)\eta(1)\eta(3/2)},\quad
 \sum a_m(1-m^{2/3})=0 .                                                 \tag{6}
\]

The denominators are nonzero since \(\eta(u)>0\) for real \(u>0\), and \(\zeta(1/2)=\eta(1/2)/(1-\sqrt2)<0\). The four-node matrix reduces by row operations to the independent rows \(1,i,2^i,(4^{2/3})^i\), \(i=0,1,2,3\). This is the confluent Vandermonde matrix at the nodes \(1,2,4^{2/3}\), with 1 repeated twice. The last equality of (6) cancels the cube term in (5) before summing errors. Treating each cube residue as \(O_m(x^{4/3})\) would fail to justify the claimed range.

The coefficients of \(1/\eta(ks)\), \(k=2,3\), are absolutely summable with weight \(1/n\), by expanding \(1/\zeta(ks)\) and \(1/(1-2^{1-ks})\). Write their Dirichlet convolution as \(b\). Since \(c=\mu*b\), \(\sum_{m\le U}|c(m)|\le U\sum_n |b(n)|/n\ll U\). Partial summation then gives \(\sum_{m\le L}|c(m)|/m\ll\log(2L)\) and \(\sum_{m\le L}|c(m)|m^{v-1}\ll_v L^v\) for fixed \(v>0\). Subtract \(\log R\) times the first row in the log equation and divide the two power rows by their natural powers of \(R\). The fixed inverse matrix and the preceding bounds give \(a_{4^iR}=O(\log^2(2L))\). Hence

\[
 \sum_m |a_m|m^v\ll_v L^v\log^2(2L)\qquad(v>0\ \text{fixed}).            \tag{7}
\]

Define \(J(y)=\sum_m a_mJ_m(y)\). Its Dirichlet coefficients equal those of \(H(s)\sum_m a_m(1-m^{1-s})\). Through index \(L\), the second factor has coefficients \(1,c(2),\ldots,c(L)\), by (6) and the definition of \(a_m\). Therefore the product equals 1 at index 1 and 0 at every \(2\le n\le L\). For \(L<n\le2L\), all proper divisors lie at most \(L\), and the second factor's coefficient at \(n\) is 0. Since \(h*c\) is the unit, the product's coefficient is exactly \(-c(n)\). Thus \(J(y)=y-1\) for \(1\le y\le L+1\); for \(L<y\le2L\) we have

\[
 y-1-J(y)=\sum_{L<n\le y}c(n)(y-n).                                     \tag{8}
\]

On squarefree indices, \(c(n)=\mu(n)\). Proper-square and cube corrections are present at other indices, e.g. \(c(4)=1\). This fixes the sign and multiplicities at the first unresolved band.

Let \(K_{x,L}(p)=x-p-pJ(x/p)\) for \(0<p\le x\). Its Lebesgue continuum integral is exactly zero: integrating each positive-part ramp on \([0,1]\) gives \(\int_0^1uJ_m(1/u)du=H_m(1)/2=\eta(2)\eta(3)\log m/2\) by continuation from Mellin exponents \(>1\). For justification of continuity at 1, the filter-only bound in the following paragraph provides a dominator. By (5)–(7) the sum of projected prime ramps is \(x^2/2-(2/3)x^{3/2}+O_\sigma(x^{1+\sigma}L^{1-\sigma}\log^2(2L))\). This error is \(o(x^{3/2})\) when \(\sigma>1/5\) is chosen sufficiently near \(1/5\), since \(\lambda<3/8\). The native sum \(\sum_{p\le x}(x-p)\log p\) equals \(A(x)+x^2/2-2\). Subtracting proves (1) before removal of the smallest primes; the original constant 2 is absorbed in the error.

## Absolute control on the oldest primes

The Mellin transform of \(J_m\) alone has multiplier \(H_m(s)\). Its pole at 1 is removable; the eta factors are entire. Shift its ramp contour to any fixed \(1/6<\tau<1/3\). The same three convexity factors now give vertical growth \(O_\tau((1+|t|)^{(3-6\tau)/2+\epsilon})\), with exponent strictly below 1. No \(V\) term restricts this contour. The denominator is still \(s(s+1)\); no pole is crossed. Exactly as for (4), for all \(y\ge1\),

\[
 |J_m(y)|\ll_\tau m^{1-\tau}y^{1+\tau},\qquad
 |K_{x,L}(p)|\ll_\tau x+x^{1+\tau}L^{1-\tau}\log^2(2L)p^{-\tau}.
\]

Chebyshev's upper bound and partial summation therefore bound the total absolute contribution of \(p\le x^\kappa\) by \(O_\tau(x^{1+\kappa}+x^{1+\tau+(\lambda+\kappa)(1-\tau)}\log^2(2x))\). Fix \(\tau\) close enough to \(1/6\) that the second exponent is below \(3/2\); this is possible since \(\lambda+\kappa<2/5\). This completes (1), including the small-prime cost. For \((\lambda,\kappa)=(0.37,0.025)\), \(\sigma=0.205\) gives error exponent \(1.49915\) in (5) after summation, and \(\tau=0.17\) gives \(1.49785\) for the deep-prime retirement.

## Simultaneous equality and shared arithmetic inputs

For the explicit exponents above, let \(S_{\rm eta}(x)\) be the sum in (1), and let \(S_{\rm fac}(x)\) be the sum in (1) of the factorial note with its externally supported choice \(L_0=\lfloor x^{0.11}\rfloor\). At the **same** real \(x\), both equal \(A(x)+(2/3)x^{3/2}+o(x^{3/2})\). Consequently

\[
 \frac{S_{\rm eta}(x)-S_{\rm fac}(x)}{x^{3/2}}\longrightarrow0 .
\]

Their summation primes are disjoint for sufficiently large \(x\), since \(x^{0.63}<x^{0.64}/(0.11\log x)^2\) eventually. Their full arithmetic inputs overlap. To form the factorial coefficients one can use the primes through \(L_0\) for Möbius inversion. The eta coefficients analogously use the primes through \(L=\lfloor x^{0.37}\rfloor\) for inverse coefficients and the same fixed normalization functions. In a direct inventory that includes the entire coefficient sieve and the specified summation primes, the two prime lists intersect in exactly the \(\pi(L_0)\) primes through \(L_0\), for all sufficiently large \(x\). This inventory does not assert minimal use of each prime or count global analytic inputs as finite data. In particular the common argument, normalization constants, and arithmetic relations are shared. Disjoint summation ranges supply no independence or covariance bound.

Equation (1) localizes the missing signed arithmetic input. An upper bound of the required strength for either signed sum remains open. These are paper deductions. No new Lean or production qualification is asserted.
