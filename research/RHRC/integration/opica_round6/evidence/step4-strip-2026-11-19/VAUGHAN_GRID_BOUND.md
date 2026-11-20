# A power saving for the centered prime contribution to the power grid

**DERIVED on paper.** Write \(e(t)=\exp(2\pi i t)\). For \(1/3\le\theta\le1/2\), \(X\ge2\), \(1\le h\le X^{1/6}\) integral and every interval \(I\subset[X,2X]\),
\[
 \left|\sum_{m\in I}\Lambda(m)e(hm^\theta)\right|
 \ll_\epsilon X^{5/6+\epsilon}.                                      \tag{1}
\]
The constant may be chosen uniformly on this closed \(\theta\)-range. The estimate counts the genuine von Mangoldt weights, including all prime powers, and it holds for each prefix of the dyadic interval. For every fixed \(\theta>1/3\) in the range the exponent is strictly below \(1/2+\theta\) after choosing \(\epsilon<\theta-1/3\). In particular \(\theta=3/8,\ 0.49,\ 0.499,\ 1/2\) all have strict saving. This supplies one centered arithmetic term in the proposed grid projection. No bound for the full uncentered prime response is being assumed.

## The convolution and the ranges

Use real cutoffs \(U=V=X^{1/3}\) and subscripts \(\le U\) and \(>U\) for truncated arithmetic functions. With \({\bf1}(m)=1\), the exact Vaughan identity reads
\[
 \Lambda
 =\Lambda_{\le V}+\mu_{\le U}*\log
 -(\mu_{\le U}*\Lambda_{\le V})*{\bf1}
 +(\mu_{>U}*{\bf1})*\Lambda_{>V}.
\]
It follows directly from \(\log={\bf1}*\Lambda\) and \(\mu*{\bf1}={\bf1}_{m=1}\). The first term vanishes on \(I\). The second has a coefficient on \(d\le U\) and a free inner variable with log weight. The third has an outer coefficient \(a_d=(\mu_{\le U}*\Lambda_{\le V})(d)\) on \(d\le UV\), with \(|a_d|\le\sum_{v\mid d}\Lambda(v)=\log d\), and a free unweighted inner variable. Treat \(d\le X^{1/3}\) in this third term by the same free-variable bound as in the second. For \(X^{1/3}<d\le X^{2/3}\), both factors in a nonempty product \(dk\in I\) are at least a constant times \(X^{1/3}\). Move that part into the bilinear estimate below. In the fourth term both factors already exceed \(X^{1/3}\), and \(|(\mu_{>U}*{\bf1})(d)|\le\tau(d)\), \(|\Lambda(k)|\le\log k\). All coefficient and dyadic subdivision costs are absorbed by \(X^\epsilon\), starting with a sufficiently smaller exponent in the elementary divisor bound. [Montgomery–Vaughan, chapter 17, especially the identity (17.5) and bilinear partition (17.53)](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)

Put \(F=hX^\theta\), so \(X^{1/3}\le F\le X^{2/3}\). For \(d\le X^{1/3}\), \(k\asymp K=X/d\), the second derivative of \(h(dk)^\theta\) in \(k\) has absolute value comparable to \(F/K^2\). The ordinary second-derivative estimate on every inner subinterval gives \(O(\sqrt F+K/\sqrt F)\). Partial summation costs \(O(\log X)\) when the inner weight is \(\log k\). Summing the permitted \(d\)'s costs
\[
 O_\epsilon\!\left(X^\epsilon[X^{1/3}\sqrt F+X/\sqrt F]\right)
 \ll_\epsilon X^{5/6+\epsilon}.
\]
The constants in the second derivative are uniform since \(\theta(1-\theta)\) is bounded above and below away from zero on the indicated compact range.

## The bilinear estimate

Dyadically split \(m\asymp M,\ k\asymp N\) and swap the two independent coefficient sequences if necessary so that \(M\ge N\). On a nonempty rectangle \(MN\asymp X,\ M\gg \sqrt X,\ N\gg X^{1/3}\). The weight is \(a_m b_k{\bf1}_{mk\in I}\); truncation endpoints such as \(d\le X^{2/3}\) are put in the appropriate individual interval. Bound the coefficients by \(O_\epsilon(X^\epsilon)\) as above.

Partition the shorter \(k\)-interval into consecutive blocks of integer length at most
\[
 Q=\max(1,\lfloor c\min(N,MN/F)\rfloor)
\]
with a sufficiently small absolute \(c>0\). In the displayed parameter ranges the quantity in the floor tends to infinity uniformly as \(X\to\infty\); enlarge constants for bounded \(X\). The number of blocks is \(O(N/Q)\). For \(k_1,k_2\) in the same block a distance \(j\ge1\) apart, the differenced phase in \(m\) is \(g(m)=h(k_1^\theta-k_2^\theta)m^\theta\). Its derivative is monotone, of fixed sign, and
\[
 |g'(m)|\asymp Fj/(MN),\qquad |g'(m)|\le1/2.
\]
The first assertion follows twice from the mean value theorem on dyadic intervals. The second follows from the choice of \(c\). The simultaneous restrictions \(mk_1\in I\) and \(mk_2\in I\) leave an interval. The first-derivative exponential sum estimate on this interval therefore gives \(O(MN/(Fj))\). One can see the estimate by writing the summand as a successive difference divided by \(e(g(m+1)-g(m))-1\) and summing by parts; the reciprocal denominator has total variation \(O(MN/(Fj))\) because the phase increments are monotone and remain at that distance from an integer. Reversing signs conjugates the sum.

Apply Cauchy–Schwarz first over blocks and then to the \(m\)-coefficients in each block. The diagonal after summing over blocks contributes \(O_\epsilon(X^\epsilon M^2 N)\) before multiplication by the number of blocks. For each nonzero distance \(j\le Q\), there are at most \(O(N)\) pairs in all blocks together. The preceding derivative bound and the \(m\)-Cauchy factor give an off-diagonal of \(O_\epsilon(X^\epsilon M^2N^2/F)\), with the sum over \(1/j\) absorbed. Thus the bilinear sum \(S\) satisfies
\[
 \frac{|S|^2}{(MN)^2}\ll_\epsilon
 X^\epsilon\left(\frac1Q+\frac{N}{FQ}\right)
 \ll_\epsilon X^\epsilon
 \left(\frac1N+\frac F{MN}+\frac1F+\frac1M\right)
 \ll_\epsilon X^{-1/3+\epsilon}.
\]
When \(F\) is below a sufficiently small multiple of \(M\), a single block or a fixed number of blocks suffices. When \(F\) is larger, the shorter blocks keep the differenced derivative away from nonzero integer resonances. This common argument proves (1) even at \(\theta=3/8\), where treating all pairs by an unblocked second derivative with cutoffs \(X^{1/4}\) would leave no strict margin in its diagonal estimate.

## Sawtooth, endpoints and weights

For a circle interval \(A\) use the weighted Erdős–Turán inequality, with the finite positive measure \(\sum_{m\in I}\Lambda(m)\delta_{\{m^\theta\}}\). Its deviation from \(|A|\sum_{m\in I}\Lambda(m)\) is at most a constant times
\[
 \frac{\sum_{m\in I}\Lambda(m)}{H+1}+
 \sum_{h=1}^{H}\frac1h\left|\sum_{m\in I}\Lambda(m)e(hm^\theta)\right|.
\]
The usual trigonometric majorant and minorant can be integrated against these positive weights. Taking \(H=\lfloor X^{1/6}\rfloor\), using the elementary total \(O(X\log X)\) and (1), bounds the expression by \(O_\epsilon(X^{5/6+\epsilon})\). Translating the arc by any fixed or variable phase leaves this bound uniform. Arcs of arbitrarily short length also bound the mass at an exact jump by the same error. Integrating the arc estimate yields, for every real \(v\),
\[
 \sup_{I\subset[X,2X]}
 \left|\sum_{m\in I}\Lambda(m)\bigl(\{m^\theta+v\}-1/2\bigr)\right|
 \ll_\epsilon X^{5/6+\epsilon}.                                  \tag{2}
\]
Either value convention at an exact integer is admissible. More generally, any periodic, bounded-variation test of mean zero costs its total variation times this bound (using the above atom bound if separate point values are assigned). A second real or complex weight \(b(m)\) of bounded variation on the dyadic interval costs a factor \(\sup|b|+\operatorname{Var} b\) by partial summation using the uniform prefix estimates. No coefficient sign is removed before applying (1).

If the test is wanted on ordinary primes alone, removing all higher prime powers from (1) or (2) costs \(O(\sqrt X\log^2 X)\) by elementary counting, uniformly on subintervals. For \(\theta>1/3\) the stricter target \(o(X^{1/2+\theta})\) for the sawtooth follows. One may instead truncate at \(H=X^{1/2-\theta+\eta}\) with \(0<\eta<\theta-1/3\). Both the truncation term and the nonconstant harmonics then retain a strict margin. At \(\theta=1/3\), (1) and (2) still hold, but the displayed proof supplies no strict saving over \(X^{1/2+\theta}=X^{5/6}\).
