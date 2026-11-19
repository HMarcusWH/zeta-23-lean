# Which interaction graphs can carry the native prime energy?

**19 November 2026. Paper deduction, with Step 4 OPEN.** There is a precise consequence of the bounded-width intuition for the genuine arithmetic response. On the native terminal window, *any* family of pair graphs of subexponential maximum degree contributes subexponentially, even when the family is chosen adaptively from the arithmetic data. This includes every additive lag up to \(\exp(\sqrt n)\). An off-line zero would require a large net positive contribution from the remaining ordinary-prime pairs at every sufficiently late integer horizon.

## The source and the independent observation theorem

Put \(s=1/4096,\ j=(D^2-1/4)^2q_s\), the repository's one-copy source, and \(P(t)=\sum_{m\ge2}\Lambda(m)m^{-1/2}j(t-\log m)\). Write \(d\) for the zero-displacement supremum from the native theorem. With \(I_n=[n-2\log n,n]\), its compiler-checked conclusion gives
\[
 \frac{\log(1+V_n)}{2n}\longrightarrow d,\qquad V_n=\int_{I_n}|P(t)|^2dt.
\]
Specialize the source index to zero and the window coefficient to 2. At this stage one may restrict to integers because the theorem holds at every continuous horizon tending to infinity. The graph witnesses connect its proof to the actual source and the sinc product. The geometric decay estimates for the companion two-lobe detector use the different, two-copy multiplier. [Native window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154) · [Source and exact histories](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · [Formal Gevrey bound](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincInverseGevreyBounds.lean)

The source derivative estimate gives \(\|j^{(m)}\|_\infty\le C B^m(m!)^2\). Four extra derivatives of the seed cost a polynomial in \(m\), absorbed by a fixed increase of \(B\). Compact support and \(\psi(x)\ll x\) then give \(|P^{(m)}(t)|\le C' e^{t/2} B^m(m!)^2\) for \(t\ge1\). By the product rule \(|(P^2)^{(m)}(t)|\le C''e^t B_1^m(m!)^2\) for fixed \(B_1\ge1\), since \(\sum_{k=0}^m\binom mk^{-1}\le 2^m\) for \(m\ge1\).

Use \(J_n=\lceil 2\log(n)e^3B_1 n\rceil\) equal panels on \(I_n\). On each take the ordinary \(n\)-node positive Gauss–Legendre rule. All \(O_j(n^2\log n)\) nodes and weights are fixed before the zero under consideration. Write \(t_i,w_i\) for this horizon's array, and \(Q_n=\sum_i w_i P(t_i)^2\). The degree-\((n-1)\) Taylor remainder on one panel is at most \(C''e^n(B_1n\,|I_n|/J_n)^n\le C''e^{-2n}\). Positivity and exactness give
\[
 |Q_n-V_n|\le 4C''\log(n)e^{-2n},\qquad \frac{\log(1+Q_n)}{2n}\longrightarrow d.
\]
The last inequality uses that \(\log(1+x)\) is 1-Lipschitz on \([0,\infty)\). The number of observation times says nothing about the computational cost of evaluating all the arithmetic pairs at one observation. [Quadrature exactness and positive weights](https://dlmf.nist.gov/3.5.v)

## A paid bound uniform over interaction graphs

At node \(i\) set \(v_m=\Lambda(m)m^{-1/2}j(t_i-\log m)\). Only finitely many terms occur. For \(t_i\in I_n\) and \(n\) sufficiently large, \(m\in[e^{t_i-s},e^{t_i+s}]\) whenever \(v_m\ne0\). Using \(\Lambda(m)^2\le(\log m)\Lambda(m)\) and Chebyshev's upper for \(\psi\),
\[
 \sum_m v_m^2\le C_j(1+n),\qquad
 D_n:=\sum_i w_i\sum_m v_m^2=O_j(n\log n).
\]
For any undirected simple graph \(G_i\) on these indices, of maximum degree at most \(D\), the edgewise inequality \(2|v_m v_l|\le v_m^2+v_l^2\) proves
\[
 \sum_i w_i\sum_{\{m,l\}\in G_i}2|v_m v_l|\le D D_n.
\]
This estimate holds for graphs depending on the sample time, the signs, or the actual coefficients. All remaining pairs are explicitly restored. In particular \(|m-l|\le e^{\sqrt n}\) costs \(O_j(n\log n\,e^{\sqrt n})\) even with absolute values. If \(d>0\), fix any \(0<\alpha<2d\). Removing a graph with \(D\le e^{\alpha n}\), and the diagonal, leaves a signed sum that is eventually positive and has logarithmic rate \(2d\) per unit \(n\). Indeed \(Q_n=\exp((2d+o(1))n)\) and the removed terms are \(O_j(n\log n\,e^{\alpha n})\).

The diagonal has an asymptotic as well. For ordinary primes its value at time \(t\) is \(\int (\log y)y^{-1}j(t-\log y)^2\,d\vartheta(y)\). On the compact-ratio support the prime number theorem and one integration by parts replace \(d\vartheta(y)\) by \(dy\) with error \(o_j(t)\). Indeed the derivative of the integrand is \(O_j(t/y^2)\), and the endpoint terms vanish. The main term is \(\int(t-v)j(v)^2dv=t\|j\|_2^2\) by evenness. Proper prime powers contribute \(O_j((1+t)^2e^{-t/2})\) to this diagonal, by Chebyshev on the prime bases. Since the smallest node tends to infinity, \(D_n\sim 2\|j\|_2^2 n\log n\). This supplies the leading constant in the bound for low-degree graphs.

## Restore all higher prime powers

Split the *field* as \(P=P_{\rm prime}+R\), where \(R\) contains every exponent \(k\ge2\). Uniformly for late \(t\), put \(X=e^{t+s}\). For squares the unnormalized sum of \(\log p\) is \(O(\sqrt X)\) by Chebyshev. Exponents \(k\ge3\) give \(O(X^{1/3}\log X)\) by the same estimate, since \(k\le\log_2 X\). Multiplication by \(\|j\|_\infty e^{-(t-s)/2}\) yields \(|R(t)|\ll_j1\). Thus
\[
 \left|\sqrt{Q_n}-\Big(\sum_i w_i P_{\rm prime}(t_i)^2\Big)^{1/2}\right|
 \le C_j\sqrt{2\log n}.
\]
The actual higher-power field even tends to \(1/32\). Its square-prime contribution is \(\int y^{-1}j(t-2\log y)\,d\vartheta(y)\). On the fixed-ratio interval for the bases the prime number theorem gives a substitution error \(o_j(1)\) by integration by parts. The main term is \(\tfrac12\int j=1/32\) since \(j=(D^2-1/4)^2q_s\) and \(\int q_s=1\). The exponents at least three cost \(O_j((1+t)e^{-t/6})\). This constant belongs to the one-copy source.

The norm inequality handles the mixed terms in both directions. If \(d>0\), prime-only energy also equals \(\exp((2d+o(1))n)\). If the prime-only norm has a subexponential upper on a cofinal sequence, the same is true of the full norm there. The mixed prime/power term still depends on the size of the prime field.

Take \(G_i\) on ordinary primes to contain every additive gap at most \(e^{\sqrt n}\). A sufficient closing inequality is now particularly concrete. Denote by \(S_n\) the signed sum
\[
 2\sum_i w_i\!\!\sum_{\substack{p<q\ {\rm prime}\\q-p>e^{\sqrt n}}}
 \frac{\log p\log q}{\sqrt{pq}}\;j(t_i-\log p)j(t_i-\log q).
\]
The two supports already enforce \(|\log(q/p)|\le2s\). It suffices that, for every \(\eta>0\), there be a fixed \(C_\eta\) and arbitrarily large integers \(n\) with \(S_n\le C_\eta e^{\eta n}\). The diagonal and the discarded near pairs have independent subexponential bounds. The norm inequality then restores every higher prime power. Conversely if \(d>0\), \(S_n=\exp((2d+o(1))n)\) at all sufficiently large integers. This direction identifies the signed excess an arithmetic proof must prevent.

Taking absolute values across the remaining pairs would discard the needed cancellation. On a fixed subinterval where \(j\) has one sign and magnitude bounded below, the prime number theorem gives an unsigned pulse mass \(\gg_j e^{t/2}\). Squaring, removing the \(O_j(n)\) diagonal and the paid near pairs, and summing over panels in the terminal unit interval gives \(\sum_i w_i\sum_{\rm far}|2v_p v_q|\gg_j e^n\). The complete panels contained in that interval have total weight at least \(1-2|I_n|/J_n\). This diagnosis concerns absolute values *before* summing over nodes.

**OPEN.** The graph calculation controls all low-degree contributions. The remaining graph of prime pairs is dense in the narrow multiplicative band. The independent, cofinal signed upper for \(S_n\) has not been proved. The finite original-trial exclusion in the companion report has different quantifiers and a different source.
