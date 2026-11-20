# Which prime-pair graphs can carry a rightward zero?

**19 November 2026. Paper deduction.** If the actual rightward displacement supremum \(d\) is positive, every sufficiently late native window receives asymptotically its entire prime-field energy from the signed interaction of *distinct primes* outside any prescribed graph having \(O(x^\alpha)\) partners per prime in the multiplicative shell \(p\asymp x\), whenever \(\alpha<2d\). This applies to the graph containing all gaps \(|p-q|\le p^\alpha\). Every higher prime power, both mixed terms and the prime diagonal have explicit smaller exponential rates. The conclusion uses the one-copy source without a positivity assumption on the remaining sum.

Write \(w_m(t)=m^{-1/2}j(t-\log m)\) and \(P=J_1+H\), where \(J_1=\sum_p (\log p)w_p\) includes only first-power primes, and \(H=\sum_{p,\nu\ge2}(\log p)w_{p^\nu}\). For a chosen set \(G\) of ordered pairs of distinct primes, split
\[
 P^2=W_G+B_G+2PH-H^2,\quad
 B_G=\sum_p(\log p)^2w_p^2+\sum_{(p,q)\in G}\log p\log q\,w_pw_q,
\]
where \(W_G\) is the ordered sum over distinct primes outside \(G\). This pays both orientations exactly. Including only pairs oriented by \(p<q\) and doubling requires a symmetric selection.

At time \(t\) only indices in \([e^{t-s},e^{t+s}]\) contribute, with \(s=1/4096\). Up to \(x\), the sum of \(\log p\) over higher powers costs \(O(\sqrt{x}(1+\log x)^2)\) by counting exponents and possible bases. Hence \(|H(t)|\ll_j(1+t)^2\). The native explicit formula gives \(|P(t)|\ll_j e^{dt}\) including the bounded initial interval. For fixed \(0\le\alpha\le1\), suppose each \(p\) has at most \(C p^\alpha\) outgoing partners in \(G\) with \(e^{-2s}p\le q\le e^{2s}p\). Counting at most \(O(e^t)\) bases, bounding the logarithms by \(O(1+t)\), and retaining the two factors \(m^{-1/2}\) gives
\[
 |B_G(t)|\ll_{j,G}(1+t)^2e^{\alpha t},\qquad
 |2P(t)H(t)-H(t)^2|\ll_j (1+t)^4 e^{dt}. \tag{1}
\]
The second inequality uses the complete actual field. Bounding the prime-only field independently by elementary counting would instead charge an exponent \(1/2\) in this term.

For fixed \(C_0>1\) take the exact native window \(I_T=[T-C_0\log T,T]\). Its full energy for \(d>0\) has logarithm \((2d+o(1))T\). Whenever \(\alpha<2d\), (1) therefore proves the strict comparison
\[
 \frac{\int_{I_T} W_G(t)dt}{\int_{I_T}P(t)^2dt}\longrightarrow1 . \tag{2}
\]
Indeed the discarded *absolute error* is at most \(O_{j,G,C_0}((1+T)^4\log T\,e^{\max(d,\alpha)T})\), while \(\max(d,\alpha)<2d\). In particular (2) proves the signed sum in its numerator is positive at every sufficiently late horizon under the hypothetical zero. Subtracting the actual \(E_Y\) also changes neither side's leading growth, since its terminal integral is \(O_Y(\log T)\). On gamma-weighted complete histories from [the fixed-line note](FIXED_LINE_JETS.md) the same estimate shows \(\int W_Gd\mu_k/A_k\to1\). Integrating a fixed polynomial times \(e^{\beta t}\) against \(\mu_k\) costs \(O_\beta((1+k)^4(1-\beta/2)^{-(2k+1)})\) for \(\beta<2\). The full growth factor is \((1-d)^{-2k+o(k)}\). [Native window rate](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154) · [Fixed diagonal](../FIXED_SIEVE_SIGN.md)

A concrete threshold requiring no input about \(d\) is \(|p-q|\le\exp(\sqrt{\log\min(p,q)})\). This graph satisfies the degree bound for **every** \(\alpha>0\). Thus it can be removed in (2) for any hypothetical \(d>0\), however small. More generally, if an *independent arithmetic argument* bounds the signed wide-pair integral from above by \(O(e^{\kappa T})\) on unbounded horizons for a graph with degree exponent \(\alpha\), then \(d\le\max(\kappa,\alpha)/2\) for \(\kappa\ge0\). Otherwise (2) contradicts that upper on the same horizons. This yields an intermediate quantitative target. For the displayed subpower gap threshold, upper bounds for every \(\kappa>0\) suffice to close Step 4. No such independent wide-pair upper is established here. Positivity of an isolated near-diagonal sum has no implication for that sign.

## The literal double Dirichlet series

For \(\Re z>1\), absolute convergence and the support of \(j\) give
\[
 \int_0^\infty e^{-zt}J_1(t)^2dt
  =\sum_{p,q}\frac{\log p\log q}{(pq)^{(1+z)/2}}
    K_z(\log(p/q)),\qquad
 K_z(v)=\int_{\mathbb R}e^{-zu}j(u-v/2)j(u+v/2)du .
\]
Each pair is paid exactly. \(K_z(v)=0\) for \(|v|>2s\). It is entire in \(z\) and bounded uniformly on compact \(z\)-sets for all \(v\). The prime diagonal converges absolutely on \(\Re z>0\). Every \(G\)-portion with the above degree bound converges absolutely and locally uniformly on \(\Re z>\alpha\), by comparison with \(\sum_{m\ge2}(\log m)^2m^{-1-\Re z+\alpha}\). The transform of \(2PH-H^2\) is holomorphic for \(\Re z>d\) by (1). Thus if \(d>0\) and \(\alpha<2d\), the rightmost real singularity at \(2d\) established for the positive square survives in the complementary distinct-prime Dirichlet expression. The precise statement concerns the continuation afforded by the time integral. No absolute convergence of the unrestricted complement at that point is asserted. An upper based on smooth continuum correlations or individually fixed shifts would have to control this entire remaining signed sum uniformly as its offsets grow.
