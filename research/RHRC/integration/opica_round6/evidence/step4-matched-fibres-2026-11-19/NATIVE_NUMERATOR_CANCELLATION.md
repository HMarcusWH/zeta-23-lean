# A larger range of frequencies at the actual origin

19 November 2026. **DERIVED on paper.** At the largest denominators, summing over numerators before taking absolute values lowers the sufficient numerator threshold from \(L^{1/3}\) to \(L^{1/4}\) on the first dyadic interval. This uses the exact shared coefficient of the genuine graph. It also works at all integer shifts. The remaining native signed sum is open.

Use the fixed distributed calibration and the variables of [the residue-graph calculation](PERIOD_AND_NATIVE_PHASE.md). Set \(S_q=\sum_{q\mid m}a_m\). For \(q\asymp D,\ h_*=\min(h,q-h)\asymp K\), the coefficient of \(e(hn/q)\), \(e(z)=\exp(2\pi i z)\), is exactly \(-S_q/(4\sin^2(\pi h/q))\). In particular \(|S_q|\ll q^{-1}\log^3(2L)\), since \(|a_m|\ll\log^2(2L)/m\) and \(m\le CL\) for a fixed \(C\). Use the half-open dyadic conventions from the earlier note.

## Sum numerators before moduli

Fix \(q\). Work first on \(K\le h<2K,\ h\le q/2\). The interval at the upper end can be shorter. For any prefix ending at \(v\) its coprime sum is exactly
\[
 \sum_{\substack{K\le h\le v\\(h,q)=1}} e(hn/q)
 =\sum_{d\mid q}\mu(d)\sum_{K\le dj\le v} e(jn/(q/d)).
\]
The inner interval has at most \(Q=q/d\) terms. Uniformly over its endpoints its absolute value is bounded by \(Q\) when \(Q\mid n\) and by \(1/|\sin(\pi n/Q)|\) otherwise. The average of this common envelope over \(n\bmod Q\) is \(O(\log(2Q))\), by pairing the residues \(r,Q-r\) and using \(\sin(\pi r/Q)\ge2r/Q\) for \(1\le r\le Q/2\). This also covers \(Q=1\). The same estimate holds for the maximum over all prefixes, since the envelope depends only on the residue. For \(N\) consecutive sites with any integer starting point, an enclosing union of \(\lceil N/Q\rceil\) consecutive \(Q\)-periods gives the same mean bound up to \(1+Q/N\le1+C\) when \(N\ge L\).

On the selected half, the factor \(\sin^{-2}(\pi h/q)\) is positive, monotone and \(O(q^2/K^2)\). Summation by parts against the prefix estimate bounds its weighted sum by that initial weight times the common prefix envelope. Reflect the upper half and count \(h=q/2\) only once. Hence on any \(N\ge L\) consecutive sites the mean absolute contribution of this \(q,K\) is at most
\[
 O_C\!\left(|S_q|(q/K)^2\tau(q)\log(2q)\right).
\]
Summing over \(D\le q<2D\), using \(\sum_{q<2D}\tau(q)\ll D\log(2D)\) by counting products, gives
\[
 \boxed{\ \frac1N\sum_{n=n_0+1}^{n_0+N}|F_{D,K}(n)|
       \ll_C \frac{D^2}{K^2}\log^5(2L) .\ }                         \tag{1}
\]
Absolute values across denominators are permitted only for this upper. Within each denominator the signed Fourier sum and its common \(S_q\) enter before taking the absolute value. Arbitrary independent coefficients for its numerators could invalidate this gain.

## Combine the two bounds at each site scale

On \(N<n\le2N\) the weighted absolute contribution from (1) is \(O_C(N^{-2}D^2 K^{-2}\log^5(2L))\). The dual large sieve in the previous note instead gives
\[
 O_C\!\left(\log^3(2L)\big[N^{-2}D^{3/2}K^{-3/2}
             +N^{-5/2}D^{5/2}K^{-3/2}\big]\right).
\]
For \(D\le CL,\ N\ge L,\ K\ge1\), the first term is already at the critical power \(L^{-1/2}\). Thus a rectangle is controlled on this block whenever **either** of the following holds:
\[
 \boxed{\quad D^5 L\le N^5K^3 \qquad\text{or}\qquad
                 D^4 L\le N^4K^4 .\quad}                              \tag{2}
\]
Take \(N=2^jL\), \(j\ge0\). For each \(D,K\), the scales satisfying each of the two conditions separately form a terminal string. Summing the respective geometric powers \(N^{-2},N^{-5/2}\) from the earliest qualifying scale bounds all contributions from the union, allowing an overlap in this *upper estimate*. Each rectangle then costs \(O_C(L^{-1/2}\log^5(2L))\). There are \(O_C(\log^2(2L))\) rectangles. A final partial block may be extended for the nonnegative estimates. The full joint contribution from (2), with each rectangle counted once in the actual Fourier sum on each block, is \(O_C(L^{-1/2}\log^7(2L))\).

At \(N=L\), the sufficient threshold for \(K\) is the smaller of \(D^{5/3}/L^{4/3}\) and \(D/L^{3/4}\). They intersect at \(D=L^{7/8}\). Every rectangle with \(K\gg_C L^{1/4}\) is now controlled. At \(N\asymp L^{1.01}\) every rectangle with \(K\gg_C L^{0.24}\) is controlled. Small denominators \(D\lesssim N L^{-1/5}\) are already covered by the first condition.

## What would close the remaining estimate

For an integer \(n>L\) in the finite statistic, let \(N=N(n)\) be the unique \(2^jL\) with \(N<n\le2N\). Define
\[
 H_L=\sum_{L+\lfloor L^{5/6}\rfloor<n\le\lfloor L^{1.01}\rfloor}
  n^{-3}\left|
  \sum_{\substack{D^5L>N(n)^5K^3\\ D^4L>N(n)^4K^4}}
        F_{D,K}(n)\right|.
\]
The bound just proved, the first native interval estimate, and the reverse triangle inequality give
\[
 \left|H_L-\mathcal B_L(0)\right|\ll_C L^{-1/2}\log^7(2L).
\]
The absolute value is outside the full remaining signed sum at the prescribed origin. For every \(\varepsilon>0\), a proof of \(H_L\le L^{-1/2+\varepsilon}\) at arbitrarily large integers \(L\) suffices. If there is a rightward zero, \(H_L\) has exponent \(B-1\) along all large integer cutoffs. In particular the sector \(D\asymp N\asymp L,\ K=1\) still evades both independent bounds. The paper criterion and the preceding estimates do not establish the requested inequality. [Proof of the exponent](RESIDUE_GRAPH_CRITERION.md) · [Exact finite knot calculation](lean-period/FactorialKnot.lean.md)
