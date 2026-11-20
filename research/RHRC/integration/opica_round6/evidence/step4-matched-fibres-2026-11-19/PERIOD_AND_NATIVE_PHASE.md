# Critical energy over the full residue graph and the frequencies left at its native origin

19 November 2026. **DERIVED on paper.** The source's residue graph has the required mean-square scale over a complete period. At the actual origin, an independent large-sieve calculation pays every frequency rectangle except the large-denominator, small-numerator range specified below. The critical bound on that remaining signed sum is **OPEN**.

## Choose a centered graph without altering the actual Möbius input

Fix an integer \(L\) and retain \(a_m=-\mu(m)/m\) for \(2\le m\le L\). For each \(R\in(2L,3L]\) divisible by 9 choose three rational corrections at \(R,2R,4R\) to impose
\[
 \sum a_m=1,\qquad \sum ma_m=3,\qquad \sum m^2a_m=13 .
\]
Average over these \(R\), for all \(L\) large enough that the set is nonempty. The rescaled three-by-three matrix is an ordinary Vandermonde matrix at \(1,2,4\). The residual right sides after division by \(1,R,R^2\) are \(O(\log(2L))\) even using absolute values. Each \(m\) can occur at at most three extra positions before averaging, so the complete finite list satisfies \(|a_m|\ll\log(2L)/m\), with support \(m\le12L\). The conditional upper refinement \(O_s(L^{s-1}\log^2 L)\) for the sum of absolute extra weights for \(s>B\), \(B<1\), follows from the same partial summation as for the native four-moment list.

An alternative retains the two additional factorial moments \(\sum a_m\log m=1\) and \(\sum a_m(1-\sqrt m)=1/\zeta(1/2)\) as well, using five corrections \(4^kR,0\le k\le4\). The normalized rows \(1,k,2^k,4^k,16^k\) have an invertible confluent Vandermonde matrix. Now \(|a_m|\ll\log^2(2L)/m\), \(m\le768L\). This variant retains the original factorial prime-area normalization and native Möbius prefix. The rational three-moment variant uses the separate direct Mellin identity at the actual zeta zeros; it does not require the two extra moment targets. Both have the same absolute residue criterion from the [direct analytic proof](RESIDUE_GRAPH_CRITERION.md).

At \(n\in\mathbb Z\) put \(b_m(n)=r(m-r)\) with \(r=n\bmod m\). The residue statistic is
\[
 E_L(n)=-1+\tfrac12\sum_m a_m b_m(n),\qquad
 \mathcal B_L(t)=\sum_{L<n\le\lfloor L^{1.01}\rfloor}\frac{|E_L(t+n)|}{n^3}.
\]
Here \(t=0\) is the true origin. From the actual Mellin response and interpolation on the integer grid, \(\mathcal B_L(0)=L^{B-1+o(1)}\) at every sufficiently large integer cutoff in the logarithmic-exponent sense. In particular arbitrarily large \(L\) meeting \(L^{-1/2+\epsilon}\) for each \(\epsilon>0\) suffice to exclude an off-line zero. This note derives independent bounds for the finite graph using integer residues.

## Exact mean, covariance and exceptional shifts

Let \(P\) be the lcm of the nonzero coefficient indices. For \(t\) uniform modulo \(P\), write \(\langle\cdot\rangle\) for the arithmetic mean. The elementary sums of the first two powers give \(\langle b_m\rangle=(m^2-1)/6\), hence \(\langle E_L\rangle=0\) exactly. Let \(g=\gcd(m,k)\). Conditional on \(t\bmod g=r\), the residues modulo \(m\) and \(k\) are independent uniform choices within that common class, by the Chinese remainder theorem. Substitution of \(r+gh\) for \(h=0,\ldots,m/g-1\) gives
\[
 \mathbb E[b_m(t)\mid t\bmod g=r]=b_g(r)+(m^2-g^2)/6 .
\]
Consequently \(\operatorname{Cov}(b_m,b_k)=\operatorname{Var}(b_g)=(g^4+10g^2-11)/180\); the last equality follows by summing the powers up through four. In particular, for the entire signed graph,
\[
 \langle E_L^2\rangle=\frac1{720}\sum_{m,k}a_ma_k
       \big(\gcd(m,k)^4+10\gcd(m,k)^2-11\big)\ll L^3\log^4(2L).
\]
For the upper, write \(m=gu,\ k=gv\), discard the coprimality restriction for the absolute estimate, and use \(\sum_{g\le CL}g^2(1+\log(CL/g))^2\ll_C L^3\). This sums every cross term. Cauchy–Schwarz in the period variable gives \(\|\mathcal B_L\|_{2,t}\le\sum_{n>L}n^{-3}\langle E_L^2\rangle^{1/2}\ll L^{-1/2}\log^2(2L)\). For any \(\epsilon>0\) the fraction of shifts where \(\mathcal B_L(t)>L^{-1/2+\epsilon}\) is \(O(L^{-2\epsilon}\log^4 L)\).

The full-period exponent for \(E_L^2\) is sharp. The Jordan totient identity \(g^a=\sum_{d\mid g}J_a(d)\) gives \(720\langle E_L^2\rangle=\sum_{d>1}(J_4(d)+10J_2(d))(\sum_{d\mid m}a_m)^2\). For every squarefree \(L/2<d\le L\) coprime to 6 only its own low coefficient contributes. Indeed \(d\mid 2^kR\) implies \(d\mid R\); then \(9d\mid R\), impossible at \(R\le3L\). Such integers have positive density, for example by inclusion-exclusion with \(\mu(k)/k^2\) on integers coprime to 6. Since \(J_4(d)\ge d^4/\zeta(4)\), this subsum alone is \(\gg L^3\).

The actual initial plateau is a rare phase. Each prime \(p\in(L/2,L]\) occurs only at its own nonzero modulus, by the same argument. Its forward difference in \(E_L\) equals \((p-1)/(2p)-(t\bmod p)/p\). Condition on the residues at every other modulus, excluding all of these primes. The remaining prime coordinates are independent. The possible sums of fractional parts of their variable slopes are a translated grid of exactly \(Q=\prod_{L/2<p\le L}p\) points, each with probability \(1/Q\). Two consecutive equal values therefore occur with conditional probability at most \(1/Q=\exp[-(1/2+o(1))L]\), by ordinary PNT. The native filter has \(E_L(1)=\cdots=E_L(L+1)=0\). This explains why Markov's inequality for random shifts cannot certify the native start.

## A uniform payment on every phase by Fourier denominator and numerator

For \(q\ge2,\ 1\le h<q,\ (h,q)=1\), write \(h_*=\min(h,q-h)\) and \(e(z)=e^{2\pi i z}\). The exact centered expansion at the integer sites is
\[
 E_L(n)=\sum_{q,h} A_{q,h}\,e(hn/q),\qquad
 A_{q,h}=-\frac{\sum_{q\mid m}a_m}{4\sin^2(\pi h/q)} .
\]
Indeed the periodic second difference of \(b_m\) is constant \(-2\) away from residue 0 with an extra \(2m\) at 0. Division of each nonzero Fourier coefficient by \(-4\sin^2(\pi h/q)\), followed by the factor \(1/2\) in \(E_L\), gives the formula. The average is already zero. There is one coefficient per reduced frequency, summed over every contributing modulus. Thus \(|A_{q,h}|\ll q\log^3(2L)/h_*^2\).

Split the reduced frequencies into dyadic rectangles \(D\le q<2D,\ K\le h_*<2K\), with \(D\le C L\). On each, \(\sum |A_{q,h}|^2\ll D^3 K^{-3}\log^6(2L)\). Distinct reduced frequencies are separated on the unit circle by at least \(1/(4D^2)\). Put \(F_{D,K}(n)=\sum A_{q,h}e(hn/q)\) over that rectangle. The dual large sieve, on *any* consecutive \(N\) sites with \(N\ge L\), gives
\[
 \left(\frac1N\sum_{n=n_0+1}^{n_0+N}|F_{D,K}(n)|^2\right)^{1/2}
 \ll \log^3(2L)\,(1+D^2/N)^{1/2}D^{3/2}K^{-3/2}.
\]
The coefficient bound sums unordered frequencies as distinct residues including both conjugates; no independence of phases is used. [Montgomery and Vaughan, The large sieve](https://doi.org/10.1112/S0025579300004708)

Call a rectangle paid when \(D^5\le L^4 K^3\). Then the right side is \(O(L^{3/2}\log^3(2L))\) throughout \(N\ge L\). The first term uses \(D\le C L,\ K\ge1\); the second is exactly the stated rectangle condition. Sum the \(O(\log^2 L)\) rectangles by the triangle inequality in the normalized square norm. Divide the sites \(n>L\) into blocks \([2^j L,2^{j+1}L)\), extend the final block for the nonnegative square estimate, and bound the weighted absolute sum by Cauchy–Schwarz on each block. Summing the geometric weights yields
\[
 \sum_{L<n\le L^{1.01}}\frac{|\sum_{\rm paid}F_{D,K}(t+n)|}{n^3}
       \ll L^{-1/2}\log^5(2L)
\]
uniformly even at the actual shift \(t=0\). In particular all rectangles with \(D\le L^{4/5}\) are paid, as are those with \(K\gg_C L^{1/3}\). This estimate includes the constant mode by its exact cancellation above.

There is also a short range of sites already paid at the native shift. For \(L<n<2L\) the actual ramp is \(E_L(n)=\sum_{L<j\le n}\mu(j)(n-j)\). Hence for \(L<n\le L+\lfloor L^{5/6}\rfloor\), the native contribution to \(\mathcal B_L(0)\) is \(O(L^{-3}\sum_{h\le L^{5/6}}h^2)=O(L^{-1/2})\). Combining this with the paid rectangles by the triangle inequality leaves the exact sufficient upper
\[
 \sum_{L+\lfloor L^{5/6}\rfloor<n\le \lfloor L^{1.01}\rfloor}
 \frac1{n^3}
 \left|\sum_{D^5>L^4K^3} F_{D,K}(n)\right|
 \le L^{-1/2+\epsilon}
\]
at arbitrarily large integer \(L\), for every positive \(\epsilon\) (fixed constants or log powers are absorbed by choosing a smaller epsilon). This quantity retains the *signed* sum over the remaining rectangle coefficients before taking its modulus. In fact its difference from \(\mathcal B_L(0)\) in absolute value is \(O(L^{-1/2}\log^5(2L))\), by the reverse triangle inequality and the initial-site bound. If \(B>1/2\), it therefore has exponent \(B-1\) at every sufficiently large integer cutoff. The complete-period estimate meets the power on average over shifts. The native inequality above remains open. [Exact finite period controls](PERIOD_GRAPH_CHECK.json) · [Reproducer](check_period_graph.py) · [Calibration stress test and native short window](QUIET_PREFIX_AND_CALIBRATION.md)
