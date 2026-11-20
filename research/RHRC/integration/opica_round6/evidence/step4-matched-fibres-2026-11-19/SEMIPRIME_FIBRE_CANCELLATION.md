# Matching a sharp semiprime block to its actual positive divisor fibres

**DERIVED on paper.** The entire explicit positive semiprime block in the [joint product covariance](../step4-area-runs-2026-11-19/SHARED_PRODUCT_COVARIANCE.md) can be paid at the critical \(X^{3+o(1)}\) scale, including its part with both long separation and large least common multiple. The payment uses individual, genuine, positive divisor contributions from the same sharp cofactor interval. Each original prime cofactor remains in the sum. A separate calculation pays a fixed smooth interior window to arbitrary power accuracy. The final section sums the whole interior and identifies its exact endpoint corrections. The remaining signed covariance and Step 4 are open.

## The true arithmetic rows

Keep \(L_1=\lfloor X^{11/100}\rfloor,\ L_2=\lfloor X^{37/100}\rfloor,\ Y=X/L_1\). Write \(a=13/25,\ b=3/5,\ c=11/10,\ d=13/10\). In the known rectangle \(p\in[aY,bY]\) and \(q\in[cL_1,dL_1]\) are genuine primes; \(bd<1\). In the first observation a selected row \(n=pq\) contributes \(-(X-pq)\log p\). In the second it contributes \(-(X-pq)\log q\). Its outer label in that observation is \(q\). Let \(T_1<0\) be the sum of these first-observation rows, and \(T_2<0\) the corresponding second sum. Their product has a strictly positive main term of order \(X^4/\log^2 X\), with the constant computed in the linked note. In particular \(|T_1|\ll X^2\) from Chebyshev and the elementary interval counts.

In the [eta filter](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md), write
\[
 H(s)=\zeta(s)\eta(2s)\eta(3s),\quad H(s)^{-1}=\sum c_0(n)n^{-s},
 \quad A_L(s)=\sum_m a_m(1-m^{1-s}),\quad
 R_L(s)=1-H(s)A_L(s).
\]
The coefficients of \(R_L\) are \(r_2(j)\). Here and below \(L=L_2\). Matching, moment equations, the four exceptional positions \(4^iR,\ 0\le i\le3,\ R\asymp L\), and the bound \(\sum_m|a_m|m^v\ll_v L^v\log^2(2L)\) are as in the joint product note. At primes \(j\in[aY,bY]\) one has \(r_2(j)=-1\).

On a squarefree cofactor \(j>1\) coprime to \(R\) and odd, the coefficients of \(H\) equal 1 at every divisor, those of \(1/H\) equal \(\mu\), and none of the four exceptional positions divides \(j\). Therefore
\[
 r_2(j)=-\sum_{h\mid j,\ h\le L}\mu(h).
 \tag{1}
\]
This follows directly from the finite divisor convolution. If \(j=v_1v_2v_3\) for distinct primes, at least two of them are \(\le L\), and every pair product is \(>L\), (1) equals the number of its individual prime factors \(\le L\), minus 1. It is exactly 1 or 2.

## A reproducible surplus of these positive cofactors

Set \(\alpha=37/89\), the limit of \(\log L/\log Y\). Take \(N=140\). For each index pair satisfying
\[
 1\le i,\quad j\ge i+2,\quad 89(i+j)>37N,\quad
 89(j+1)<37N,\quad i+2j+3<N,
\]
use \(u=\log v_1/\log Y\in(i/N,(i+1)/N]\) and \(v=\log v_2/\log Y\in(j/N,(j+1)/N]\). Let \(v_3\) run over primes for which \(t=v_1v_2v_3/Y\in[a,b]\). Exclude primes dividing \(R\) from all three choices. These fixed strict margins imply \(v_1<v_2<v_3\), \(v_1,v_2\le L\) and \(v_1v_2>L\) for all large \(X\), including the floor in \(L\). All cofactors are odd. Unique ordered factorization keeps the cells disjoint.

At fixed \(q\) put \(\xi=q/L_1\in[c,d]\) and \(I(\xi)=\int_a^b(1-\xi t)dt\), bounded uniformly away from zero. The total negative mass of all original prime cofactors in this fibre, divided by \(\log q\), is asymptotic to \(XYI(\xi)/\log Y\) by ordinary PNT. The sum of \(X-qv_1v_2v_3\) over the triples in any one cell, again before the outer logarithm, divided by the same quantity, tends uniformly in \(\xi\) to
\[
 \iint_{\rm cell}\frac{du\,dv}{uv(1-u-v)}.
\]
Indeed, for fixed \(v_1,v_2\), the scale of \(v_3\) is \(Z=Y/(v_1v_2)\), with \(\log Z=(1-u-v)\log Y\) and \(Z\ge Y^{c_0}\) for a fixed \(c_0>0\). Partial summation of PNT on \([aZ,bZ]\) gives \(XZ[I(\xi)+o(1)]/\log Z\) uniformly. Only two fixed polynomial moments in \(t\) enter. A bounded number of primes \(v_3\asymp Z\) divide \(R\), costing \(O(X)\) per pair, negligible uniformly on that scale. The measures \(\sum_{v_1}1/v_1\), \(\sum_{v_2}1/v_2\) in their log coordinates converge on these fixed cells to \(du/u,dv/v\) by PNT and partial summation. Omitting prime factors of \(R\) removes \(o(1)\) reciprocal mass because all such primes exceed a fixed power of \(Y\) and their number in that range is bounded. This proves the asymptotic. [Ordinary prime number theorem](https://dlmf.nist.gov/25.16.E3)

Each cell integral exceeds \(N/[(i+1)(j+1)(N-i-j)]\). The following integer calculation verifies that the 558-cell total is at least \(1.101194\).

~~~python
N = 140
cells = [(i, j) for i in range(1, N) for j in range(i + 2, N)
         if 89 * (i + j) > 37 * N and 89 * (j + 1) < 37 * N
         and i + 2 * j + 3 < N]
lower = sum((1_000_000 * N) // ((i+1)*(j+1)*(N-i-j)) for i, j in cells)
assert (len(cells), lower) == (558, 1_101_194)
~~~

Thus the actual positive \(r_2\)-weighted triple pool, using \(r_2\ge1\), exceeds the prime deficit by more than 10% in **each** \(q\) fibre for all sufficiently large \(X\). The strict asymptotic surplus pays for all endpoints. The proof of this assertion uses ordinary PNT independently of a fixed zero ceiling.

## A sharp, two-sided payment at square scale

Form the following binary selection of genuine second-observation labels \((q,j)\) at each \(X\).

1. Keep all the original negative prime cofactors \(j\in[aY,bY]\).
2. For each \(q\) in ascending order, sort its triple pool by integer cofactor. In this fibre the negative mass is known exactly. The last positive prefix of mass at most that deficit and the first prefix of mass at least the deficit both exist, allowing the empty prefix. Include the real coefficients \((X-qj)r_2(j)\log q\). Each prefix therefore has signed error of the appropriate sign and magnitude at most \(2X\log q\).
3. If the accumulated signed error from earlier \(q\)'s is positive, use the lower prefix. Otherwise use the upper prefix. After each choice the absolute running error is at most \(2X\log X\), since the new increment has opposite sign and that same magnitude bound. Ties with exact equality need no correction.

Let \(T_2^*\) be this full signed selection. Then \(|T_2^*|\le2X\log X\), and \(|T_1T_2^*|\ll X^3\log X\). The product includes every pair from \(T_1T_2\). Only positive triple cofactors in their original sharp cofactor interval were added to the second factor. The selector depends on the actual finite arithmetic data at \(X\). Its rule and all cells are fixed before \(X\) or any hypothetical zero is chosen.

Even if the second row \(qj\) has several eligible prime labels, only the indicated labeled summand is being selected. Repeated labels are distinct entries of the actual expansion \(b_2(n)=\sum_{q\mid n}(\log q)r_2(n/q)\). The other labels and all unselected triples belong to the complementary signed sum. This prevents any substitution of a partially selected coefficient for a complete integer-row coefficient. On the already paid families \(|n-m|\le e^{\sqrt{\log X}}\) or \({\rm lcm}(n,m)\le Xe^{\sqrt{\log X}}\), the previous absolute bounds also hold for the selector: their majorants sum absolute divisor and label contributions before estimating multiplicities. Subtracting that intersection shows that the selected sector among the genuinely long-shift, large-lcm pairs is \(O_\epsilon(X^{3+\epsilon})\) in signed absolute value for each \(\epsilon>0\). The all-remaining covariance is unresolved.

## A fixed smooth cofactor window

A different, deterministic payment sums **every** cofactor in a smooth window. Take \(\phi_\Delta\) equal to 1 on \([a,b]\), zero outside \([a-\Delta,b+\Delta]\), with smooth transitions scaled from one fixed smooth cutoff, \(0\le\phi_\Delta\le1\). For \(q\in[cL_1,dL_1]\), this lies strictly below \(X/q\) for every sufficiently small \(\Delta\). The entire second fibre is
\[
 X\sum_j r_2(j)(1-\xi j/Y)\phi_\Delta(j/Y).
\]
\(R_L(s)\) is entire: the pole of \(\zeta(s)\) at 1 is canceled by each \(1-m^{1-s}\), and both eta factors are entire. On any fixed line \(\Re s=-M,\ M\) an integer at least 2, the functional equation and Stirling give
\[
 |R_L(-M+it)|\ll_M L^{1+M}\log^2(2L)(1+|t|)^{3/2+6M}.
\]
For \(\Phi=(1-\xi u)\phi_\Delta(u)\), integration by parts in \(\log u\) gives
\[
 |\widehat\Phi(-M+it)|\ll_{M,k}(1+|t|)^{-1}
                            (1+\Delta|t|)^{-k}
\]
for every integer \(k\ge1\). Its total variation is bounded and its derivative of order \(k+1\) has \(L^1\) norm \(O_{M,k}(\Delta^{-k})\), uniformly in \(\xi\). Mellin inversion from \(\Re s>1\) and shifting to \(-M\) are justified by rapid vertical decay at fixed \(X\). Choosing \(k>3/2+6M\) bounds the result by
\[
 O_M\!\left(X L\log^2(2L)(L/Y)^M\Delta^{-3/2-6M}\right).
\]
For \(\Delta=X^{-\delta}\) with \(0<\delta<13/150=(0.89-0.37)/6\), choose the fixed \(M\) arbitrarily large. This gives \(O_{A,\delta}(X^{-A})\) for each \(A>0\), uniformly in the genuine outer \(q\). It pays the factor with all these \(q\)'s and any polynomial-size first selection to the same arbitrary-power accuracy upon increasing \(A\). This smooth payment requires no choice of positive triples. Its full composite contribution cancels the full negative prime contribution in the smooth fibre, and its transition-prime contribution is \(O(X(Y\Delta+1))\) before the outer log by elementary counting.

## Complete interior and the true terminal boundary

Put \(Y_q=X/q\), fix \(\beta>0\), and consider every eligible \(q\) satisfying \(Y_q/L\ge X^\beta\). Fix \(0<\delta<\beta/6\), \(\Delta=X^{-\delta}\). Let \(\chi_\Delta(u)=1\) on \(0\le u\le1-2\Delta\), zero for \(u\ge1-\Delta\), with one fixed smooth rescaled transition in between. This retains **all** low cofactors. Let \(g_\Delta(u)=(1-u)\chi_\Delta(u)\). Its Mellin transform continues meromorphically with only poles at \(s=0,-1\) and respective residues \(1,-1\), since it is exactly \(1-u\) at the origin. More explicitly, integrating by parts twice gives
\[
 \widehat g_\Delta(s)
  ={1\over s(s+1)}\int_0^\infty g_\Delta''(u)u^{s+1}\,du .
\]
The second derivative is supported in the transition interval and has bounded \(L^1\) norm, since \(1-u=O(\Delta)\) there. Repeated integration by parts gives the same large-\(t\) estimate as for \(\widehat\Phi\), with power \(-2\) in place of \(-1\). The residues crossed on shifting are therefore the only non-negligible terms:
\[
 X\sum_{j\ge1} r_2(j)g_\Delta(j/Y_q)
   =X R_L(0)-qR_L(-1)+O_{A,\beta,\delta}(X^{-A}).
 \tag{2}
\]
Indeed the contour remainder is \(O_M(X L\log^2(2L)(L/Y_q)^M\Delta^{-1/2-6M})\), uniformly in \(q\); choose \(M\) after \(A,\beta,\delta\) are fixed. Any polynomial number of fibres, including their log weights, can be summed by increasing \(A\).

For the existing filter \(H(0)=-1/8\) and \(H(-1)=0\) (the trivial zero of \(\zeta(-2)\) in \(\eta(-2)\)). Thus (2) equals \(X[1+(1-\sum_m a_m m)/8]-q\), up to the stated error. The existing four constraints do not set this first scalar to zero.

One may separately define a **five-node variant** by adjoining \(256R\) to the exceptional indices and imposing \(\sum a_m m=9\). The earlier equations for matching, continuum, square and cube stay in place. The five rows after the same rescaling are \(1,i,2^i,(4^{2/3})^i,4^i\), \(0\le i\le4\), a nonsingular confluent Vandermonde system. The last residual, divided by \(R\), is bounded using \(\sum_{m\le L}|c_0(m)|\ll L\); all new exceptional coefficients are still \(O(\log^2(2L))\). Thus the [eta localization proof](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md) applies to this variant with the same exponents. Even the exceptional-node size and gcd costs in the matched row majorants change only by constants.

For that variant (2) becomes \(-q+O_A(X^{-A})\) per fibre. The total signed smooth interior for \(Y_q/L\ge X^\beta\) costs at most \(O((X/L)^2)=O(X^{1.26})\) by Chebyshev, below the \(X^{3/2}\) single-source threshold. The five-node observation can consequently be restricted, up to \(o(X^{3/2})\), to the original source's near-terminal cofactors \(j>(1-2\Delta)X/q\) with weight \(1-\chi_\Delta(j/Y_q)\), together with all eligible outer primes \(q>X/(L X^\beta)\). The original lower prime cutoff still applies. The outer range adjacent to \(X/L\) includes the [oscillating first band](../step4-area-runs-2026-11-19/FIRST_BAND_OSCILLATION.md). These last regions still require a signed estimate at the common horizon.

These are finite and analytic paper deductions. No new formal statement or CI qualification is claimed.
