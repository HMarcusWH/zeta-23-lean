# A divisor gap on the genuine signed survivor graph

**DERIVED on paper, conditional only on the cited earlier paper transfer and classical proven estimates.** For every fixed \(0<\gamma<\beta<1-\log 2\), the native matching can be chosen so that **no survivor has any divisor** \(d\) with
\[
             |\log d-\tfrac12\log n|\le (\log U)^\beta .
\]
Here \(U\) is its whole terminal shell. The surviving vertices still give the two original one-sided energies up to bounded absolute error per shell. On these vertices, the signed sum over divisors below the square root annihilates every polynomial in \(\log d\) of degree less than \((\gamma-o(1))\log\log U\). The upper half has the same property. Removing the top endpoint from the upper half restores the original Möbius sign with a minus sign. This is an exact obstruction to recovering the missing bound from those vanishing moments.

## Local count at the true roughness

Use the notation and actual matching of [PR303, Prime-factor histories](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md). Set \(y=\lceil\log_2X\rceil^2,\ L=\log\log U,\ z=\exp(\log U/L^2),\ V=\prod_{p\le y}(1-1/p)\). The old running-count constraint implies \(\omega(n)\le L+O(\sqrt L)\). Apply the following count only to native squarefree \(y\)-rough labels satisfying that bound. The previously marked atypical labels already have matching costs.

On every interval \(J=(x,x+H]\) in the shell with \(H\ge U^{0.48}\), a specified band \(D<d\le2D\), \(D=U^{1/2+o(1)}\), contains a divisor of at most
\[
                  HV\,(\log U)^{-(1-\log2)+o(1)}
                  \tag{1}
\]
such labels. Uniformity here includes all bands within \(O((\log U)^\beta+1)\) of the midpoint in log coordinates. Changing between the two integer endpoint conventions shifts \(x\) by at most one. The estimates are uniform for that shift.

For the two true factors \(de=n\), write
\[
 w(d)=\mathbf1_{P^-(d)>y}\,2^{-\omega_{(y,z]}(d)},\qquad w(1)=1 .
\]
Their sets of primes are disjoint. Thus \(1\le 2^{L+O(\sqrt L)}w(d)w(e)\) for these factorizations. After this inequality the upper sum can include all ordered positive integer factor pairs in the band. The dependence of \(e\) on \(d\) and the cell is retained by counting \(de\in J\).

Take \(\alpha_p=1\) through \(y\), \(1/2\) between \(y\) and \(z\), and zero beyond. For each variable separately, majorize \(\prod_{p\mid d}(1-\alpha_p)\) by the inclusion–exclusion polynomial of even degree \(k=2\lceil20 L\rceil\). Bonferroni for factors in \([0,1]\) follows by applying it to independent events of those probabilities for a **fixed** \(d\). The upper polynomial is nonnegative pointwise, so the two majorants can be multiplied. The expansion uses divisibility conditions \(r\mid d,\ s\mid e\), with absolute coefficients at most one, \(r,s\le z^k=U^{o(1)}\), and \(U^{o(1)}\) terms in total.

For such \(r,s\), let \(B=x/(rs)\) or \((x+H)/(rs)\), and \(K=D/r\). The number of pairs with \(r\mid d,\ s\mid e,\ de\in J\) equals
\[
           {H\log 2\over rs}
              +O\big(H/(sD)+U^{1/3+o(1)}\big).                 \tag{2}
\]
Indeed, sum the difference of the two exact floors over \(K<j\le2K\). The harmonic sum is \(\log2+O(1/K)\). For each endpoint the discrepancy in \(\sum_{K<j\le2K}(\{B/j\}-1/2)\) is \(O(U^{1/3+o(1)})\). To verify this, truncate the sawtooth estimate at \(M=\lfloor K B^{-1/3}\rfloor\) (eventually positive). For frequency \(m\), curvature on the interval is comparable with \(mB/K^3\). The second derivative bound for its exponential sum gives \(O(\sqrt{mB/K}+K^{3/2}/\sqrt{mB})\). The sawtooth bound then gives \(O(K/M+\sqrt{MB/K}+K^{3/2}/\sqrt B)\), of the required order since \(B=U^{1+o(1)},K=U^{1/2+o(1)}\). This includes integer endpoint coincidences. [Stephan Baier, lectures on exponential sums, Lemma 6 and Theorem 7](https://www.atmschools.org/sites/default/files/Baier-Lectures_on_expo_sums.pdf)

The truncated Euler sum in either variable differs from \(W=\prod_{p\le z}(1-\alpha_p/p)\) by at most \((\sum_{p\le z}\alpha_p/p)^{k+1}/(k+1)!\). This uses adjacent Bonferroni truncations, including the lower one. Since the harmonic mass is at most \(L+O(1)\), the error is \(O((\log U)^{-20})\). The prime harmonic estimate gives \(W=V\exp[-L/2+O(\log L)]\). The expanded main term is consequently \(H\log2\,(W+O((\log U)^{-20}))^2\). The total remainder in (2) is \(H U^{-1/2+o(1)}+U^{1/3+o(1)}\), smaller than \(H(\log U)^{-A}\) for every fixed \(A\) in the stated range. Multiplying by \(2^{L+O(\sqrt L)}\) and dividing by \(HV\) proves (1). No cancellation in the unknown signed vertex count was used.

## Put the counted labels into the existing matching

For every \(n\in[U,2U)\), the forbidden divisor interval fits inside the fixed shell band from \(U^{1/2}\exp[-(\log U)^\beta]\) through \((2U)^{1/2}\exp[(\log U)^\beta]\). Cover by \(O(1+(\log U)^\beta)\) factor-two bands. By (1), the extra marked population is \(o(HV)\) in **every** first-, second- and third-stage cell. That is below any fixed positive fraction of the old donor margin \( \asymp \kappa HV\) for sufficiently large \(U\). Increase the original typicality constant at the outset if necessary to leave slack. Add the extra vertices to the previous target list and exclude those vertices from the old partner lists before matching. Exhaustion in each good parent and the unchanged exceptional-cell estimates in the original proof now apply. Thus for each sign the sum over nodes of \(w_J |[s f_J]_+^2-[s r_J]_+^2|\) is \(O(1)\) per whole shell. This is a new selection on the true labels. It does not assert negligible energy upon merely deleting the divisor-bearing rows. No estimate on the masked primitive graph after deletion is implicit. The full primitive-to-node comparison precedes this operation.

## Exact signed responses below and above the square root

Let \(a\) be the product of primes dividing a surviving \(n\) below \(\exp((\log U)^\gamma)\), with the upper endpoint included. Write \(h=\omega(a)\). The running constraint and the prime harmonic estimate imply \(h=\gamma L+O(\sqrt L+\log L)\), uniformly at sufficiently large cutoffs. Moreover \(\log a\le O(L)(\log U)^\gamma<(\log U)^\beta\). For each divisor \(b\mid n/a\), the entire set \(\{bc:c\mid a\}\) lies on one side of \(\sqrt n\). Otherwise its smallest member would lie in the forbidden band. Squarefreeness gives one such representation for each divisor and \(\mu(bc)=\mu(b)\mu(c)\).

In particular the actual finite transform on the lower half is
\[
 F_n(s)=\sum_{d\mid n,\ d<\sqrt n}\mu(d)d^{-s}
       =\prod_{p\mid a}(1-p^{-s})
             \sum_{b\mid n/a,\ b<\sqrt n}\mu(b)b^{-s}.
\]
It vanishes to order at least \(h\) at zero. The complete upper half obeys the same factorization with the opposite inequality. For every polynomial of degree \(j<h\), each half therefore has \(\sum\mu(d)P(\log d)=0\). These identities hold separately on actual vertices of either parity. On the upper half punctured at \(d=n\), the sum instead equals \(-\mu(n)P(\log n)\). At \(P=1\) the remaining charge is the entire original endpoint, however many moment equations the complete halves satisfy.

There is quantitative signed suppression too. Uniformly for \(|s|\le C/\log U\) with fixed \(C\), the finite sum over \(b\) has modulus \(O_C(2^{\omega(n)})\), and each small-prime factor has modulus \(O_C(\log p/\log U)\). Even the largest permitted small prime gives
\[
 |F_n(s)|\le \exp[-(\gamma(1-\gamma)-o(1))L^2].
\]
The same uniform bound holds for the complete upper half. It is a per-vertex analytic response bound on a **divisor** transform. The punctured endpoint explains exactly why treating that response as an upper on the complete signed **vertex** charge fails.

The previous graph implication still requires a cofinal \(X^\epsilon\) upper for one polarity of the full weighted survivor charges. The divisor gap narrows the allowed surrogate proof inputs and permits a rigorous exclusion of balanced factorizations from the target. The unbalanced labels, signed partners already spent, and endpoint signs still enter the shared source. No such closing upper follows here. Step 4 and RH remain **OPEN**.

## The size of the response on a wider frequency range

Fix \(0<\beta<1-\log 2\), \(\eta>0\), \(C>0\). Set \(\tau=\min(\beta,\eta)\). For this same divisor-gap selector consider the product \(a_\tau\) of the primes dividing \(n\) with \(\log p\le(\log U)^\tau/L^2\). Eventually \(\log a_\tau=O((\log U)^\tau/L)<(\log U)^\beta\), so the lower and upper halves still each contain only complete cubes. The same selector works for these estimates at each fixed \(\eta\).

Write \(t_0=\log\log y\), \(t_1=\tau L-2\log L\), and \(A(t)=\#\{p\mid n:y<p,\ \log\log p\le t\}\). The running prime-divisor bound on each survivor and the prime harmonic estimate give
\[
 A(t)=t-t_0+O(\sqrt L+1)\qquad(t_0\le t\le t_1).
\]
In particular \(h_\tau=A(t_1)=\tau L+O(\sqrt L+\log L)\). Partial summation on this *same* integer gives
\[
 \sum_{p\mid a_\tau}\log\log p
 =t_1 A(t_1)-\int_{t_0}^{t_1}A(t)\,dt
 =\tfrac12\tau^2 L^2+O(L^{3/2}+L\log L).
\]
For \(|s|\le C(\log U)^{-\eta}\) and \(\Re s\ge-C/\log U\), integrate the exponential along the straight segment from \(0\) to \(s\log p\). It gives \(|1-p^{-s}|\le |s|\log p\,\exp(C\log p/\log U)\). The remaining \(b^{-s}\) are bounded, and there are at most \(2^{\omega(n)}=\exp(O(L))\) terms. Multiplying all factors yields, on either complete half,
\[
 \left|\sum_{d\mid n,\ d\ {\rm in\ the\ half}}\mu(d)d^{-s}\right|
 \le \exp\!\left[-(\eta\tau-\tfrac12\tau^2)L^2+
                   O_{\eta,\beta,C}(L^{3/2}+L\log L)\right].
\]
For \(0<\eta\le\beta\) the coefficient is \(\eta^2/2\); for \(\eta=1\) it is \(\beta-\beta^2/2\). The bound includes imaginary frequencies and an explicit range of negative real parts. Larger negative real parts can amplify the unselected cofactor transforms. On the upper half punctured at \(d=n\), the exact additional term is \(-\mu(n)n^{-s}\); at \(s=0\) this has absolute value one.

## Finite checks and the existing Lean result

The [exact checker](check_divisor_halves.py) and [finite results](DIVISOR_HALVES_EXACT.json) use three actual rough squarefree labels in whole terminal shells, including both signs. Both unclipped examples have zero lower signed count and punctured upper count \(-\mu(n)\). In the third example the cut splits a divisor cube, the lower count is \(-2\), and the factored reciprocal sum fails. Divisor counts and reciprocal sums use exact arithmetic. The checker verifies the finite polynomial moment identities by integer exponent coordinates. It does not run the asymptotic matching algorithm.

The repository already proves the equality of the two Möbius-sign counts on the *complete* divisor set of every \(n\ne1\). The arithmetic input added above is the paid gap on actual survivors, which gives separate cancellation on both halves up to growing moment order. The full vertex sign survives puncturing regardless of that order. [Original Lean declaration](../../../../../../Zeta23/OPICAFollowup/WeightedMixing.lean#L886)
