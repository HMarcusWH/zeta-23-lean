# Simultaneous spacing of every divisor on the signed survivor source

**DERIVED on paper.** Fix a large native cutoff \(X\), a complete terminal shell \([U,2U)\), \(y=\lceil\log_2 X\rceil^2\), \(V=\prod_{p\le y}(1-1/p)\), and the original signed coefficient \(\mu(n){\bf1}_{P^-(n)>y}\). Here the native grid index is exactly $s_X=\lceil\sqrt{\lfloor\log_2 X\rfloor}\rceil$. The published signed matching can impose a new condition on every surviving integer in addition to the earlier running-factor counts and the gap about \(\sqrt n\). For any two distinct divisors \(d<e\) of that same integer,
\[
 e-d>d^{\lambda_U},\qquad
 \lambda_U=\frac45-\frac{10}{\sqrt{\log U}}.                    \tag{1}
\]
The conclusion holds for all sufficiently large cutoffs. Each of the two native one-sided energies changes by \(O(1)\) per whole shell, with absolute node errors summed. This is a statement about genuine removed labels paired with genuine opposite signs. The quantitative local count below is independent of any zeta-zero location. [Original full-source matching](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md) · [Earlier central divisor gap and its combination with the donor pool](../step4-parity-deficit-2026-11-20/DIVISOR_GAPS_AND_SIGNED_HALVES.md)

## The number of new targets on a genuine matching interval

If \(g=(d,e)\), set \(k=d/g,\ l=e/g\). For a squarefree label the product of the two coprime divisors \(kl\) divides \(n\) (in fact their least common multiple already suffices). A violation gives
\[
  1\le l-k\le g^{\lambda_U-1} k^{\lambda_U}\le k^{\lambda_U}.
\]
If \(k=1\), \(l\le2\) is impossible on a large rough label. Otherwise \(k>y\). It suffices to count all positive integer triples \(n=m k(k+h)\) with \(k>y,\ 1\le h\le k^{\lambda_U}\), including multiplicities and unrestricted \(m\). This positive upper includes all primality and squarefreeness patterns that the coupled source could present.

Let \(J=(x,x+H]\) be an integer interval in the shell, with \(H\) any of the three native walking lengths \(H_1,H_2,H_3\) in the published matching. A half-open integer cell is exactly of this form after shifting its left coordinate by one. For dyadic \(P<k\le2P\), \(y/2\le P\ll\sqrt U\), put \(M=U/P^2\). For each of the at most \((2P)^{\lambda_U}\) integer shifts use the following bounds. Constants are uniform for all these \(h\), \(H\), and large \(U\).

* With \(k\) fixed, count \(m\) by the difference of the two floors at \(F_z(k)=z/[k(k+h)]\), \(z=x,x+H\). The sum over \(k\) of the continuous differences is \(O(H/P)\). The trivial floor cost is \(O(P)\).
* Every admissible \(m\) lies between \(c M\) and \(C M\), for absolute positive \(c,C\). On this common interval enlarge the count by dropping \(P<k\le2P\). The two exact endpoints for positive \(k\) are \(G_z(m)=\sqrt{z/m+h^2/4}-h/2\). Each derivative in \(z\) is \(O(1/(MP))\). Thus the enlarged continuous main term is again \(O(H/P)\), and its trivial floor cost is \(O(M)\). Here \(M\gg1\). This enlargement avoids truncating either inverse at a dyadic boundary.
* With \(\psi(t)=\{t\}-1/2\) and \(\psi\) equal to \(-1/2\) at integers, the error in either pair of floors is exactly a difference of sawtooth sums. On the dyadic range of the relevant variable denote its scale by \(N\) and the amplitude of the phase by \(Y\). They are \((N,Y)=(P,M)\) for \(F\), or \((M,P)\) for \(G\). Rescaling the variable by its dyadic scale shows \(|F^{(j)}|\asymp Y/N^j\), respectively \(|G^{(j)}|\asymp Y/N^j\), for \(j=2,3\) in the estimates where each is used. Indeed \(h/P\to0\) uniformly, \(z/U\asymp1\), and the normalized profiles converge in \(C^3\) on compact positive intervals to a positive multiple of \(v^{-2}\) or \(v^{-1/2}\). Their relevant derivatives are bounded away from zero. The additive constant in \(G\) has no effect.

The truncated sawtooth inequality bounds one endpoint by \(O(N/K+\sum_{j\le K}|S_j|/j)\), \(S_j=\sum e(jf(v))\), with the usual majorant including integer coincidences. The second derivative test gives \(|S_j|\ll\sqrt{jY}+N/\sqrt{jY}\). For \(1\le Y\le N^2\), take \(K\asymp(N^2/Y)^{1/3}\), rounding to a positive integer. The resulting error is
\[
 O\big((NY)^{1/3}+N/\sqrt Y\big).                               \tag{2}
\]
We give the cubic-frequency cutoff explicitly since a crude sum of the cubic bound down through frequency one loses the claimed exponent. [Sawtooth majorization and second derivative estimate, Lemma 6 and Theorem 7](https://www.atmschools.org/sites/default/files/Baier-Lectures_on_expo_sums.pdf) · [Third derivative estimate and proof](https://people.math.harvard.edu/~elkies/M259.02/vdc.pdf)

For the dual phase let \(N=M,Y=P\), with \(M^{5/4}\le P\le M^3\). The third derivative test gives
\[
 |S_j|\ll M^{1/2}(jP)^{1/6}+M(jP)^{-1/6}.
\]
Take \(K\asymp(M^3/P)^{1/7}\ge1\), and use the **second** derivative test through \(K_0=M^{3/2}/P\) if \(K_0\ge1\). The relation \(P\ge M^{5/4}\) gives \(K_0\le K\), up to harmless integer rounding. When \(K_0\ge1\) the low part costs \(O(M^{3/4}+M/\sqrt P)\); the decreasing term in the high part costs \(O(M(K_0P)^{-1/6})=O(M^{3/4})\). When \(K_0<1\), the latter costs \(O(MP^{-1/6})\ll M^{3/4}\) on the entire range. All are \(O(M^{4/7}P^{1/7})\). The increasing cubic term through \(K\), and \(M/K\), have this same bound. This proves the dual endpoint error
\[
 O(M^{4/7}P^{1/7}).                                               \tag{3}
\]

Write \(u=\log P/\log U\). The table gives one valid endpoint bound \(E(P)\) per integer \(h\). The two trivial ranges cover the dyadic endpoints, including \(P\) within a fixed factor of \(\sqrt U\).

| Range of \(u\) | Choice | \(E(P)\) |
|---|---|---|
| \(u\le1/4\) | Sum over \(k\), trivial | \(P\) |
| \(1/4\le u\le1/3\) | (2) with \(N=P,Y=M\) | \((U/P)^{1/3}\) |
| \(1/3\le u\le5/14\) | (2) with \(N=M,Y=P\) | \((U/P)^{1/3}\) |
| \(5/14\le u\le3/7\) | (3) with \(N=M,Y=P\) | \(U^{4/7}/P\) |
| \(3/7\le u\) | Sum over \(m\), trivial | \(U/P^2\) |

For the forward quadratic range \(P/\sqrt M=P^2/\sqrt U\le(U/P)^{1/3}\). For the dual quadratic range \(M/\sqrt P=U/P^{5/2}\le(U/P)^{1/3}\). The cubic endpoints are precisely \(P=M^{5/4},M^3\). The number in the dyad is consequently
\[
 \ll H P^{\lambda_U-1}+P^{\lambda_U}E(P).                         \tag{4}
\]
For every \(\lambda\) in a fixed neighborhood of \(4/5\) the second term's largest exponent occurs at \(u=5/14\), with value \(3/14+5\lambda/14\). Indeed its slopes in successive ranges are \(1+\lambda,\ \lambda-1/3,\ \lambda-1,\ \lambda-2\), with the same quadratic expression on both quadratic ranges. Summing dyads for \(\lambda=\lambda_U\) gives
\[
 \ll H y^{-1/5}+\sqrt U\,(\log U)\exp[-(25/7)\sqrt{\log U}].
                                                                    \tag{5}
\]
The harmonic factor in the first term is a geometric sum beginning at \(y/2\). An integer at the shell edge changes no exponent or interval convention.

The smallest donor interval has \(H_1=2^{\lfloor(\log_2 H_0)/2\rfloor}\), \(H_0=U2^{-s_X}\), \(s_X=\lceil\sqrt{\lfloor\log_2 X\rfloor}\rceil\), and \(U\gg X^{.99}\) in a complete terminal shell. Hence \(H_1\gg\sqrt U\exp(-\sqrt{\log U})\) eventually. Since \(V\asymp1/\log y\), (5) is \(o(HV)\), uniformly on **every** first, middle and final donor interval. The strict margin \(\asymp\kappa HV\) in each good sign pool of the original proof absorbs both the new targets and the same number potentially lost from the pool. Add them before selecting actual partners, retaining the original choices of large fixed typicality constants with slack. The same three-level matching pairs every target. On \(H\ge H_3\) its signed net charge is exactly zero; on the intervening lengths its existing exceptional-cell bounds apply; on \(H\le H_1\) the absolute tree cost is bounded. This proves the stated \(O(1)\) comparison on every subset of a complete shell's nodes, with all spent partners debited. Other previously imposed target populations with the same slack can be combined. The initial source-to-node comparison uses the original primitive GCD mask before any removal.

## What the time response can resolve

For \(d<e\mid n\), either \(d\le\sqrt n\) or \(n/e\le\sqrt n\). Applying (1) on that side and using \(\log(1+x)\ge x/2\) on \(0\le x\le1\) gives
\[
 \log(e/d)\ge \tfrac12 n^{-(1-\lambda_U)/2}
     \gg n^{-1/10}\exp[-6\sqrt{\log n}].                          \tag{6}
\]
The reciprocal divisor pair has exactly the same frequency gap. Thus every survivor's *entire* divisor spectrum is separated at this scale; earlier central gap statements concern just the cut through \(\sqrt n\).

For any complex weights \(c_d\) on this one integer's divisors, set \(D_n(t)=\sum_{d\mid n}c_d e^{it\log d}\), with \(v=\tau(n)\) and \(\Delta\) the right side of (6). On every real interval of length \(2T\),
\[
 \left|\frac1{2T}\int |D_n(t)|^2\,dt-\sum_{d\mid n}|c_d|^2\right|
       \le \frac{2(1+\log v)}{T\Delta}\sum_{d\mid n}|c_d|^2.     \tag{7}
\]
After ordering the frequencies the \(j\)-th neighbor on either side is at distance at least \(j\Delta\). The sinc off-diagonal matrix therefore has the displayed absolute row-sum bound, which bounds its quadratic form by \(2|ab|\le|a|^2+|b|^2\). At \(T=n^{1/10}\exp(8\sqrt{\log n})\) the relative error tends uniformly to zero; \(\log v\le\log n\) suffices. The signed actual coefficients \(c_d=\mu(d)\), either complete divisor half, and all their coherent combinations are allowed. This controls the normalized observation of any **one** allocation, even under the existing moment zeros. Different integers share divisor frequencies, in particular \(d=1\). Formula (7) supplies no orthogonality across their labels. A square-integrated estimate on this growing frequency span also gives no bound of the required scale on one fixed low-frequency band: even the perfectly orthogonal harmonics \(e^{ijt}\) on \([-\pi,\pi]\) can add to \(v\) at \(t=0\). The project still needs signed cancellation between the distinct genuine survivors, with their original net charges on the same horizon. Step 4 and RH remain **OPEN**.

There is also a falsification on the **actual arithmetic coefficients**. For any finite set of surviving labels at a fixed horizon, collect the finite set of primes occurring in them. The vector \((e^{it\log p})_p\) is dense in its torus, even with any prescribed lower bound on \(t\). Indeed every nonconstant torus character has continuous time average zero by unique prime factorization and integration of its nonzero exponential frequency. Approximation of a continuous bump inside any chosen open box by trigonometric polynomials then puts the orbit inside that box at arbitrarily late times. Choosing every prime phase near \(-1\) makes \(\mu(d)e^{it\log d}\) simultaneously close to \(+1\) for every divisor of every chosen label. Consequently each complete signed divisor transform can approach \(\tau(n)\), and all the signed full labels can align at once. This uses their true shared primes. The exceptional time depends on the complete finite set and says nothing about alignment in a prescribed fixed zero-frequency band. It directly rules out replacing the final signed estimate by a supremum over unrestricted observation times.

**Scope.** This is a new relative-to-project paper deduction, based on the stated classical estimates and the linked published matching. No new native run, Lean theorem, or independent proof of the closing energy bound is claimed.
