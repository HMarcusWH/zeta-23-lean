# Cancellation on complete product rows sharing a large ordinary prime

**DERIVED on paper.** The signed sum on all pairs whose greatest common divisor exceeds the largest possible old cofactor can be bounded by \(x^{3+o(1)}\) using the existing unconditional subpower factorial cutoff. This covers an explicit all-positive family of size \(\gg x^{16/5}/\log x\) contained among the previously unresolved long shifts and large least common multiples. A second construction pays the same entire sector throughout the original admissible power range above \(0.025\), including \(L=\lfloor x^{0.11}\rfloor\). It uses the project's external zero ceiling, one additional linear calibration against the complete lower-prime source, and a mean-square estimate for the true periodic weights. The remaining small-gcd signed sum and Step 4 are open.

## The exact arithmetic in a large-prime fibre

Use the distributed factorial filter with cutoff \(L\), lower prime endpoint \(u_0=x^{3/4}/[L\log^2(2L)]\), upper endpoint \(x/(L+1)\), and residual shape \(E(y)=(y-1)-\sum_m a_m J_m(y)\) for \(y\ge1\). Let \(\mathcal H\) be its open outer-prime interval. Keep unchanged the distributed eta filter at \(L_2=\lfloor x^{0.37}\rfloor\), with outer-prime set \(\mathcal L\) in \((x^{0.025},x/(L_2+1))\). For each of the choices of \(L\) below, every \(p\in\mathcal H\) eventually exceeds both \(64(3L_2)\) and \(x/(L_2+1)\), satisfies \(p^2>x\), and obeys \(x/p<L_2\). In particular the two outer sets are disjoint. The original normalization, bounds on the coefficients, error estimates, product-row definitions and disjoint-band comparisons are in the [factorial](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md), [eta](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md), [covariance](../step4-area-runs-2026-11-19/SHARED_PRODUCT_COVARIANCE.md) and [distributed-row](../step4-area-runs-2026-11-19/BOTH_ROW_ENERGIES.md) notes.

For \(1\le j\le x/p\), let \(h(j)\) be the eta base coefficient from \(\zeta(s)\eta(2s)\eta(3s)\), and \(w_2(j)\) its coefficient after the distributed calibration. In any \(a b^2 c^3=pj\), the prime \(p\) must lie in \(a\), since \(p^2>x\). Thus \(h(pj)=h(j)\). No active eta dilation index contains \(p\), so \(m\mid pj\) if and only if \(m\mid j\) for every such index. The entire filtered coefficient consequently satisfies
\[
 w_2(pj)=w_2(j)=\mathbf 1_{j=1}.
\]
The second equality uses exact prefix inversion up to \(L_2\), at the actual horizon. Therefore, for the complete second row at \(pk\le x\),
\[
 b_2(pk)=
 \begin{cases}
 -\log k & k\text{ is an outer prime in }\mathcal L,\\
 0 & \text{otherwise}.
 \end{cases}
\]
Indeed all permitted prime labels divide \(k\), and an individual label \(q\mid k\) has residual \(r_2(pk/q)=-\mathbf 1_{k/q=1}\). This accounts for *every* possible divisor, including repeated prime factors of \(k\).

A nonzero first row \(n\) has a unique \(p\in\mathcal H\) dividing it since \(u_0>\sqrt x\). Put \(D=x/u_0\). Writing \(n=pj\) gives \(j<D<p\). Hence for every such row
\[
 \gcd(n,m)>D\quad\Longleftrightarrow\quad p\mid m.
\]
For the reverse contrapositive, \(p\nmid m\) forces \(\gcd(n,m)\mid j\). There is no overcount between fibres. Write \(R_{\mathcal L}(y)=\sum_{q\in\mathcal L}(y-q)_+\log q\). Summing each complete factorial fibre before taking absolute values yields the exact identity
\[
 T=\sum_{\gcd(n,m)>D} f_1(n) f_2(m)
   =-\sum_{p\in\mathcal H}p^2\log p\,E(x/p) R_{\mathcal L}(x/p). \tag{1}
\]

## Unconditional critical-scale bound and a positive stress test

The original fourth factorial moment gives \(|E(y)|\ll L^2\log^2(2L)\) uniformly. Chebyshev gives \(0\le R_{\mathcal L}(y)\ll y^2\). Therefore (1) gives
\[
 |T|\ll x^2 L^2\log^2(2L)\,\vartheta(x/(L+1))
       \ll x^3 L\log^2(2L).
\]
With \(L=\lfloor\exp(\kappa\sqrt{\log x})\rfloor\), for the sufficiently small positive constant of the original unconditional localization, this is \(x^{3+o(1)}\). Both outer observations still recover the same centered area at \(o(x^{3/2})\). The relevant gcd threshold is \(D=x^{1/4+o(1)}\), and the two outer-prime ranges remain disjoint at large \(x\). With the *original* \(L=\lfloor x^{0.11}\rfloor\), restricting (1) to \(p\le x/L^2\) already gives \(O(x^3\log^2(2L))\) for that portion, without changing any coefficients.

For a stress test choose \(P=x^{4/5}\) and \(Y=x/P\). Take ordinary primes \(P<p<2P\) and \(Y/5<j,q<Y/4\) with \(j\ne q\). At sufficiently large \(x\), \(p\in\mathcal H\), both \(j,q\in\mathcal L\), and the factorial cofactor \(j\) exceeds the largest factorial dilation index for all cutoffs treated here. Since \(j\) is prime, \(w_1(j)=1\). On \(n=pj,m=pq\) the complete first row is \(-(x-pj)\log p\) and the complete second row is \(-(x-pq)\log q\). Each product is positive, \(p^2>x\) gives uniqueness of the labels, \(|n-m|\ge p\), and \(\operatorname{lcm}(n,m)=pjq\asymp x^{6/5}\). Ordinary PNT gives a subtotal
\[
 \gg x^2\frac{P}{\log P}\left(\frac{Y}{\log Y}\right)^2\log P\log Y
 \gg x^{16/5}/\log x.
\]
To test the paid portion of the original \(0.11\)-power choice, take \(P=x^{3/4}\) and \(Y=x^{1/4}\), giving instead \(\gg x^{13/4}/\log x\), now with \(2P<x/L^2\). In each critical-scale version, deleting near shifts or small-lcm pairs costs at most \(x^{3+o(1)}\) by the previous distributed row-energy and lcm estimates. The rest of the *same large-gcd sector* therefore compensates the positive test family at the critical scale.

## A fifth calibration for fixed-power whole-fibre cancellation

Choose \(L=\lfloor x^\lambda\rfloor\), with \(0.025<\lambda<(1-r)/(2-r)\) and \(r=0.873346\) the project's externally supplied upper ceiling. This includes \(\lambda=0.10\) and \(\lambda=0.11\). Fix \(s>r\) small enough that \(s+\lambda(2-s)<1\). As in the original factorial proof, \(|\vartheta(t)-t|\ll_s t^s\). Set \(Y_{\max}=x/u_0\), \(a=L+1\), and \(W(y)=R_{\mathcal L}(y)/y^2\). For \(a\le y\le Y_{\max}\), the upper eta prime cutoff exceeds \(y\). Consequently
\[
 W(y)=\tfrac12+O_s(y^{s-1}+x^{0.025}/y),\qquad
 |W(y)|\ll1,\qquad |W'(y)|\ll 1/y \text{ a.e.}
\]
The first estimate integrates the complete theta discrepancy and restores every removed prime \(q\le x^{0.025}\) at a cost \(O(yx^{0.025})\) before division by \(y^2\). The last estimate follows from \(R'_{\mathcal L}(y)=\sum_{q<y,\ q\in\mathcal L}\log q\ll y\) off the finitely many corners.

Impose
\[
 \mathcal M(E)=\int_a^{Y_{\max}} E(y)W(y)\frac{dy}{y^2}=0. \tag{2}
\]
All inputs in \(W\) are actual lower ordinary primes, with the same deterministic \(x\) and cutoffs. This condition is finite and computable from them. It uses no information about primes in \(\mathcal H\), positive stops or zeros.

Here are the solvability and conditioning details. For each \(R=2L+1,\ldots,3L\), take weights \(d_i\) at \(4^i R\), \(i=0,\ldots,4\), where \(\sum d_i t^i=P_0(t)=(t-1)^2(t-2)(t-4)\). They preserve the previous four equations, by the equalities \(P_0(1)=P_0'(1)=P_0(2)=P_0(4)=0\). Write \(E_R(y)=-\sum d_i J_{4^iR}(y)\). It vanishes below \(R\), since there all five factorial ramps agree. The elementary periodic formula and the four homogeneous equations give \(|E_R(y)|\ll R^2,\ |E_R'(y)|\ll R\) a.e. Its full continuum sensitivity is
\[
 \int_1^\infty E_R(y)y^{-2}dy
 =-\zeta(0)\sum_i d_i(4^iR)\log(4^iR)
 =-4\zeta(0)R\log(4)P_0'(4)\ne0 .
\]
Indeed the Mellin transform at \(s\) is \(-\zeta(s)\sum_i d_i(1-m_i^{1-s})/[s(s+1)]\). The removable value at zero follows by differentiation, using \(\sum d_i(1-m_i)=0\); boundedness of \(E_R\) justifies the integral there. Multiplying by \(W\) and truncating at \(Y_{\max}\) changes one half of the full integral by \(O_s(L^s+x^{0.025}+L^2/Y_{\max})=o(L)\), uniformly in \(R\). Thus all slopes have the same sign and size \(\gg L\), including their average over \(R\).

The original distributed \(E_0\) satisfies \(|\mathcal M(E_0)|\ll L\log^2(2L)\). Add \(\beta L^{-1}\sum_R E_R\) with \(\beta=-\mathcal M(E_0)/\mathcal M(L^{-1}\sum_R E_R)=O(\log^2(2L))\). This solves (2) exactly. The new factorial calibration uses indices at most \(768L\), keeps all four old moments and all prefix coefficients, and preserves the uniform bounds \(\sum |a_m|m^v\ll_v L^v\log^2(2L)\), \(|m a_m^{\rm correction}|\ll\log^2(2L)\). All previously used old-prime localization error estimates are uniform under these bounds, also for this fixed-factor increase of the largest index. The final \(E\) satisfies
\[
 |E|\ll L^2\log^2(2L),\qquad |E'|\ll L\log^2(2L)\ \text{a.e.},\qquad E(a)=0 .
\]

It remains to replace the outer prime sum by the continuum that (2) sets to zero. Dividing (1) by \(-x^2\) gives the integral of \(E(x/p)W(x/p)\) against \(d\vartheta(p)\) on \(\mathcal H\). Its ordinary-length integral is \(x\mathcal M(E)=0\). For \(y=x/p>L^2\), both integrals are \(O(x\log^2(2L))\) by the bound on \(E\), bounded \(W\), and \(\vartheta(x/L^2)\ll x/L^2\). For \(a\le y\le L^2\), apply Stieltjes summation against \(\vartheta(p)-p\). The possible endpoint terms, for either convention at a cutoff prime, are controlled by \(O_s(x^s L^{2-2s}\log^2(2L))\); the other endpoint has \(E(a)=0\). The elementary pointwise derivative gives the integral error
\[
 O_s\!\left(x^s\log^2(2L)\int_L^{L^2}
       y^{-s}(L+L^2/y)dy\right)
 \ll_s x^s L^{3-2s}\log^2(2L).
\]
This already suffices when \(s+\lambda(3-2s)<1\), including \(\lambda=0.10\). The following estimate recovers the full stated range.

Write \(\psi_0(t)=\{t\}-1/2\). Since \(J_m'(y)=m\{y/m\}-\{y\}\) almost everywhere, \(\sum a_m=1\), and \(\sum m a_m=3\), the exact periodic derivative is
\[
 E'(y)=\psi_0(y)-\sum_{m\le 768L}m a_m\psi_0(y/m).
\]
All coefficients, including those of the fifth distributed calibration, are \(O(\log^2(2L))\). Absorb the standalone \(\psi_0(y)\) into the coefficient at \(m=1\). The Fourier series of \(\psi_0(y/m)\) has coefficients \(-1/(2\pi i k)\) at nonzero frequencies \(k/m\). On grouping its frequencies in lowest terms as \(a/b\), the resulting coefficient has magnitude
\[
 \ll \frac{1}{|a|}\sum_{j\le768L/b}\frac{\log^2(2L)}j
 \ll \frac{\log^3(2L)}{|a|}.
\]
There are at most \(768L\) denominators \(b\), so the sum of all squared coefficients is \(O(L\log^6(2L))\). The frequencies are separated by at least \((768L)^{-2}\). For \(Y>0\), this gives
\[
 \int_Y^{2Y}|E'(y)|^2dy\ll (Y+L^2)L\log^6(2L).
\]
For details, first take finite Fejér sums of all sawtooths. Their individual Fourier multipliers have absolute value at most one, so the grouped bound holds unchanged. Majorize the interval by a fixed multiple of \(\operatorname{sinc}^2(\delta(y-3Y/2))\), where \(\operatorname{sinc}(v)=\sin(\pi v)/(\pi v)\) and \(\delta=\min(1/Y,1/[2(768L)^2])\). This majorant has integral \(O(Y+L^2)\) and Fourier support in \([-\delta,\delta]\). All cross frequencies therefore vanish in the majorized integral. Passing to the limit on the interval is legitimate by almost-everywhere convergence and Fatou's lemma.

For \(L\le Y\le L^2\), Cauchy–Schwarz bounds \(\int_Y^{2Y}y^{-s}|E'(y)|dy\) by
\[
 \ll_s\log^3(2L)\,[Y^{1-s}L^{1/2}+Y^{1/2-s}L^{3/2}]
 \ll_s L^{2-s}\log^3(2L),
\]
using \(s>1/2\). The term with \(W'\) is bounded over the full range by \(O_s(L^{2-s}\log^2(2L))\) using its absolute pointwise bound. Summing dyadic intervals gives an outer-prime error \(O_s(x^s L^{2-s}\log^4(2L))=o(x)\). Along with the paid tails this yields \(T=O_s(x^3\log^2(2L))\) for the whole admissible range above \(0.025\). At \(s=0.874,\lambda=0.11\), the exponent in the new error is \(0.99786\). The positive genuine-prime rectangle above lies in this sector. A fifth equation involving only the derivative of the symbol at zero would cancel the \(W=1/2\) continuum; condition (2) also pays the actual lower-prime discrepancy on the same interval.

## What is left

There is a sharp obstruction inside the residual coprime pairs. It applies to the subpower cutoff above, the calibrated \(L=\lfloor x^{0.10}\rfloor\), and the original \(L=\lfloor x^{0.11}\rfloor\). Fix \(A>0\). For every \(Q\le(\log x)^A\) and every pair of reduced residue classes modulo \(Q\), the corresponding cell of the **actual** coprime, long-shift, large-lcm product contains a completely positive subtotal \(\gg x^4/\varphi(Q)^2\) and a completely negative subtotal \(\ll-x^4/\varphi(Q)^2\). The constants are uniform in \(Q\) and the chosen units. These are explicit disjoint families, not a bound for the signed sum of the cell. No external zero ceiling is needed to compute their signs or sizes.

For the positive family use first rows \(n=pq\) with \(x^{.77}<p<x^{.79}\), and \(0.2x/p<q<0.3x/p\). Use second rows \(m=p'q'\) with \(x^{.82}<p'<x^{.84}\), and \(0.5x/p'<q'<0.6x/p'\). All labels here are ordinary primes. The four prime ranges are disjoint for large \(x\). The full first row has coefficient \(-\log p\) because \(q\) is a prime past all old calibrations. The full second row has coefficient \(-\log q'\) by the fibre calculation above. Each pair is coprime, its shift is at least \(0.2x\), and its lcm is its full product \(\asymp x^2\).

Here are the magnitudes, including the absence of a log loss. Put \(C(c,d)=\int_c^d(1-v)dv\). On a rectangle \(x^a<p<x^b,\ c x/p<q<d x/p\), ordinary PNT and partial summation give the two positive weighted sums
\[
 \sum (x-pq)\log p\sim C(c,d)x^2\log\frac{1-a}{1-b},\qquad
 \sum (x-pq)\log q\sim C(c,d)x^2\log\frac ba .
\]
In the first sum the inner count of \(q\) gives \(C(c,d)x^2/[p\log(x/p)]\), uniformly in \(p\) across the fixed exponent range. Integrating \(dp/[p\log(x/p)]\) yields the first log ratio. In the second the inner log weight removes \(\log(x/p)\) and the remaining sum of \(1/p\) gives the second ratio. The product of the two constants, using the two different rectangles above, is positive.

For the negative family keep the same second rows and replace the first rows by \(n=puvw\) with
\[
 x^{.76}<p<x^{.765},\quad L^{.51}<u<L^{.52},\quad L^{.53}<v<L^{.54},
 \qquad 0.2x/(puv)<w<0.3x/(puv),
\]
again with all labels prime. The four factors are uniquely recoverable from their disjoint ranges. The two small primes are below \(L\), their product exceeds \(768L\) eventually, and \(w\) exceeds every factorial calibration. For the two fixed values of \(\lambda\), \(w\) has exponents between \(0.118\) and \(0.14\), separated from \(q'\). For subpower \(L\), its exponent lies between \(0.235-o(1)\) and \(0.24+o(1)\), also separated from \(q'\). Thus all pairs with the second rows are again coprime, macroscopically separated, and of lcm \(\asymp x^2\). The only divisors of \(uvw\) up to \(L\) are \(1,u,v\); none is a correction node. The exact factorial coefficient is \(1+\mu(u)+\mu(v)=-1\) and hence \(r_1(uvw)=+1\). The product of the complete rows is negative.

To count this family, set \(\lambda=\lim\log L/\log x\), allowing \(\lambda=0\). For the positive magnitude of the first row sum divided by \(x^2\), the limit is
\[
 C(.2,.3)
 \int_{.76}^{.765}\int_{.51}^{.52}\int_{.53}^{.54}
 \frac{d\gamma\,d\beta\,d\alpha}
 {\beta\gamma[1-\alpha-\lambda(\beta+\gamma)]}>0.
\]
Sum first over \(w\) using the uniform fixed-ratio PNT. The resulting sum is a constant times \(\sum_{p,u,v}\log p/[puv\log(x/(puv))]\). Partial summation in the three remaining disjoint prime ranges gives the integral. Equivalently use Riemann sums on the compact exponent box, with ordinary PNT for \(\sum\log p/p\) and the reciprocal-prime asymptotic for \(\sum1/u,\sum1/v\). All weights are bounded in the rescaled variables, and \(L\to\infty\) even at \(\lambda=0\). Multiplication by the second-row magnitude establishes the order \(x^4\).

Finally, to impose \(n\equiv a_0,\ m\equiv b_0\bmod Q\), condition the last prime \(q,w\), or \(q'\) in each sum after fixing all earlier prime labels. The earlier primes exceed \(Q\) uniformly, so the required class is a unit. Every last prime is on a fixed-ratio interval at a scale at least \(x^{0.11}\). The Siegel–Walfisz theorem and partial summation therefore give \(1/\varphi(Q)\) times the stated inner main term with uniform relative \(o(1)\), by choosing a sufficiently high logarithmic saving for the fixed \(A\). The Cartesian product yields the claimed \(1/\varphi(Q)^2\) for each sign. Thus even simultaneous congruences of polylogarithmic total modulus leave positive and negative mass at the natural \(x^4\) exponent; arithmetic cancellation must still take place within or between the signed subfamilies. [Thorner and Zaman, quantitative prime number theorem for arithmetic progressions](https://arxiv.org/abs/2108.10878)

With the original subpower \(L\) the entire signed region \(\gcd(n,m)>x^{1/4}L\log^2(2L)\) is paid independently. With the fifth calibrated power \(0.11\), the analogous threshold is \(x^{0.36}\log^2(2L)\) up to the floor. Both constructions allow the residual statement to retain simultaneously the long shift, large lcm, and \(\gcd(n,m)\le D\). The remaining pairs include coprime rows. The induced scalar \(S_1S_2\) involves all of them, and neither the large-gcd estimate nor the calibrated continuum gives their required independent upper.
