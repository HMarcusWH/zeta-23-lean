# A finite positive residue statistic for the zero displacement

**DERIVED on paper.** Let \(B=\sup_\rho\Re\rho\), where \(\rho\) runs over the nontrivial zeros of the Riemann zeta function. For each integer \(L\ge2\), take the four factorial coefficients from [the old-prime localization](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) together with their prescribed Möbius prefix. More precisely, \(a_m=-\mu(m)/m\) for \(2\le m\le L\); use the four extra nodes \(R,4R,16R,64R\) with \(R=2L+1\), solving the exact real equations

\[
 \sum_m a_m=1,\quad \sum_m a_m\log m=1,\quad
 \sum_m a_m(1-\sqrt m)=1/\zeta(1/2),\quad \sum_m a_m(m-1)=2 .           \tag{1}
\]

The conclusions also hold for the previously defined equal-weight average of such four-node calibrations over \(2L+1\le R\le3L\). Fix either prescription in advance. For integer \(n\) put \(t_m(n)=n\bmod m\in\{0,\ldots,m-1\}\) and define

\[
 e_L(n)=-1+\tfrac12\sum_m a_m t_m(n)(m-t_m(n)),\qquad
 \mathcal B_L=\sum_{L+1\le n\le\lfloor L^{1.01}\rfloor}\frac{|e_L(n)|}{n^3} .
\]

Then at **every integer cutoff** tending to infinity,

\[
 \boxed{\ \mathcal B_L=L^{B-1+o(1)} .\ }                                \tag{2}
\]

Both finite sums with \(|e_L(n)|\) replaced by \([e_L(n)]_+\) or \([-e_L(n)]_+\) have the same exponent for the four original calibrations. In particular, an independent proof that for every \(\epsilon>0\) there exist arbitrarily large integers \(L\) with \(\mathcal B_L\le L^{-1/2+\epsilon}\) would imply RH. Conversely RH implies this cofinal upper by (2). The direct proof below establishes (2) unconditionally, even with three rational moment targets in place of (1). The separate true-prime comparison uses the external zero ceiling. Establishing the cofinal upper from the finite residue arithmetic remains open.

## Passing from true primes to ordinary integration

Let \(x=L^{100/11}\), so the cutoff \(\lfloor x^{0.11}\rfloor\) is exactly \(L\) for every integer \(L\). Write \(J_m(y)=\sum_{j\le y}(1-m\mathbf1_{m\mid j})(y-j)\), \(E(y)=y-1-\sum_m a_m J_m(y)\) for \(y\ge1\), and \(K_x(u)=uE(x/u)\) for \(0<u\le x\). This is the original factorial weight. Put \(a=x/L^{1.01}\) and \(b=x/(L+1)\). By the [complete signed-mass theorem](FACTORIAL_TERMINAL_MASS_EXPONENT.md),

\[
 \sum_{a<p<b}|K_x(p)|\log p=x^2L^{B-1+o(1)},\qquad
 \sum_{a<p<b}[\pm K_x(p)]_+\log p=x^2L^{B-1+o(1)}.                     \tag{3}
\]

In using this paper theorem we retain its genuine full signed input, the actual residues on true prime weights, its endpoint normalization and its small-prefix bound.

Here is the independent error bound for replacing each prime measure in (3) by Lebesgue measure. Fix \(s=0.874\); the [pinned external zero ceiling](../step4-height-window-2026-11-19/STEP4_HEIGHT_AND_GRAPH_RESULTS.md) implies both \(\vartheta(u)-u=O(u^s)\) and \(M(u)=\sum_{j\le u}\mu(j)=O(u^s)\), using a strictly smaller intermediate exponent when absorbing logarithms. The four extra coefficients satisfy \(\sum_{m\,{\rm extra}}|a_m|\ll L^{s-1}\log^2(2L)\), including the distributed option. These transfers and the calibration estimate are proved in the [factorial mass theorem](FACTORIAL_TERMINAL_MASS_EXPONENT.md).

For \(y\ge L\) away from integer knots the derivative of \(E\) is a prefix sum of the coefficients of \(1-\zeta D\), where \(D(z)=\sum a_m(1-m^{1-z})\). The omitted Möbius part of this prefix is \(\sum_{k\le y/L}[M(y/k)-M(L)]\), whose absolute value is \(O_s(yL^{s-1})\) by summing \((y/k)^s\). The calibration part is \(\sum_{m\,{\rm extra}}ma_m\lfloor y/m\rfloor\), at most \(O(yL^{s-1}\log^2(2L))\). Because \(E=0\) on \([1,L+1]\), integration gives

\[
 |E'(y)|\ll yL^{s-1}\log^2(2L)\quad\text{a.e.},\qquad
 |E(y)|\ll y^2L^{s-1}\log^2(2L).
\]

Each of \(F(u)=|K_x(u)|,[K_x(u)]_+,[-K_x(u)]_+\) is continuous and absolutely continuous on \([a,b]\), with \(|F'|\le |K_x'|\) almost everywhere. Thus for \(y=x/u\),

\[
 |F(u)|\ll u y^2L^{s-1}\log^2(2L),\qquad
 |F'(u)|\le|E(y)-yE'(y)|\ll y^2L^{s-1}\log^2(2L).
\]

Stieltjes partial summation against \(\vartheta(u)-u\) bounds the discrepancy by the two boundary terms and \(\int_a^b |F'(u)|u^sdu\). At \(b\), \(F(b)=0\). Excluding a possible prime at \(a\) uses \(\vartheta(a)\) in the lower endpoint. The interior is \(O(x^2 L^{s-1}\log^2(2L)\int_a^b u^{s-2}du)\). Including the lower boundary, the total is

\[
 O\big(x^{1+s} L^{0.01(1-s)}\log^2(2L)\big)
 =O\big(x^{1.8741386}\log^2(2x)\big).                                  \tag{4}
\]

The least possible exponent in (3) is \(2-0.11/2=1.945\), strictly above (4). The same leading exponent therefore holds for each of the three ordinary integrals. The change of variable \(y=x/u\) divides out the factor \(x^2\) exactly, giving

\[
 \int_{L+1}^{L^{1.01}} \frac{|E(y)|}{y^3}\,dy=L^{B-1+o(1)},\qquad
 \int_{L+1}^{L^{1.01}} \frac{[\pm E(y)]_+}{y^3}\,dy=L^{B-1+o(1)} .    \tag{5}
\]

## The finite reciprocal mesh and sign changes

At each integer \(n\), the identity \(2J_m(n)=(m-1)n-t_m(n)(m-t_m(n))\) and the last calibration in (1) give \(E(n)=e_L(n)\). Write \(N=\lfloor L^{1.01}\rfloor\). The single partial cell \([N,L^{1.01}]\) contributes \(O(L^2\log^2(2L)/N^3)=o(L^{-1/2})\) even in absolute value: the exact periodic formula for real arguments gives \(|E(y)|\ll L^2\log^2(2L)\) using \(0\le d_m(y)\le m^2/4\) and the coefficient bound \(\sum|a_m|m^2\ll L^2\log^2(2L)\). Thus every integral in (5) retains its exponent when stopped exactly at \(N\).

On a full interval \(y\in[n,n+1]\) the ramp \(E(y)\) is affine. After the reciprocal substitution \(z=1/y\), the integrand with measure \(dy/y^3\) becomes the absolute value or the requested positive part of \(W(z)=zE(1/z)\) with measure \(dz\). This \(W\) is affine between \(1/(n+1)\) and \(1/n\). For an affine function of endpoint values \(A,C\) on an interval of length \(h\), the integral of its absolute value equals the trapezoid \(h(|A|+|C|)/2\) when their signs agree. If their signs differ it equals \(h(|A|^2+|C|^2)/(2(|A|+|C|))\). Hence the absolute integral always lies between half the absolute trapezoid and the full trapezoid. If both endpoints are zero the integral is zero as well.

For the full reciprocal cells with \(L+1\le n<N\), combine adjacent trapezoids. The weight multiplying \(|E(n)|\) at each interior index is exactly

\[
 \frac1{2n}\left(\frac1{(n-1)n}+\frac1{n(n+1)}\right)=\frac1{n(n^2-1)}.
\]

The starting value is zero. The single coefficient for the final index \(N\) is \(1/[2N^2(N-1)]\). All these nonzero weights are between fixed positive multiples of \(n^{-3}\) for large \(L\), including the last one. This proves (2) from (5). For a single sign, convexity gives an upper trapezoid for the integral of \([\pm W]_+\) throughout each cell. It need not be comparable from below to that trapezoid if its positive side is thin. The lower exponent for each signed endpoint sum instead follows from the corresponding **integral lower** in (5) and this one-sided trapezoid inequality. Its upper exponent follows from (2). No restriction on where a sign change falls in a cell is needed.

## Direct proof, including the case of zeros approaching the line one

The exponent of this finite statistic can also be proved without the external zero ceiling. This gives a version with entirely rational arithmetic, for which the absolute-value conclusion holds. The comparison with the original true-prime observable still uses the prime-measure result (3) and its four calibrations.

Assume the same Möbius prefix, with remaining nodes in \((L,CL]\) for a fixed \(C\). Impose \(\sum a_m=1,\ \sum m a_m=3\). The calibrations below additionally satisfy the total correction bounds used in this proof. Write \(D_L(z)=\sum_m a_m(1-m^{1-z})\). It begins with \(\sum_{n\le L}\mu(n)n^{-z}\), followed by the finite correction \(-\sum_{m\ {\rm extra}}ma_m m^{-z}\). At each integer the two imposed moment equations give the same displayed formula for \(e_L(n)\). Between consecutive integers \(E\) is the affine interpolant. It is bounded for fixed \(L\) on \([1,\infty)\), since the integer values are periodic.

For \(\Re z>1\), integrate absolutely convergent first-order ramps against \(y^{-z-2}\). For a ramp \((y-j)_+\) this gives \(j^{-z}/(z(z+1))\). Since \(E=0\) through \(L+1\), the exact identity is

\[
 \int_{L+1}^{\infty}E(y)y^{-2-z}\,dy
 =\frac{1-\zeta(z)D_L(z)}{z(z+1)} .                                \tag{6}
\]

The left side converges locally uniformly on \(\Re z>-1\) for fixed \(L\). The pole of \(\zeta\) at 1 cancels since \(D_L(1)=0\). Consequently (6) also holds at every nontrivial zero \(\rho=\beta+i\gamma\), where its value is \(1/[\rho(\rho+1)]\). This uses the actual zero at a fixed height and is independent of multiplicity.

We give bounds uniform in \(L\) for each of the coefficient prescriptions in this note. If \(B<1\), choose a fixed \(B<b<1\). The proof of (2) in the [factorial mass theorem](FACTORIAL_TERMINAL_MASS_EXPONENT.md) uses only that strict inequality, then the standard zero-free disk estimate for \(1/\zeta\) and sharp-cut Perron at half-integers. It gives \(\sum_{n\le u}\mu(n)n^{-it}\ll_{b,\epsilon}u^{b+\epsilon}(1+|t|)^\epsilon\). Choosing \(b\) sufficiently close to \(B\), partial summation on any fixed line \(u<0\) gives

\[
 |D_L(u+it)|\ll_{u,\epsilon}L^{B-u+\epsilon}(1+|t|)^\epsilon.
\]

Here the total absolute mass of the extra \(a_m\)'s before multiplication by \(m^{1-u}\) is \(O_\epsilon(L^{B-1+\epsilon})\). For the four original nodes this was proved in the linked paper. The rational and five-node constructions are verified below. If \(B=1\), use \(\sum_{n\le L}n^{-u}\ll_u L^{1-u}\) and \(\sum_{\rm extra}|a_m|\ll\log^2(2L)\). This proves the same displayed bound by absolute summation, uniformly even for unbounded \(t\).

For \(J(y)=\sum a_mJ_m(y)\), shift the Mellin contour of \(\zeta(z)D_L(z)y^{1+z}/[z(z+1)]\) from 2 to \(u=-1/2+\eta\), where \(0<\eta<1/4\). The starting integral is absolutely convergent. The functional equation gives \(|\zeta(u+it)|\ll_\eta (1+|t|)^{1-\eta}\) on the target line. Choose the height epsilon strictly below \(\eta/2\). Then the new vertical is absolutely integrable by a power in \(|t|\), uniformly in \(L\) after retaining the displayed \(L\) factor. For each fixed \(L,y\), the polynomial \(D_L\) is bounded on the shifting strip independently of the height, and convexity on the critical strip, the functional equation to its left, and absolute convergence to its right give \(\zeta(\sigma+it)\ll_\eta (1+|t|)^{1-\eta/2}\) uniformly there at large heights. Thus horizontals vanish. The pole at zero has residue \(y\), because \(D_L(0)=-2,\ \zeta(0)=-1/2\); the would-be pole at 1 is removable and \(-1\) is outside. Subtracting \(J\) from \(y-1\) and taking sufficiently small preliminary \(\eta\) and epsilons yields

\[
 |E(y)|\ll_\epsilon L^{B+1/2+\epsilon}y^{1/2+\epsilon}\qquad(y\ge1). \tag{7}
\]

There is also a sharper bound near the first knot. If \(B<1\), the exact prefix derivative formula preceding (4), with \(s\) replaced by any \(b>B\) sufficiently close to \(B\), gives \(|E(y)|\ll_\epsilon y^2 L^{B-1+\epsilon}\) on \(y\ge L\). If \(B=1\), the elementary estimate \(|M(v)|\le v\) costs \(O(y\log(2y))\) for the omitted prefix in \(E'\), and extras cost \(O(y\log^2(2L))\). Hence \(|E(y)|\ll_{\epsilon,\delta}y^2L^\epsilon\) for \(L\le y\le L^{1+\delta}\), for any fixed \(\delta>0\). Integrating on this band gives an absolute upper of \(L^{B-1+o(1)}\) in logarithmic exponent.

For the lower select an actual zero with \(\beta\ge1/2\) sufficiently near \(B\) and choose

\[
 \frac{B+1/2}{\beta+1/2}<d<1+\delta.
\]

Equation (7) bounds the tail of (6) beyond \(L^d\) by \(O_\epsilon(L^{B+1/2+\epsilon-d(\beta+1/2-\epsilon)})=o(1)\) after fixing a sufficiently small epsilon. On the initial band \(y^{-\beta-2}\le L^{d(1-\beta)}y^{-3}\), so (6) gives

\[
 \int_{L+1}^{L^{1+\delta}} |E(y)|y^{-3}dy\gg_\rho L^{-d(1-\beta)} .
\]

Take the lower limit as \(L\) tends to infinity with \(\rho,d\) fixed. Then let \(\beta\) approach \(B\) through actual zeros and \(d\) approach 1 subject to its strict inequality. This covers \(B=1\) without assuming it attained; for \(B=1/2\) any critical-line zero works. The upper and lower together give exponent \(B-1\). The reciprocal-mesh argument above transfers the result to the finite positive statistic for every fixed \(\delta>0\). In its endpoint estimate the incomplete cell costs \(O(L^2\log^2(2L)/\lfloor L^{1+\delta}\rfloor^3)\).

For the original four-node family \(D_L'(1)=1\). Thus (6) at \(z=1\) gives zero, including the limit \(\zeta(z)D_L(z)\to1\). By (7) the signed tail beyond \(L^{1+\delta}\), in absolute value, is \(O_{\delta,\epsilon}(L^{B-1-3\delta/2+\epsilon})\) after choosing a smaller preliminary epsilon. The signed initial band is smaller by a fixed power than its absolute mass. Each sign therefore has exponent \(B-1\), first in the continuum and then on the endpoint mesh as above, without an external ceiling.

## Rational coefficients and exact mean over the integer residues

Keep the prefix, take \(2L+1\le R\le3L\), and use three nodes \(R,2R,4R\). Set

\[
 \sum a_m=1,\qquad \sum ma_m=3,\qquad \sum m^2a_m=13.                 \tag{8}
\]

Write \(M=\sum_{n\le L}\mu(n),\ N_1=\sum_{n\le L}n\mu(n)\) and put \(A_0=\sum_{n\le L}\mu(n)/n,\ A_1=(2+M)/R,\ A_2=(12+N_1)/R^2\). Then

\[
 a_{4R}=(A_2-3A_1+2A_0)/6,\qquad
 a_{2R}=A_1-A_0-3a_{4R},\qquad a_R=A_0-a_{2R}-a_{4R}.
\]

These are exact rational numbers. The coefficients solve the three normalized moment equations with rows \(1,d,d^2\) at \(d=1,2,4\). If \(B<1\), partial summation gives \(M=O_\epsilon(L^{B+\epsilon}),\ N_1=O_\epsilon(L^{B+1+\epsilon})\); the tail of the series at 1 for \(1/\zeta\) gives \(A_0=O_\epsilon(L^{B-1+\epsilon})\). Thus the three corrections individually satisfy the bound used above. For \(B=1\) the elementary bounds give at worst \(O(\log(2L))\). This proves the unconditional absolute-exponent theorem for (8).

Averaging these rational vectors over the \(L\) integer choices \(2L+1\le R\le3L\) retains every equation. Each extra node \(m\asymp L\) can receive at most three contributions before division by \(L\), one per factor \(1,2,4\). The distributed coefficients therefore satisfy \(|a_m|\ll\log^2(2L)/m\) at every node, and \(O_\epsilon(L^{B-2+\epsilon})\) individually at extra nodes if \(B<1\). The total absolute correction bounds still hold. With \(D_*=\mathrm{lcm}\{m:a_m\ne0\}\), each residue of a fixed modulus \(m\) occurs exactly \(D_*/m\) times in one period. As \(m^{-1}\sum_{r=0}^{m-1}r(m-r)=(m^2-1)/6\),

\[
 D_*^{-1}\sum_{n=1}^{D_*} e_L(n)
 =-1+\frac1{12}\sum_m a_m(m^2-1)=0 .
\]

This is an exact uniform-period mean. The signed integral weighted by \(y^{-3}\) is given by (6) at 1 and requires the separate log calibration to vanish. For (8) alone we assert the exponent of the absolute statistic.

A five-node option keeps all four original arithmetic normalizations in (1) and adds the last condition in (8). Take \(m_i=4^iR\) for \(0\le i\le4\). After fixed row operations and scaling, the matrix rows in \(i\) are \(1,i,2^i,4^i,16^i\); their confluent Vandermonde determinant is nonzero (nodes \(1,1,2,4,16\), using derivative data at 1). Dividing the new moment discrepancy \(12+N_1\) by \(R^2\) gives \(O_\epsilon(L^{B-1+\epsilon})\) for \(B<1\). The previous four normalized discrepancies have the same bound, including the log row after subtracting \(\log R\) times the zeroth row. At \(B=1\), absolute summation bounds these rows by \(O(\log^2(2L))\). Consequently all uniform estimates used above apply. Averaging in \(R\) spreads the corrections with \(|a_m|\ll\log^2(2L)/m\). This real family enjoys both the full-period mean and the zero signed weighted integral, as well as both sign exponents. Its square moment preserves the previous four normalizations.

For \(L<2^{100}\), the numerical band at \(\delta=0.01\) stops below \(2L\), so every real ramp in it is \(E(y)=\sum_{L<j\le y}\mu(j)(y-j)\). Indeed every omitted divisor contributing in that first band is \(j\) itself and the extra nodes exceed \(2L\). Consequently all prescriptions above agree in that range, even though their period and weighted means can differ. A finite test confined to that band cannot distinguish the prescriptions.

The remaining arithmetic task is an independent cofinal upper \(\mathcal B_L\le L^{-1/2+\epsilon}\) for every \(\epsilon>0\) in any one of these fixed prescriptions. A complete-period mean evaluates a different measure from the short weighted interval beginning at \(L+1\). The exact exponent and its two proofs do not themselves establish that upper. Step 4 and RH remain OPEN.
