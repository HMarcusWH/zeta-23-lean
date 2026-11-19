# A one-sided count at perfect fourth powers

**DERIVED on paper, 19 November 2026. Step 4 and RH are OPEN.** An independent estimate for the frequency of an explicit prime deficit would suffice. Define

\[
 C_m=\pi(m^4)-\operatorname{li}(m^4),\qquad b_m=m^2\log m/(2\pi),\qquad
 D^-(M)=\#\{8\le m\le M:C_m<-b_m\}.
\]

Here \(\operatorname{li}(x)=\operatorname{Ei}(\log x)\) and \(\pi(x)\) counts ordinary primes. The following three statements are equivalent:

1. RH.
2. \(C_m\ge-b_m\) for every \(m\ge8\).
3. For some fixed \(\kappa>0\), \(D^-(M)=O(M^{1-\kappa})\) for all sufficiently large \(M\).

The same equivalence holds for the upper barrier alone. Thus if RH fails, violations of **each** sign separately have upper counting exponent one. This means \(\limsup\log(1+D^\pm(M))/\log M=1\). It permits zero ordinary density. We derive the converse and the counting assertion here. The forward direction uses Schoenfeld's conditional bound. No novelty or Lean verification is claimed. [Schoenfeld, Corollary 1](https://doi.org/10.1090/S0025-5718-1976-0457374-X) · [Johnston, including the explicit unconditional finite range](https://doi.org/10.1007/s11139-022-00616-x)

## Preserving the signed prime measure when replacing cells by their midpoints

Put \(B=\sup_\rho\Re\rho=1/2+d\), over nontrivial zeta zeros. Thus \(0\le d\le1/2\), including the possibility of an unattained supremum. Write \(c(x)=(\lfloor x^{1/4}\rfloor+1/2)^4\), and \(d\nu_\pi=d\pi-dx/\log x\) on \(x\ge16\). The pushforward keeps the original signed mass of every cell. No prime is a fourth power here. The dyadic difference

\[
 I_X(s)=\int W(x/X)\big(c(x)^{-s}-x^{-s}\big)\,d\nu_\pi(x)
\]

for a smooth partition function \(W\) with support in a fixed compact subinterval of \((0,\infty)\) satisfies, locally uniformly on every compact set of \(s\), with \(\sigma=\Re s\),
\[
 |I_X(s)|\ll_{W,K,\epsilon}X^{1/2+2d/3-\sigma+\epsilon}.
 \tag{1}
\]
The constant can depend on the actual \(d\). The grid, weights and terminal deficits do not depend on \(d\). The estimate only needs the elementary zero count, not a density theorem.

For details let \(\theta=1/4,\ v=x^\theta,\ b(v)=1/2-\{v\}\), and \(e(y)=\exp(2\pi i y)\). Taylor-expand \(v^{-4s}\) at \(v\) through first order with increment \(b(v)\). The second-order term integrated in absolute value is \(O_K(X^{1-\sigma-2\theta})\) by Chebyshev's bound. In the first-order term use \(d\nu_\pi=(d\vartheta-dx)/\log x\). After taking out \(X^{-s-\theta}\), the amplitude is a smooth dyadic family \(A(x/X)\), uniformly bounded with any fixed number of derivatives including the \(1/\log x\) factor. Write \(X\) sufficiently large throughout; all finitely many initial cells are harmless.

The needed harmonic estimate, for either sign of \(h\), \(1\le |h|\le X\), \(F=|h|X^\theta\), is
\[
 \left|\int A(x/X)e(hx^\theta)(d\vartheta-dx)\right|
 \ll_{\epsilon,A}X^{B+\epsilon}\sqrt F .
 \tag{2}
\]
One proof uses the complete von Mangoldt sum. For \(B<1\), shift the smoothed Mellin integral with multiplier \(-\zeta'/\zeta\) from \(\Re z>1\) to a fixed line strictly between \(B\) and \(\min(1,B+\epsilon/2)\). The pole at 1 gives precisely the subtracted continuum. The logarithmic derivative on the new line is \(O_\epsilon(\log(2+|\Im z|))\) by the local partial fraction formula and the distance to the zero set. For the smooth transform in \(\log(x/X)\), Plancherel and Cauchy–Schwarz on \(|\Im z|\le C(1+F)\) bound its \(L^1\) norm by \(O(\sqrt F)\). Outside this range repeated integration by parts gives arbitrary inverse powers of \(|\Im z|\), since the phase derivative dominates and higher derivatives are \(O(F)\). The constants only need bounded smooth seminorms of \(A\). Proper powers of primes cost \(O(X^{1/2}\log^2 X)\) in absolute value by summing their counts. This proves (2) for the stated measure. For \(B=1\) the elementary total mass bound suffices. For the continuum alone repeated integration by parts gives \(O_N(XF^{-N})\). [Details of the Mellin-line bound](TRANSLATED_GRIDS.md)

Vaaler's trigonometric approximation to the centered sawtooth has coefficients \(O(1/|h|)\), \(1\le |h|\le H\). Its pointwise error is bounded by a positive Fejér polynomial with coefficients \(O(1/H)\), including its constant term. The point values at integer \(v\) are immaterial for \(d\vartheta\) and \(dx\). Integrate the error against a smooth nonnegative majorant of \(|A|\) times \(d\vartheta+dx\). For the nonzero harmonics use (2) plus twice the smooth continuum integral. Since \(F\ge X^{1/4}\), the latter is negligible by choosing a fixed large integration order. The zero harmonic costs \(O(X/H)\). Summing \(\sqrt h/h\) and \(\sqrt h/H\) gives
\[
 |I_X(s)|\ll X^{-\sigma-\theta}
     \big[X^{B+\epsilon+\theta/2}H^{1/2}+X/H\big]
     +X^{1-\sigma-2\theta}.
\]
For \(d<3/8\) choose \(H=\max(1,\lfloor X^{1/4-2d/3}\rfloor)\). The first two contributions both have exponent \(1/2+2d/3-\sigma\) up to \(\epsilon\), and the last one has exponent \(1/2-\sigma\). For \(d\ge3/8\) use the elementary first-order absolute bound \(X^{3/4-\sigma}\), which already has the required exponent. This proves (1), including \(d=0\). [Vaaler's approximation](https://doi.org/10.1090/S0273-0979-1985-15349-2)

## The nonreal singularities of the true endpoint counts

Set \(\alpha=1/2+2d/3\). On \(\Re s>1\) form the two integrals
\[
 A(s)=\int_{16}^\infty x^{-s}d\nu_\pi(x),\qquad
 A_4(s)=\int_{16}^\infty c(x)^{-s}d\nu_\pi(x)
       =\sum_{m\ge2}(C_{m+1}-C_m)(m+1/2)^{-4s}.
\]
Summing (1) over a smooth dyadic partition gives single-valued holomorphic continuation of \(A_4-A\) to \(\Re s>\alpha\). Indeed each piece is entire and the series converges normally on compact subsets. A compact initial interval adds an entire function. Differentiating before continuation on \(\Re s>1\) gives
\[
 A'(s)=\zeta'(s)/\zeta(s)+16^{1-s}/(s-1)
    +\sum_{p,\ k\ge2}(\log p)p^{-ks}
    +\sum_{p<16}(\log p)p^{-s}.
\]
The proper-power correction converges normally for \(\Re s>1/2\). The two poles at real 1 cancel. There is no real zeta zero in \((1/2,1)\), for instance by the alternating eta series. Thus \(A_4\) has analytic continuation along the real interval \((\alpha,\infty)\), with a holomorphic germ at each point. At every nonreal zero \(\rho\) with \(\Re\rho>\alpha\), \(A'_4\) has a pole of residue its multiplicity. This derivative argument avoids choosing a global branch of \(\log\zeta\).

Summation by parts, initially on \(\Re s>1\), gives
\[
 A_4(s)=4sD(s)+H_0(s),\qquad
 D(s)=\sum_{m\ge2} C_m m^{-4s-1}.
\]
The symmetric difference of the weights at \(m-1/2\) and \(m+1/2\) is \(4s m^{-4s-1}+O_K(m^{-4\sigma-3})\). The trivial \(|C_m|\ll m^4\) makes the remainder normally summable for \(\sigma>1/2\), including the finite initial boundary term in \(H_0\). In particular \(D\) is analytically continuable along the same real interval.

## How many endpoints would have to violate the bound?

The usual truncated explicit formula gives \(|\pi(x)-\operatorname{li}(x)|\ll_\epsilon x^{B+\epsilon}\). At half-integers use the explicit formula for \(\psi\) at height comparable to \(x\), the bound \(\sum_{0<|\gamma|\le 2x}|\rho|^{-1}\ll\log^2 x\), then remove proper prime powers and partially sum. Endpoint interpolation uses monotonicity. For \(B=1\) the elementary count suffices. This estimate is used at the actual \(B\); it assumes no particular zero-free half-plane. [Explicit-formula details and endpoint checks](ENDPOINT_CHECK.md)

Suppose (3) in the numbered list at the start holds, and suppose for contradiction \(d>0\). Set \(r_m=(-C_m-b_m)_+\) for \(m\ge8\). For \(M<m\le2M\) there are \(O(M^{1-\kappa})\) nonzero terms, of size \(O_\epsilon(M^{4B+\epsilon})\). Hence \(\sum r_m m^{-4s-1}\) is holomorphic by absolute convergence for \(\sigma>B-\kappa/4\). Also \(\sum b_m m^{-4s-1}\) converges absolutely for \(\sigma>1/2\). Add both series to the tail of \(D(s)\); its coefficients \(C_m+b_m+r_m\) are nonnegative.

This positive Dirichlet series has holomorphic germs all along the real interval \((\max(\alpha,B-\kappa/4),\infty)\). By Landau's theorem its abscissa of convergence cannot lie in that interval. To see the relevant step directly, if the series were holomorphic near its real abscissa, Taylor-expand from a point a little to its right into that neighborhood. For a displacement to the left all terms of the double Taylor–Dirichlet series are nonnegative. Exchanging the sums would give convergence strictly to the left of the abscissa. Thus the positive series, and after subtraction \(D\), are holomorphic throughout \(\Re s>\max(\alpha,B-\kappa/4)\). The same would hold for \(A_4\) there. Both cutoffs are strictly below \(B\). By the definition of supremum a zero has real part above both, contradicting the pole of \(A_4'\). This proves the converse. Applying the identical argument to \(-C_m\) gives the upper-barrier version.

Schoenfeld under RH gives (2) in the numbered list upon substituting \(x=m^4\). It trivially implies (3). One can replace \(b_m\) in the converse by \(O_\epsilon(m^{2+\epsilon})\) for every \(\epsilon>0\). The proof for fixed \(b_m\) already suffices. This is a count over **outer endpoints whose full cumulative ordinary-prime deficit is too negative**. An estimate for exceptional short intervals, zero ordinates, primitive ratios, or individual interaction cells needs a quantitative map to these endpoints to be usable.

## Native field and finite evidence

For the literal one-copy pulse \(j\), at large \(t\) the native field is \(\int x^{-1/2}j(t-\log x)\,d\psi(x)\). Subtracting \(dx\) leaves it unchanged by its source moment \(J(1/2)=0\). The proper-power contribution at \(x\asymp X=e^t\) is \(O_j(\log^2 X)\), carried as a term. For the ordinary primes with the continuum removed, the remaining test against \(d\nu_\pi\) is \((\log x)x^{-1/2}j(t-\log x)\). Repeating the Taylor and sawtooth proof on its compact dyadic band gives \(O_{j,\epsilon}(X^{2d/3+\epsilon})\) for moving this test to \(c(x)\), including any boundary cells. The extra log is absorbed by \(\epsilon\). Thus the native source is approximated, at this accuracy, by the literal differences \(C_{m+1}-C_m\) paired with \((\log c_m)c_m^{-1/2}j(t-\log c_m)\), where \(c_m=(m+1/2)^4\). Every original prime and continuum contribution is included. If \(d>0\) the error grows strictly more slowly than the \(d\) rate on the native terminal windows; the triangle inequality preserves their rate. For \(d=0\) the same upper and the nonnegative normalized logarithm give zero rate. [Merged one-copy theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154-L1158)

Johnston independently proves the strict two-sided inequality through \(x=1.101\cdot10^{26}\), covering **every integer \(8\le m\le3{,}239{,}267\)**. The separate reproducible [direct counts](QUARTIC_COUNTS.json) cover \(m=8,\ldots,128\). The first endpoint outside Johnston's stated range is \(3{,}239{,}268\). No lower-barrier violation was found. The required all-scale count estimate for violations remains **OPEN**. The graph's visibility theorem and the paper comparisons above could hold with \(d>0\). [Johnston, Corollary 3.3](https://doi.org/10.1007/s11139-022-00616-x)
