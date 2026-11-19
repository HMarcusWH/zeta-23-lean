# The exact Step 4 obstruction on selected vertices of the ordinary-prime graph

**DERIVED on paper.** The complete signed prime area can be tested where it reaches the top of a positive excursion. On each gap between consecutive primes it is one explicit quadratic. Combining that fact with the signed excursion theorem removes all nonstationary vertices from a test for the zero displacement. The test uses the ordinary primes, their true weights, and the complete arithmetic prefix.

For every prime \(p\), let \(p^+\) be the next prime and set
\[
 S(p)=\sum_{q\le p,\ q\ {\rm prime}}\log q,\qquad
 W(p)=\sum_{q\le p,\ q\ {\rm prime}}q\log q .
\]
Select a vertex exactly when \(p<S(p)<p^+\). For \(X>e\) put
\[
 H(X)=\max_{\substack{X\le p\le X\log X\\p<S(p)<p^+}}
   \frac{\big[S(p)^2/2-W(p)+2\big]_+}{p^{3/2}},
\]
with the empty maximum set to zero. With \(B=\sup_\rho\Re\rho\) over all nontrivial zeta zeros,
\[
 \boxed{\displaystyle
  \lim_{X\to\infty}\frac{\log(1+H(X))}{\log X}= B-\tfrac12 .}       \tag{1}
\]
In particular, it would suffice to establish, independently from the prime arithmetic, that for every \(\epsilon>0\) and \(R\) there is an \(X\ge R\) with \(H(X)\le X^\epsilon\). This is the missing inequality on this route. No advance estimate on where the next selected vertex lies is required.

## Why only these vertices matter

Write \(A(x)=\int_2^x(\vartheta(y)-y)\,dy\). For \(p<x<p^+\) the complete prefix is fixed, giving exactly
\[
 A(x)=x S(p)-W(p)-x^2/2+2 .
\]
At a prime, the right derivative of \(A\) exceeds the left derivative by \(\log p>0\). A local maximum there would require the left derivative to be nonnegative and the right derivative nonpositive, which is impossible. Inside the gap the derivative is \(S(p)-x\). A local maximum in its interior is therefore exactly \(x=S(p)\), with the value used in \(H\). Tangency at a boundary cannot supply an additional maximum. The constant 2 comes from the lower integration limit.

For \(B>1/2\), the integrated explicit formula gives \(|A(x)|\ll x^{1+B}\) by absolute summability of the zero coefficients, including the \(O(x^{3/2})\) proper-power correction. Since \(S(p)<p^+<2p\) at the selected vertices, this gives the upper limit in (1).

For the other direction, fix an actual real part \(b>1/2\) of a zero. The [density isolator](DENSITY_ISOLATOR.md) supplies fixed \(K>1,c>0\) such that **every sufficiently late** \([Y,KY]\) contains a positive and a negative excursion of \(A\), each of magnitude at least \(c x^{1+b}\) at its own argument \(x\). Choose a negative point in \([2X,2KX]\), a positive one in \([2KX,2K^2X]\), and a negative one in \([2K^2X,2K^3X]\). Opposite signs make the order strict even when the intervals meet. The maximum on the compact interval bounded by the two negative points is interior and at least the positive value. Consequently it occurs at some \(S(p)\), with \(p>X\) by Bertrand's postulate and \(p\le2K^3X\le X\log X\) once \(X\) is large. At that vertex the normalized positive value is \(\gg_{b,K}X^{b-1/2}\). Take the lower limit first, then the supremum over actual \(b\); the argument requires no attainment of \(B\). If \(B=1/2\), RH holds by symmetry, and Johnston's theorem gives \(A(x)<0\) throughout \(x>2\). In that case \(H(X)=0\). [Johnston, Theorem 1.2](https://arxiv.org/abs/2201.06184)

There is a strict-sign version: \(A(x)<0\) for every \(x>2\) if and only if \(S(p)^2/2-W(p)+2<0\) at every selected prime. For the reverse direction choose a point with \(A\ge0\), a preceding negative point (there are such points immediately to the right of 2), and a later negative point, whose existence is unconditional by [the positive xi observation](XI_AREA_ECHO.md). An interior maximum of nonnegative height gives the selected vertex. Formula (1) allows the weaker, cofinal upper and quantifies what its failure would measure.

## The full signed sum on a selected vertex

Set \(\ell_q=\log q\) and \(m_q=S(q)-\ell_q/2\). The adjacent mass intervals \([S(q)-\ell_q,S(q)]\) partition \([0,S(p)]\). Their first moments give the identity
\[
 S(p)^2/2-W(p)+2=2+\sum_{q\le p}\ell_q(m_q-q).
\]
Every earlier ordinary prime contributes. Equivalently this compares the first moments of ordinary length on the mass intervals and the actual weighted prime atoms at their arithmetic locations. The condition \(0<S(p)-p<p^+-p\) controls only the final displacement. Bounding the sum of earlier signed displacements by the terminal gap would require a separate theorem on the prefix.

Working directly at the prime has a controlled cost: \(A(S(p))-A(p)=(S(p)-p)^2/2\le(p^+-p)^2/2\). The unconditional short-interval prime theorem gives \(p^+-p=O(p^{3/5})\), so this correction is \(O(p^{6/5})\), below the \(p^{3/2}\) normalization. It is the accumulated first moment, not interpolation between neighboring primes, that remains to be controlled. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=2)

## An independent bound on the recent prime history at every true stop

At \(z=S(p)\) in its gap, the actual discrepancy \(\vartheta(z)-z\) is **exactly zero**. The signed effect of the entire most recent interval \([z-h,z]\) then has the exact expression
\[
 A(z)-A(z-h)=\frac{h^2}{2}
       -\sum_{z-h<q\le z}(q-z+h)\log q .
\]
This follows by integrating \((z-t)-(\vartheta(z)-\vartheta(t))\). The previously proved two-sided short-interval estimate, now applied with zero linear term at \(z\), gives
\[
 |A(z+v)-A(z)|\ll v^2 e^{-(\log z)^{1/4}/4}+z^{4/3}\log z
 \qquad(|v|\le z/100).
\]
For \(H=z^{3/4}\exp((\log z)^{1/4}/16)\), the uniform error over \(|v|\le H\) is \(o(z^{3/2})\). In particular the recent triangle and its continuum prediction cancel to this order, with *all actual prime terms present*. Every fourth power in this neighborhood therefore agrees with the stopped score up to \(o(z^{3/2})\); it contains at least a constant times \(\exp((\log z)^{1/4}/16)\) consecutive fourth powers. This statement applies at **every** sufficiently large selected prime. Its proof requires neither RH nor a hypothesis that a zero actually attains its supremum. [Arithmetic averaging proof](../step4-strip-2026-11-19/ACTUAL_PRIME_AVERAGING_ERROR.md)

This explicitly pays for a portion of the signed sum at the relevant vertices. Subtracting it leaves the older actual area \(A(z-H)\). Its sign and magnitude on the selected prefixes are still the unbounded arithmetic term.

## Validation scope

The accompanying interval-arithmetic computation checks the exact cut condition and graph sums on a finite prefix. It includes deliberately varied continuum slopes to execute the interior-maximum branch on the same genuine primes. Only slope 1 is the Step 4 input. The asymptotic equality in (1) is a paper deduction, and a direct independent subpower estimate for \(H\) remains open.

Specifically, all 78,498 primes up to one million were examined with their next prime, at 160-bit ball precision. There were zero eligible stops for the true slope. The controls changed the continuum from \(y\) to \(\lambda y\). The four slopes \(19/20,49/50,99/100,199/200\) gave respectively 34, 117, 203 and 377 interior stops. Across them 13 maxima were positive and 718 negative. The direct area, vertex score and preceding-prime-plus-gap formula agreed at every control stop. Those controls exercise the calculation, and supply no late true-prime sign evidence. [Reproducer](check_stopped_primes.py) · [Receipt](STOPPED_PRIME_CHECK.json)

## Falsifying a possible shortcut

Even logarithmic gaps, the logarithmic weight at every atom, and excellent relative prime-number-theorem agreement could coexist in a model with large positive stopping peaks. For fixed \(1/2<\alpha<1\), put \(g(x)=x^\alpha\sin(\log x)\), and for sufficiently large \(x\) choose \(F'(x)=(1+g'(x))/\log x\). Use integer atoms \(q_n=\lceil F^{-1}(n)\rceil\), starting at sufficiently large \(n\), each with weight \(\log q_n\). This is a falsification model, not the ordinary primes. Eventually the atoms are distinct, their gaps are \(O(\log x)\), and their cumulative count is \(F(x)+O(1)\). Partial summation gives their cumulative log mass as \(x+g(x)+O(\log x)\). Consequently their integrated log-mass error is
\[
 \frac{x^{1+\alpha}}{(1+\alpha)^2+1}
   \big[(1+\alpha)\sin(\log x)-\cos(\log x)\big]+O(x\log x).
\]
The peak argument above now forces positive stopping scores of order \(x^{1+\alpha}\) in recurring multiplicative windows. This pinpoints why a small last gap and a closely matched last mass do not by themselves bound the sum of all earlier signed displacements. A proof must use an additional property of the true prime measure.
