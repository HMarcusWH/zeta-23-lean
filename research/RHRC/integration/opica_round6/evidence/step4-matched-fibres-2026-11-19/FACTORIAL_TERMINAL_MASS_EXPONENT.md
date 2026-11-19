# The exact growth exponent of both signs in a terminal band of actual primes

**DERIVED on paper.** Let \(B=\sup_\rho\Re\rho\) for nontrivial zeros of \(\zeta\). We use \(B<1\), supplied here by the [pinned external ceiling](../step4-height-window-2026-11-19/STEP4_HEIGHT_AND_GRAPH_RESULTS.md); symmetry gives \(B\ge1/2\). Fix \(0<\lambda<1\), set \(L=\lfloor x^\lambda\rfloor\), and take the real factorial residual \(K_x(p)\) on ordinary primes described below. For **every fixed \(\delta>0\)**, put

\[
 I_\delta(x)=\{p\text{ prime}:x/L^{1+\delta}<p<x/(L+1)\},\qquad
 M_\pm(x)=\sum_{p\in I_\delta(x)}[\pm K_x(p)]_+\log p .
\]

At all real horizons tending to infinity, separately for the two signs,

\[
 \boxed{\ M_\pm(x)=x^2 L^{B-1+o(1)}\ } .                              \tag{1}
\]

The same exponent holds for the total absolute mass, either on this band or on all \(p<x/(L+1)\). At the original \(\lambda=0.11\), the complete signed sum reconstructs \(A(x)+(2/3)x^{3/2}\) up to \(o(x^{3/2})\), by the prior [power-cutoff calculation](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md). In particular each sign has mass at least \(x^{1.945-o(1)}\), and RH would give the exact exponent 1.945. The proof does not assume that \(B\) is attained. For the broader range of \(\lambda\), (1) concerns the corresponding factorial weights; it does not assert that all those cutoffs reconstruct the area with square-scale error.

## Definitions and two bounds for the moving coefficient polynomial

For integer \(m\ge2\) put \(J_m(y)=\sum_{j\le y}(1-m\mathbf1_{m\mid j})(y-j)\). Keep the [four factorial calibrations](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md):

\[
 \sum a_m=1,\quad \sum a_m\log m=1,\quad
 \sum a_m(1-\sqrt m)=1/\zeta(1/2),\quad \sum a_m(m-1)=2 .
\]

Here \(a_m=-\mu(m)/m\) for \(2\le m\le L\). The other four coefficients occur at \(R,4R,16R,64R\) with \(2L+1\le R\le3L\). The proof works for each such choice and for the [equal-weight distribution over these choices](../step4-area-runs-2026-11-19/BOTH_ROW_ENERGIES.md). Put

\[
 D(s)=\sum a_m(1-m^{1-s}),\quad J(y)=\sum a_m J_m(y),\quad
 K_x(u)=x-u-uJ(x/u)\quad(0<u\le x).
\]

Thus \(D(s)=\sum_{n\le L}\mu(n)n^{-s}-\sum_{m\text{ extra}}ma_m m^{-s}\). The Dirichlet coefficients of \(\zeta(s)D(s)\) agree with those of 1 through index \(L\), so \(K_x(u)=0\) on \([x/(L+1),x]\). Also \(D(1)=0\) and \(D'(1)=1\).

For each fixed \(b>B\), \(1/\zeta(u+it)\ll_{b,\epsilon}(1+|t|)^\epsilon\) uniformly for \(u\ge b\); a proof using Borel–Carathéodory and three circles is in the [earlier note](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md). We take \(B<b<1\). Here is the needed sharp-cutoff version, including height dependence. For real \(t\), apply truncated Perron to \(1/\zeta(z+it)\) with half-integer \(V=\lfloor U\rfloor+1/2\), initial line \(1+1/\log V\), and height \(T=(3+V+|t|)^2\). Its coefficients \(\mu(n)n^{-it}\) have modulus at most 1. The truncation error for \(V\ge 5/2\) is \(O(V\log^2(2V)/T)\): near \(V\) use distance to the nearest integer and the harmonic sum over that distance; outside \([V/2,2V]\) use absolute convergence on the starting line. Shift to \(\Re z=b\). The new vertical is \(O_\eta(V^b T^\eta\log(2T))\), and each horizontal is \(O_\eta(VT^{-1+\eta})\), because \(|\Im(z+it)|\le T+|t|\le2T\). The reciprocal is regular even at the pole of \(\zeta\). Choosing \(\eta\) sufficiently small in terms of the desired epsilon gives

\[
 \sum_{n\le U}\mu(n)n^{-it}\ll_{b,\epsilon} U^{b+\epsilon}(1+|t|)^\epsilon\quad(U\ge2). \tag{2}
\]

The four correction coefficients are \(O_{b,\epsilon}(L^{b-1+\epsilon})\) each before distribution, uniformly in \(R\). At the normalization nodes 1 and its derivative, the tails of \(\sum\mu(n)/n=0\) and \(\sum\mu(n)\log n/n=-1\) are \(O(L^{b-1+\epsilon})\) by (2) at \(t=0\) and partial summation (take a smaller preliminary epsilon). These sums agree with the value and negative derivative of \(1/\zeta\) by convergence from the right. At nodes \(1/2\) and 0 the initial polynomial is \(O(L^{b-u+\epsilon})\) at \(u=1/2,0\). Multiplying the four value equations by their respective \(R^u\) and eliminating \(\log R\) in the derivative equation gives right sides \(O(L^{b+\epsilon})\), including the fixed target values. The fixed inverse matrix for coefficients \(m a_m\) then gives the stated bound on \(a_m\); averaging over \(R\) preserves the summed absolute bound. By (2) and partial summation, on each fixed real line \(u\),

\[
 |D(u+it)|\ll_{u,b,\epsilon} L^{(b-u)_++\epsilon}(1+|t|)^\epsilon .    \tag{3}
\]

The logarithmic borderline is absorbed in epsilon. On a compact strip one can increase epsilon slightly to make the bound uniform. All occurrences of arbitrary epsilon below can first be taken smaller than the final claimed slack.

## Independent upper for the complete absolute mass

Write \(Y=x/p\) and let \(r(j)\) be the coefficients of \(1-\zeta D\). For \(Y>L\), those from the omitted Möbius tail contribute exactly

\[
 \sum_{e\le Y/L}\sum_{L<d\le Y/e}\mu(d)(x-ped).
\]

For each \(e\) the inner sum is \(pe\int_L^{Y/e}(M(v)-M(L))dv\), where \(M(v)=\sum_{d\le v}\mu(d)\). By (2) this costs \(O_{b,\epsilon}(x(Y/e)^{b+\epsilon})\). Summation over \(e\), with \(b+\epsilon<1\), is \(O(xY L^{b-1+\epsilon})\). The correction terms have absolute cost at most \(xY\sum_{m\rm\ extra}|a_m|\), of the same order. Thus, for all eligible primes,

\[
 |K_x(p)|\ll_{b,\epsilon}xY L^{b-1+\epsilon},\qquad
 \sum_{p<x/(L+1)}|K_x(p)|\log p\ll_{b,\epsilon}x^2 L^{b-1+\epsilon}\log(2x). \tag{4}
\]

The final sum uses \(\sum_{p\le x}(\log p)/p\ll\log(2x)\). Taking \(b\downarrow B\) supplies the upper exponent in (1) uniformly in the actual horizon. It bounds the absolute value after any assignment of unit phases to complete outer-prime fibres.

## Sharper control of the deep prefix

The Mellin integrand for \(J(Y)\) is \(\zeta(z)D(z)Y^{1+z}/[z(z+1)]\), initially on \(\Re z=2\). Shift to \(u=-1/2+\eta\) with \(0<\eta<1/4\). The pole at 1 cancels by \(D(1)=0\). At zero the residue is exactly \(Y\), since \(D(0)=-2\) by the fourth calibration and \(\zeta(0)=-1/2\). The functional equation bounds \(\zeta(u+it)\ll_\eta (1+|t|)^{1-\eta}\) at high heights, as the reflected zeta factor is absolutely convergent there. Taking the height epsilon in (3) less than \(\eta/2\) yields absolute convergence after division by \(z(z+1)\). Horizontals vanish by classical convexity or the functional equation throughout the fixed strip and the fact that \(D\) is a finite polynomial for each \(x\). On multiplying by \(p\), the residue cancels the linear \(x\) in \(K_x(p)\). Allowing independent arbitrarily small slacks in \(b-B\) and \(\eta\), and using \(p\le x\), gives for any final \(\epsilon>0\)

\[
 |K_x(p)|\ll_{\lambda,\epsilon}x^{1/2+\epsilon}L^{B+1/2}p^{1/2}.        \tag{5}
\]

The leftover term \(p\) is covered. Consequently the entire unweighted absolute deep-prefix mass at \(p\le x/L^{1+\delta}\) is

\[
 \ll x^{2+\epsilon}L^{B-1-3\delta/2}.                                  \tag{6}
\]

If this cutoff lies below 2 its prime sum is empty. This explicit power saving will allow separation of the two signs on the terminal band itself.

## Detecting the lower exponent with the actual prime measure

Fix a nonreal zero \(\rho=\alpha+i\gamma\) with \(1/2\le\alpha\le B\). We use zeros arbitrarily close to \(B\); when \(B=1/2\) take any critical-line zero. For each fixed \(\alpha\) chosen sufficiently near \(B\), take real \(\sigma>\max(0,\alpha+B-1)\) slightly above its lower endpoint, and \(B<b<1\) sufficiently close to \(B\), such that \(\sigma<\alpha\) and

\[
 \sigma+\lambda(b-\sigma)<\alpha.                                      \tag{7}
\]

This is possible because at the limiting values \(\alpha=b=B\), \(\sigma=2B-1\) the left side is smaller than \(B\) by \((1-B)(1-\lambda)>0\). Let \(P(w)=\sum_p(\log p)p^{-w}\). Mellin inversion on the actual discrete prime sum yields the multiplier \(P(z+1-\rho)[1-\zeta(z)D(z)]x^{1+z}/[z(z+1)]\). Move the line from 2 to \(\sigma\). Throughout the new line, \(\Re(z+1-\rho)>B\ge1/2\), and \(P(w)=-\zeta'(w)/\zeta(w)\) plus an absolutely convergent bounded higher-prime-power series on this region. The only pole crossed is at \(z=\rho\), coming from \(w=1\). There \(1-\zeta(\rho)D(\rho)=1\), independent of the multiplicity of \(\rho\). At \(z=1\) the bracket is regular. On each fixed line a positive distance to the right of \(B\) the logarithmic derivative is \(O_\epsilon(|t|^\epsilon)\) at large heights by Cauchy's formula for a local logarithm. At bounded heights the new line avoids all poles. Together with zeta convexity and (3), this makes the vertical integral absolute and the horizontals vanish. The constants may depend on the chosen zero and lines. Thus (7) proves at every sufficiently late \(x\)

\[
 \sum_{p<x/(L+1)} K_x(p)p^{\rho-1}\log p
 =\frac{x^{1+\rho}}{\rho(1+\rho)}+o_\rho(x^{1+\alpha}).                \tag{8}
\]

For any fixed \(d>(B+1/2)/(\alpha+1/2)\), the twisted absolute mass at \(p\le x/L^d\) is, by (5) and Chebyshev partial summation,

\[
 \ll x^{1+\alpha+\epsilon}L^{B+1/2-d(\alpha+1/2)}=o(x^{1+\alpha})
\]

on choosing the epsilon after \(d\). When \(\alpha\) is close to \(B\) we may take \(1<d<1+\delta\) and \(d<1/\lambda\). On the remaining band \(p^{\alpha-1}\le(x/L^d)^{\alpha-1}\). The modulus of (8) therefore gives

\[
 \sum_{x/L^d<p<x/(L+1)}|K_x(p)|\log p\gg_\rho x^2 L^{-d(1-\alpha)} .      \tag{9}
\]

This band is contained in \(I_\delta(x)\). First take the lower limit as \(x\to\infty\) with all constants fixed; then let actual real parts \(\alpha\) approach \(B\) and \(d\) approach 1 from above while retaining its strict inequality. This yields the lower logarithmic exponent \(B-1\), regardless of attainment of \(B\).

## Why each sign must occur inside the terminal band

For the full **untwisted signed** sum move the same ramp contour with multiplier \(P(z)[1-\zeta(z)D(z)]\) to any fixed \(v>B\), \(v<1\). At 1, \(\zeta(z)D(z)\to D'(1)=1\), so the pole of \(P\) is removable. The new line contains no prime-series pole. Use (3) with \(B<b<v\), the pole-free logarithmic derivative, and the absolutely convergent prime-power correction to obtain \(O(x^{1+B+\epsilon})\) by choosing \(v\) sufficiently close to \(B\). The horizontal and vertical estimates are valid as in (8). At every fixed \(\lambda<1\), the power gap to \(x^2L^{B-1}\) is \((1-B)(1-\lambda)>0\). By (6) the signed sum on the complement of \(I_\delta\) is also smaller by a fixed power. Hence the signed sum on \(I_\delta\) is smaller by a fixed power than its absolute mass from (9). The positive and negative masses are respectively half the sum and half the difference of absolute and signed mass, with the sign chosen accordingly. This completes (1) for both signs.

The exponent measures arithmetic cancellation on true ordinary primes and improves the earlier [one-critical-zero lower bound](TRUE_PRIME_TWIST_AND_BOTH_SIGNS.md). At \(\lambda=0.11\), the available external ceiling gives the independent upper \(M_\pm\ll_\epsilon x^{1.98606806+\epsilon}\). Proving the critical exponent 1.945 as an upper from a different arithmetic input remains open. Neither the exponent identity nor a count of matched labels gives the square-scale signed upper. No new Lean or production qualification is asserted.
