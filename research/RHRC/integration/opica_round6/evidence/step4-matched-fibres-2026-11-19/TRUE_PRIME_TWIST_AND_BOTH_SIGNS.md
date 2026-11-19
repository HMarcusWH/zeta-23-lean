# Forced signed cancellation on a band of actual ordinary primes

**DERIVED on paper.** The older-prime reconstruction from the [factorial localization](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) contains nearly quadratic positive and negative masses on a single moving band, even though its signed total is much smaller. This holds on the genuine ordinary primes at every sufficiently large real horizon, including stopped primorials. It follows by testing the exact reconstruction weights with the phase of one known critical-line zero, then estimating that test on the actual prime source.

For a positive parameter \(L\) taken to be an integer, use exactly the factorial coefficients \(a_m\) and weight \(K_x(u)\) in that earlier note. Define

\[
 U=\frac{x}{L+1},\qquad U_0=\frac{x}{L^{4/3}\log^2(2L)},\qquad
 M_*(x,L)=\frac{x^2}{L^{2/3}\log(2L)} .                               \tag{1}
\]

With \(L=\lfloor\exp(\kappa\sqrt{\log x})\rfloor\) and a sufficiently small fixed \(\kappa>0\), the following hold **unconditionally** for all large \(x\):

\[
 \begin{aligned}
 \sum_{U_0<p<U}[K_x(p)]_+\log p&\gg M_*(x,L),\\
 \sum_{U_0<p<U}[-K_x(p)]_+\log p&\gg M_*(x,L),\\
 \left|\sum_{U_0<p<U} K_x(p)\log p\right|&=o(M_*(x,L)).                \tag{2}
 \end{aligned}
\]

Each of the first two quantities is thus at least \(x^{2-o(1)}\). The bounds also hold for the fixed power cutoff \(L=\lfloor x^{0.11}\rfloor\) using the project's supplied external zero ceiling \(r=0.873346\). Then each mass is \(\gg x^{1.926666\ldots}/\log x\), on summation primes ranging from order \(x^{0.853333\ldots}/\log^2 x\) to order \(x^{0.89}\). Equation (2) quantifies cancellation; its signed upper is much larger than the Step 4 scale.

## The exact continuum moment survives every factorial dilation

Fix one nonreal critical-line zeta zero \(\rho=1/2+i\gamma\). Its existence suffices; the argument needs no zero off the line and permits multiplicities. For \(0<u\le x\) the real weight and its support are

\[
 K_x(u)=x-u-uJ(x/u)=u\left[-1+\frac12\sum_m a_m d_m(x/u)\right],\qquad
 K_x(u)=0\quad(U\le u\le x).
\]

Here \(J=\sum a_m J_m\), \(d_m\) is the continuous periodic factorial weight with \(|d_m|\le m^2/4\) and \(|d_m'|\le m\) almost everywhere. The four normalization conditions include \(\sum a_m=1\) and \(\sum a_m(m-1)=2\). The earlier proof gives \(\sum |a_m|m^v\ll_v L^v\log^2(2L)\) for fixed \(v>0\). In particular

\[
 |K_x(u)|\ll u L^2\log^2(2L),\qquad
 |K'_x(u)|\ll [L^2+(x/u)L]\log^2(2L)                                  \tag{3}
\]

almost everywhere on any compact subinterval of \((0,x]\). The derivatives can be integrated there because the functions are piecewise linear or continuously differentiable between finitely many breakpoints.

Write \(D(s)=\sum a_m(1-m^{1-s})\). For \(\Re s>0\), the [factorial Mellin identity](../step4-area-runs-2026-11-19/FACTORIAL_PRIME_PROJECTIONS.md) gives

\[
 \int_0^U K_x(u)u^{s-1}du=\frac{x^{1+s}}{s(s+1)}[1-\zeta(s)D(s)].       \tag{4}
\]

This follows by scaling the full continuum ramp and subtracting the projected ramp. The apparent pole at 1 in \(\zeta(s)D(s)\) is removable since \(D(1)=0\). At \(s=\rho\), the right side of (4) is \(x^{1+\rho}/[\rho(1+\rho)]\), whose modulus is a fixed nonzero multiple of \(x^{3/2}\) at every \(x\). The complex twist serves to prevent cancellation of its own oscillatory phase in measuring this lower bound. One may choose any of the rigorously verified critical-line zeros. [Platt and Trudgian](https://arxiv.org/abs/2004.09765)

## Discrete transfer for the unconditional subpower cutoff

Set \(f(u)=K_x(u)u^{\rho-1}\). We prove

\[
 \sum_{p<U}K_x(p)\log p\,p^{\rho-1}
 =\frac{x^{1+\rho}}{\rho(1+\rho)}+o(x^{3/2}).                           \tag{5}
\]

Take a fixed \(c>0\) with \(|\vartheta(t)-t|\ll t\exp(-c\sqrt{\log t})\) for \(t\ge2\), and \(0<\kappa<c/8\). The continuum and absolute prime sums below \(\sqrt x\) are both \(O_\rho(L^2\log^2(2L)x^{3/4})\) by (3), Chebyshev's upper bound and partial summation. Above \(\sqrt x\), compare \(d\vartheta(u)\) against \(du\) by Stieltjes integration by parts. The upper boundary vanishes since \(K_x(U)=0\). The lower boundary costs \(O_\rho(L^2\log^2(2L)x^{3/4})\). From (3),

\[
 |f'(u)|\ll_\rho\log^2(2L)[L^2u^{-1/2}+Lx u^{-3/2}].
\]

Thus the interior error is

\[
 \ll_\rho \log^2(2L)e^{-c\sqrt{(\log x)/2}}[L^2U^{3/2}+LxU^{1/2}]
 \ll_\rho x^{3/2}L^{1/2}\log^2(2L)e^{-c\sqrt{(\log x)/2}}=o(x^{3/2}).
\]

This proves (5) by (4). It uses the actual prime measure on the entire stated support. At a prime endpoint include it on one side only; the closed lower prefix and the open upper remainder yield the same Stieltjes bounds. [Fiori, Kadiri and Swidinsky](https://arxiv.org/abs/2206.12557)

## From the observed phase to both signs on the same band

The total twisted absolute mass at \(p\le U_0\) is \(O(L^2\log^2(2L) U_0^{3/2})=O(x^{3/2}/\log(2L))\), using (3). Thus (5) forces the modulus of the complex sum restricted to \(U_0<p<U\) to exceed a fixed multiple of \(x^{3/2}\). Since \(|p^{\rho-1}|=p^{-1/2}<U_0^{-1/2}\) on this band, its **unweighted** absolute mass satisfies

\[
 \sum_{U_0<p<U}|K_x(p)|\log p\gg_\rho x^{3/2}\sqrt{U_0}=M_*(x,L).
\]

The smaller unweighted prefix is \(O(L^2\log^2(2L)U_0^2)=O(M_*(x,L)/\log(2L))\) in absolute value. Meanwhile the full signed sum is \(A(x)+(2/3)x^{3/2}+o(x^{3/2})\) by the earlier unconditional factorial localization, before its optional low-prime truncation. Integrating the same effective PNT and splitting at \(\sqrt x\) gives \(|A(x)|\ll x^2\exp[-(c/\sqrt2)\sqrt{\log x}]+O(x)\). As \(\kappa<c/8\), this signed total is \(o(M_*(x,L))\). Subtract the smaller prefix to obtain the last line of (2). Adding and subtracting this signed sum from the absolute mass proves the other two lines on the same band.

## Fixed power cutoff with the supplied external ceiling

Here use the unmodified \(L=\lfloor x^{0.11}\rfloor\) factorial coefficients. The Mellin multiplier of the true discrete twisted sum in (5) is

\[
 P(s+1-\rho)[1-\zeta(s)D(s)]\frac{x^{1+s}}{s(s+1)},\qquad
 P(w)=\sum_p(\log p)p^{-w}=-\sum_{k\ge1}\mu(k)\zeta'(kw)/\zeta(kw).
\]

This is exact on \(\Re s=2\), by Mellin inversion of each ramp. Move to \(\Re s=0.39\); then \(\Re(s+1-\rho)=0.89> r\). All \(k\ge2\) terms converge absolutely there. The sole pole of the principal logarithmic derivative crossed in this shift is at \(s=\rho\), with residue +1 for \(P(s+1-\rho)\). Since \(\zeta(\rho)=0\), the multiplier in square brackets has value exactly 1 at that point. The pole at \(s=1\) in \(\zeta(s)D(s)\) is removable. At sufficiently high imaginary parts the logarithmic derivative is \(O_\epsilon((1+|t|)^\epsilon)\) by applying Cauchy's estimate to the zero-free \(\log\zeta\) on a fixed smaller disk above \(r\). The nearby finite-height segment of the new line avoids every pole. [Pinned tracker input and analytic transfer](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)

On the new line, \(|D|\ll L^{0.61}\log^2(2L)\) by the coefficient bound, and \(\zeta(0.39+it)\ll_\epsilon (1+|t|)^{0.305+\epsilon}\) by convexity. The denominator makes the vertical integral absolutely convergent. The horizontals tend to zero with the same vertical-growth bounds uniformly across the strip at high heights. Thus (5) holds with error \(O_\rho(x^{1.39}L^{0.61}\log^2(2L))=O_\rho(x^{1.46})\). The native signed total is \(O(x^{1.874})\) from \(\vartheta(u)-u\ll u^{0.874}\) and the earlier power-cutoff identity. Since \(1.874<2-(2/3)(0.11)=1.926666\ldots\), this again is \(o(M_*(x,L))\). The previous band argument applies without alteration.

These are paper deductions on the actual ordinary primes. The diagnostic forces two large opposite contributions within a specified old band and controls their relative imbalance. The source-specific upper needed for the full signed residual at the square-root scale remains OPEN.
