# A finite unweighted sign range from a positive average in logarithmic scale

**DERIVED on paper, 19 November 2026.** Let \(A_\vartheta(x)=\int_2^x(\vartheta(t)-t)\,dt\), with \(\vartheta(t)=\sum_{p\le t}\log p\). Then
\[
 A_\vartheta(x)<0 \quad (2<x\le 1.21\cdot10^{48}).
\]
More precisely \(A_\vartheta(x)<-0.056x^{3/2}\) for \(10^{19}\le x\le10^{48}\) and \(A_\vartheta(x)<-0.002x^{3/2}\) for \(10^{19}\le x\le1.21\cdot10^{48}\). These finite-range deductions use a published, unconditional finite-height zero verification. The argument covers every real \(x\) in the range and supplies no sign beyond its cutoff.

**Finite-height version.** If all nontrivial zeta zeros of height \(|\gamma|\le H\) lie on the critical line and \(H\ge10^{12}\), the same two margins apply from \(10^{19}\) through \(H^4/81\) and \((11/90)^2 H^4\), respectively. Take \(H=3\cdot10^{12}\) for the numerical statements. Johnston's Lemma 2.1, from Büthe, supplies \(\vartheta(t)<t\) up to \(10^{19}\). His Theorem 1.2 makes the unrestricted unweighted sign equivalent to RH. His unconditional all-range Theorem 1.3 uses the weight \(t^{-2}\). Axler's Theorem 1.7 gives a sharper unweighted comparison under RH. The finite-range estimate here follows below from their inputs and is a paper deduction; I did not locate a publication stating precisely this cutoff. [Finite-height verification](https://doi.org/10.1112/blms.12460) · [Johnston, Theorems 1.2–1.4 and Lemma 2.1](https://arxiv.org/pdf/2201.06184#page=2) · [Axler, Theorem 1.7](https://arxiv.org/pdf/2203.09290#page=5)

## A positive average which majorizes the actual prime-power primitive

Put \(\Psi_1(x)=\sum_{n\ge2}(x-n)_+\Lambda(n)\). Each summand is convex, and \(\Psi_1(x)=\int_2^x\psi(t)\,dt\) for \(x\ge2\). For any bounded positive random variable \(Q\) with \(\mathbb E Q=1\),
\[
 \Psi_1(x)\le\mathbb E\Psi_1(xQ).
\]
This one-sided inequality is the step that recovers an upper for the original, unsmoothed primitive. A sign established only for an averaged error would not give this conclusion without paying for the averaged quadratic main term.

Use **angular** Fourier frequency, with \(G(y)=\int_\mathbb R g(u)e^{iyu}\,du\), and set
\[
 g(u)={\bf1}_{|u|\le1/2}\cos(\pi u),\qquad
 G(y)=\frac{2\pi\cos(y/2)}{\pi^2-y^2},\qquad f(y)=|G(y)|^2/\pi .
\]
The expression for \(G\) is understood by continuity at \(\pm\pi\). Plancherel gives \(\int f=2\int g^2=1\) and \(\int y^2 f(y)\,dy=2\int |g'|^2=\pi^2\), since \(g\) vanishes at its support endpoints. Moreover
\[
 \int f(y)e^{ivy}\,dy=2\int g(u)g(u+v)\,du=0 \qquad (|v|>1).
\]
The transform and its first two derivatives are continuous because \(y^2 f\) is integrable. Thus the integrals with factors \(1,y,y^2\) all vanish at every \(|v|>1\), and by continuity at the endpoints as well. For \(|y|\ge 7\), the formula for \(G\) gives \(f(y)\le(64\pi/9)|y|^{-4}<24|y|^{-4}\).

Take \(D=H/1000\), \(Z=\int_{-D}^D f(y)\,dy\), and let \(U\) have density \(f{\bf1}_{[-D,D]}/Z\). Then \(1-Z\le16/D^3\). With \(V=U/H,\ m=\mathbb E e^V,\ Q=e^V/m\), symmetry gives \(m\ge1\) and \(|V|\le0.001\). Thus \(Q\) has mean one and \(xQ>2\) throughout the claimed large-\(x\) range. The extra quadratic main term after averaging satisfies
\[
 \frac{x^2}{2}(\mathbb E Q^2-1)
 =\frac{x^2}{2m^2}\operatorname{Var}(e^V)
 \le\frac{x^2}{2}e^{0.002}\mathbb E V^2
 \le \frac{1.0021\pi^2}{2}\frac{x^2}{H^2}.                    \tag{1}
\]
Here \(|e^V-1|\le e^{0.001}|V|\) and \(e^{0.002}/Z<1.0021\).

## The low zeros and the entire high tail

The integrated explicit formula at \(r>2\) has quadratic main term \(r^2/2\), zero terms \(-r^{1+\rho}/(\rho(1+\rho))\), and remainder
\[
 -r\log(2\pi)+(\zeta'/\zeta)(-1)
 -\sum_{k\ge1}\frac{r^{1-2k}}{2k(2k-1)}.
\]
This remainder is less than 4. Indeed the functional equation gives \((\zeta'/\zeta)(-1)=\log(2\pi)-(1-\gamma_E)-(\zeta'/\zeta)(2)<4\), using \(\sum_{n\ge2}\Lambda(n)n^{-2}\le\sum_{n\ge2}n^{-3/2}<2\). The zero sum is absolutely convergent uniformly on the bounded interval of \(r=xQ\) for each \(x\). The published two-sided ordinate sum with multiplicities is \(\sum_\rho |\gamma|^{-2}<0.04621\), independent of RH. Each denominator has modulus at least \(\gamma^2\). [Johnston's statement of the integrated formula](https://arxiv.org/pdf/2201.06184#page=4) · [Brent, Platt and Trudgian, Corollary 1, positive ordinates](https://arxiv.org/pdf/2009.13791#page=9)

For \(|\gamma|\le H\), finite verification gives \(\beta=\Re\rho=1/2\). Then \(|\mathbb E Q^{1+\rho}|\le e^{0.0015}<1.0016\). Together these zeros cost less than \(0.04621\cdot1.0016\,x^{3/2}\). Zeros exactly at the limit \(H\) are included here.

For \(|\gamma|>H\), set \(\lambda=1+\beta\in[1,2]\), \(v=\gamma/H\). The multiplier is
\[
 \mathbb E Q^{1+\rho}
 =\frac{m^{-1-\rho}}{Z}
    \int_{-D}^D f(y)e^{ivy}e^{\lambda y/H}\,dy .
\]
The degree-two Taylor polynomial \(p_2(y)=1+\lambda y/H+(\lambda y/H)^2/2\) integrates to zero against \(f(y)e^{ivy}\) on the **whole** real line. We pay both truncation and Taylor error. First,
\[
 \int_{|y|>D}f(y)|p_2(y)|\,dy
 \le16/D^3+48/(HD^2)+96/(H^2 D).
\]
Second, \(\int_{-D}^D |y|^3 f(y)\,dy\le343+48\log H\), by splitting at 7. Hence the inner Taylor remainder costs at most \(8 e^{0.002}(343+48\log H)/(6H^3)\). Combining, using \(|m^{-1-\rho}|\le1\) and \(1-Z\le16/D^3\), gives the uniform bound
\[
 |\mathbb E Q^{1+\rho}|
 \le \frac{1.7\cdot 10^{10}+100\log H}{H^3}.
\]
No critical-line or spacing hypothesis is used for these zeros. After division by \(x^{3/2}\), their full contribution is at most
\[
 0.04621\,\frac{\sqrt{x}}{H^2}
       \frac{1.7\cdot10^{10}+100\log H}{H}.                     \tag{2}
\]
In particular no sign cancellation among their contributions has been assumed.

## Restoring all prime powers and checking the margin

Johnston's unconditional Lemma 2.3 gives \(\psi(t)-\vartheta(t)>0.98\sqrt t\) for \(t\ge121\); at earlier \(t\) this difference is nonnegative. Combining the explicit formula, the convex majorant and the paid proper-prime-power bias gives, for \(u=\sqrt x/H^2\) and \(x\ge10^{19}\),
\[
 \frac{A_\vartheta(x)}{x^{3/2}}
 < \frac{900}{x^{3/2}}+
 \frac{1.0021\pi^2}{2}u +0.04621\cdot1.0016
 +0.04621\,u\,\frac{1.7\cdot10^{10}+100\log H}{H}
 -\frac{2(0.98)}3.                                             \tag{3}
\]
The finite constant covers \(2\) from \(\int_2^x t\,dt\), the upper \(4\) on the linear, constant and trivial-zero terms of the explicit formula, and \((2/3)(0.98)121^{3/2}\) from the lower endpoint of the bias estimate. Formula (3) uses the actual prime powers through the von Mangoldt primitive and their true difference from the ordinary primes. [Johnston, Lemma 2.3](https://arxiv.org/pdf/2201.06184#page=3)

For all \(H\ge10^{12}\), both \(1/H\) and \(\log(H)/H\) decrease. Using \(\pi<22/7\), \(\log(10^{12})<28\), the right side of (3) is below \(-0.056\) at \(u=1/9\) and below \(-0.002\) at \(u=11/90\). Smaller \(u\) gives at least these margins when using the same uniform bound \(900/x^{3/2}<900/10^{28}\). The [exact rational checker](check_bandlimited_theta.py) verifies the bounds on normalization, tails and both margins. It reads the finite-height theorem and ordinate-sum theorem as mathematical inputs; it certifies the numerical inequalities in this deduction. No new Lean compilation or production CI was run.

For a fixed finite \(H\) the Jensen term grows with \(\sqrt{x}/H^2\). The proof gives a finite prefix of length proportional to \(H^4\), not an arbitrarily late sequence. **Step 4 and RH remain OPEN.**
