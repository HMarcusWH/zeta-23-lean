# An actual negative cross term in the rough divisor graph

**DERIVED on paper, 19 November 2026.** On sufficiently long intervals the rough squarefree composites, with all their Möbius signs, compensate the ordinary primes to every fixed inverse power of the logarithm. This yields a negative signed contribution from both directions of the prime-to-composite edges. For the signed native weights the result is an absolute error bound that retains the actual complex phase.

Use the cutoff \(Q_n=n^{2+o(1)}\), \(e^{cn}\le x\le e^n\), and \(I=(x,x+H]\), where \(c>0\) and \(7/12<\lambda<1\) are fixed, \(x^\lambda\le H\le x\). Put \(P_I=\pi(x+H)-\pi(x)\), and let \(C_I\) be the sum of \(\mu(r)\) over **all rough squarefree composites** in \(I\). Since \(x>Q_n\) eventually, every prime in \(I\) is eligible. Thus
\[
 C_I-P_I=\sum_{\substack{r\in I\\p\mid r\Rightarrow p>Q_n}}\mu(r)
     =O_{A,c,\lambda}(H/\log^A x)\quad\text{for every fixed }A>0.
\]
The ordinary prime number theorem in short intervals gives \(P_I\sim H/\log x\) uniformly on this range (partition longer intervals into admissible lengths if necessary). In particular the signed **composite sector itself is positive** on every such sufficiently late interval, with \(C_I/P_I=1+O_{A,c,\lambda}(\log^{-A}x)\) for any fixed \(A\), increasing the exponent of the input estimate by one. [Rough convolution bound and its proof](ROUGH_INTERVAL_CANCELLATION.md) · [Guth and Maynard, Corollary 1.3](https://arxiv.org/abs/2405.20552)

For unit weights the graph contains all ordered prime–composite and composite–prime pairs. Their total signed weight is exactly \(-2P_I C_I\), so
\[
 -2P_I C_I=-2P_I^2+O_A(H^2/\log^{A+1}x)
          \sim -2(H/\log x)^2 .
\]
The retained prime–prime and composite–composite sums are \(P_I^2\) and \(C_I^2\), including their diagonals. The complete cell square is \((C_I-P_I)^2\). The negative asymptotic is an actual arithmetic restriction. It follows from cancellation of the full Möbius sequence on the same interval, without conditioning on RH.

## The actual source weights

Take one small-prime color \(s\), and use the weight \(w(k)=k^{-1/2}V(t-\log(sk))\) in its variable \(k\). The same calculation applies to a projected \(h_n(\log(sk))\) with uniformly bounded value and first derivative. The common factor \(\mu(s)/\sqrt{s}\) can be restored exactly. For a complex profile put
\[
 U=-\sum_{p\in I}w(p),\qquad
 W=\sum_{\substack{r\in I,\ r\ {\rm rough}\\r\ {\rm squarefree\ composite}}}\mu(r)w(r).
\]
The supremum of \(|w|\) plus its total variation on \(I\) is \(O_V(x^{-1/2})\) by differentiation. For every prefix of \(I\) of length \(h\ge x^{\lambda'}\), \(7/12<\lambda'<\lambda\), the actual rough signed count is \(O_{A}(H/\log^A x)\) by the cited bound; on shorter prefixes use \(x^{\lambda'}+1=o(H/\log^A x)\). Abel summation then gives, on the **same cell**,
\[
 |U+W|\ll_{V,A,c,\lambda} H/(\sqrt{x}\log^A x),\qquad
 |U|\ll_{V,c,\lambda}H/(\sqrt{x}\log x).
\]
Consequently the signed cross term satisfies
\[
 \left|2\Re(U\overline W)+2|U|^2\right|
 \le 2|U|\,|U+W|
 \ll_{V,A,c,\lambda} H^2/(x\log^{A+1}x).
\]
This holds with either orientation included and permits \(U=0\). In particular if \(|U|\) exceeds the bound for \(|U+W|\), the cross term is strictly negative. In the colored graph each side of the cross-term comparison is multiplied by \(1/s\) when the two factors \(\mu(s)/\sqrt{s}\) are restored. The additional graph factor \(\sqrt{s}\), when used, multiplies both sides again. These are bounds on exact cell sums. Averaging over a translated partition is legitimate on the cells that satisfy the length and scale hypotheses; a clipped short boundary cell requires its separate prefix estimate.

For the native width \(H=x(\exp(1/B_n)-1)\), \(B_n=\exp(n/\log(n+2))\), and \(\log x\asymp n\), this gives \(|U+W|\ll_A\sqrt{x}/(B_n(\log x)^A)\). It still allows exponential growth in \(n\). The unresolved quantity is the small **difference** between two large, now quantitatively matched signed sectors. At accessible finite scales the graph can contain very few rough composites; the asymptotic claim is only for the specified coupling of \(Q_n,x,H\), with fixed parameters and sufficiently large \(n\). [Complete graph and its critical normalization](LOG_RATIO_STRIP.md)

At the actual fixed cutoff \(10^7\), the tested interval just before the first eligible squarefree composite contains 1,499 primes and zero eligible composites, so its cross term is exactly zero. The adjacent interval beginning with that composite contains 1,533 primes and the one positive composite, making the ordered cross term exactly \(-3{,}066\). These intervals of about 50,000 integers near \(10^{14}\) are too short for the asymptotic theorem. They test the signs, both edge orientations, and the point where the composite sector first appears. [Actual interval counts](FIRST_ROUGH_COMPOSITE.json) · [Independent convolution and cutoff controls](ROUGH_CONVOLUTION_CHECKS.json)
