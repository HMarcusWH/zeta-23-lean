# What the quiet native prefix determines

**DERIVED on paper.** For the distributed five-moment factorial filter, even one zero integer slope is an exponentially rare phase of the complete period. The \(L^3\) power in its full-period variance is sharp. There are explicit arithmetic calibrations with the same five global moments, allowed size, Möbius inputs, exact zero response through \(L+1\), and identical response to the standard filter through \(2L\), whose native weighted absolute response is bounded below by a positive constant. One such perturbation uses only the five original nodes at each centre. A second preserves all five moments separately at every centre, using one more node. These results isolate the extra information carried by the specific choice of calibration.

Take the factorial filter with \(a_m=-\mu(m)/m\) on \(2\le m\le L\) and \(N\) equally weighted centres \(R\in(2L,3L]\), \(9\mid R\). Its ordinary moment conditions are those in the [factorial source](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md), with \(\sum a_m(m^2-1)=12\) appended. The original five correction nodes are \(4^kR,\ 0\le k\le4\). Write

\[
 f_m(t)=r_m(m-r_m),\quad r_m=t\bmod m,\qquad
 E(t)=-1+\tfrac12\sum a_m f_m(t).
\]

Use uniform integer \(t\) over a complete period, the lcm of the support indices. This construction has \(E(0)=-1\) and \(E(n)=0\) for \(1\le n\le L+1\).

## An exact small-probability estimate for slopes

Every prime \(L/2<p\le L\) occurs at precisely one support index, \(m=p\), with coefficient \(1/p\), for all large \(L\). No other low index is divisible by \(p\). Since \(9\mid R\), divisibility by an odd \(p>3\) would require \(9p\mid R\), impossible here. The same exclusivity holds for the six-node variant below.

At integer times \(f_p(t+1)-f_p(t)=p-1-2r_p\), including the transition \(r_p=p-1\). Condition on all residues modulo the lcm of the other support indices. The contribution of these exclusive primes to \(E(t+1)-E(t)\) is

\[
 \sum_{L/2<p\le L}\left(\frac{p-1}{2p}-\frac{r_p}{p}\right).
\]

By CRT their residues range independently. Modulo one, the slope is uniform on a translate of the \(Q\)-point grid, \(Q=\prod_{L/2<p\le L}p\). Indeed \((r_p)_p\mapsto\sum_p r_p(Q/p)\pmod Q\) is bijective, as reduction modulo each \(p\) shows. Thus the conditional and unconditional probability of **any prescribed exact slope** is at most \(1/Q=\exp[-(1/2+o(1))L]\) by ordinary PNT. Two consecutive zero values already satisfy this rare condition. The polynomial estimates for the proportion of exceptional phases therefore do not give a bound after conditioning on the exact native plateau. [Ordinary PNT](https://dlmf.nist.gov/27.12.E5)

## Sharp exponent in the period variance

For \(g=\gcd(m,n)\), condition on \(t\bmod g\). The finer residues modulo \(m,n\) are conditionally independent and
\(\mathbb E[f_m(t)\mid t\bmod g]=f_g(t)+(m^2-g^2)/6\), by summing an arithmetic progression of residues and their squares. Hence \(180\,\operatorname{Cov}(f_m,f_n)=g^4+10g^2-11\), from the second and fourth power sums. Put \(J_k(d)=d^k\prod_{p\mid d}(1-p^{-k})\). Since \(\sum_{d\mid g}J_k(d)=g^k\), this gives the nonnegative identity

\[
 720\,\operatorname{Var}E
 =\sum_{d\ge2}(J_4(d)+10J_2(d))\left|\sum_{d\mid m}a_m\right|^2 .
\]

For squarefree \(d\in(L/2,L]\) coprime to 6, the only contributing \(m\) divisible by \(d\) is \(d\) itself, by the same \(9d>3L\) argument. There are \(\gg L\) such \(d\). For example inclusion-exclusion with \(\mu^2(n)=\sum_{k^2\mid n}\mu(k)\) gives density \((1/3)\prod_{p\ge5}(1-p^{-2})>0\) with error \(O(\sqrt L)\). Each chosen \(d\) contributes \(\gg d^2\) since \(J_4(d)\ge d^4/\zeta(4)\). Thus \(\operatorname{Var}E\gg L^3\). The distributed bound \(|a_m|\ll\log^2(2L)/m\) gives the upper \(O(L^3\log^4(2L))\) by summing the same identity over \(d\ll L\). This controls integer values under complete-period averaging.

## A native extension using signed arithmetic

There is a limited extension for the original filter. Fix any \(K,A>0\) and set \(H=\lfloor L^{5/6}\log^K L\rfloor\). For large \(L\), \(H<L\); on this range every proper divisor lies at most \(L\), and no calibration has started. Hence exactly \(E(L+h)=\sum_{L<j\le L+h}\mu(j)(L+h-j)\). Write this ramp as \(\int_0^h[M(L+u)-M(L)]\,du\). On \(u<L^{2/3}\) use the trivial bound \(u+1\), and above that cutoff use the all-interval signed Möbius estimate \(O_D(u/\log^D L)\) for arbitrary \(D\). This gives

\[
 \sum_{h\le H}\frac{|E(L+h)|}{(L+h)^3}
 \ll_D L^{-3}\big(H L^{4/3}+H^3/\log^D L\big)
 \ll_{K,A} L^{-1/2}/\log^A L .
\]

Choose \(D>A+3K\) in the last line. This proves a logarithmic enlargement and logarithmic saving at the native threshold, using the actual signed Möbius input. It leaves intervals of any fixed larger power outside the estimate. [Matomäki, Shao, Tao and Teräväinen, Theorem 3.1(i)](https://arxiv.org/pdf/2204.03754#page=35) · [Project audit of the exact short-interval input](../step4-strip-2026-11-19/ROUGH_INTERVAL_CANCELLATION.md)

## Two source-preserving tests of the plateau extrapolation

For an explicit deformation use the polynomial \(b(z)=(z-1)^2(z-2)(z-4)=\sum_{k=0}^4 b_k z^k\). At the five existing nodes of centre \(R\) add the distributed corrections \(t_R b_k\), where

\[
 t_R=N^{-1}\left(1-R\frac{\sum_RR^2}{\sum_RR^3}\right).
\]

Here all sums run over the full centre set. The value, log, square-root and linear moment increments vanish separately at each centre, by the roots at \(1\) (double), \(2\) and \(4\). The quadratic moment increment is \(b(16)\sum_R R^2t_R=0\). Thus the fifth equation is preserved exactly after the averaging. The original individual five-node solution at each centre remains distinguished by the additional per-centre equation. The index set for the deformed filter fits the same period as the original five prescribed nodes and low coefficients, with zero-coefficient indices permitted in that common period. Each high coefficient added is \(O(1/L)\) with bounded index multiplicity. The punctual Möbius inputs, exact moment values and distributed coefficient bounds used for the source reconstruction are all preserved.

For \(0\le n\le2L\), each high-node kernel is still given by \(mn-n^2\). The increment to \(E(n)\) is zero because the constant and linear-in-\(m\) moments of the added coefficients vanish. For integers \(13L/4\le n\le15L/4\), however, one has \(R<n<2R\) and \(n<4R\) for *all* centres. The difference between the wrapped and polynomial values at \(m=R\) is \(2R(n-R)\); the other four nodes still use the polynomial. Consequently

\[
 \Delta E(n)=b_0\sum_Rt_R R(n-R)=b_0 n\sum_Rt_R R,\qquad
 L^{-1}\sum_Rt_R R\longrightarrow
 \frac52-\frac{(19/3)^2}{65/4}=\frac{37}{1170}>0 .
\]

The limits are ordinary Riemann sums on \([2,3]\). Since \(b_0=8\), the increment is positive and \(\gg L^2\) throughout this entire interval.

Alternatively keep **all five** homogeneous equations separately at every centre. Add \(N^{-1}\widetilde b_k\) at the six indices \(4^k R,\ 0\le k\le5\), with \(\sum\widetilde b_kz^k=(z-1)^2(z-2)(z-4)(z-16)\). The extra root sets the quadratic moment to zero separately at each \(R\). The same no-wrap calculation applies through \(2L\). On \([13L/4,15L/4]\) the signed increment is \(\widetilde b_0N^{-1}\sum_RR(n-R)\), of constant sign and magnitude \(\gg L^2\). The new maximum index \(4^5(3L)\) is still a fixed multiple of \(L\).

For either construction \(\sum_{13L/4\le n\le15L/4}|\Delta E(n)|/n^3\gg1\). This interval is contained in \((L,L^{1.01}]\) for all sufficiently large \(L\). Even the triangle inequality on the opposite-sign perturbations gives a fixed sign with native weighted response bounded below on an unbounded sequence.

In fact the ordinary Mertens bound shows that **either** sign works at **every** sufficiently large \(L\). For the uniquely calibrated unperturbed filter, each unaveraged high-node coefficient is \(O_A(\log^{-A} L)\) for every fixed \(A\). To see this, the full low-source sums at the value and logarithmic moments agree with their targets, by \(1/\zeta(1)=0\) interpreted by continuity and \((1/\zeta)'(1)=1\). Partial summation with \(M(u)\ll_B u/\log^B(2u)\) controls their omitted tails by \(O_A(\log^{-A}L)\), including the \(\log R\) term after reducing the logarithmic row by the value row. For each \(\gamma=1/2,1,2\), the other normalized deficit is bounded by constants divided by \(R^\gamma\) and \(R^{-\gamma}|\sum_{m\le L}\mu(m)m^{\gamma-1}|=O_A(\log^{-A}L)\) by another partial summation. The matrix on the fixed five nodes is independent of \(R\) after these scalings.

For \(L\le n<4L\), the original \(E(n)=(n-1)-J(n)\) is the integer ramp of the native residual \(1-\zeta D\), with \(D\) the matched inverse polynomial. The divisor identity \(1-\zeta D=\zeta(1/\zeta-D)\) leaves at most three native tails \(\sum_{L<j\le n/k}\mu(j)(n-kj)\), \(1\le k\le3\). Each costs \(O_A(L^2/\log^A L)\) by the same Mertens bound. The high-node contribution has this bound also, since each active correction weight before an integer ramp is its index times \(O_A(\log^{-A}L)\) before averaging and there are only a bounded number of multiples per centre. Therefore \(E(n)=o(L^2)\) uniformly on the test interval. The deformed native absolute responses there are dominated by the explicit increments, giving the strengthened lower bound. [Unconditional Mertens estimate](https://arxiv.org/abs/2208.06141)

Both deformations satisfy the complete-period bounds and agree exactly with the standard filter through \(2L\). These results use no zero ceiling and concern inference from those structural properties. The sharper arithmetic bound for the specified, undeformed, per-centre five-node solution remains open. No new Lean or CI claim follows.
