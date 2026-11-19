# A direct upper for positive excess in the large-cofactor complement

**DERIVED on paper.** Work on the actual all-rough node graph restricted to complete terminal shells with \(Z=X^\kappa\), \(0<\kappa<.01\). Decompose a true charge \(f_J=A_J+R_J\), where \(A_J\) contains every squarefree rough \(q\in J\) with \(q/P^+(q)\le Z\) and \(R_J\) is its deterministic complement. For every fixed \(\delta>0\), every such node of width \(H\ge U^{7/12+\delta}\) in a shell \([U,2U)\) has \(A_J>0\) and \(R_J<0\) at every sufficiently large \(X\). On the entire tree of these complete shells,
\[
     \sum_J w_J [R_J]_+^2
       \ll_{\epsilon,\kappa}
       X^{\max(0,\,\min(1/6,\,2B-17/12))+\epsilon},
       \qquad B=\sup_\rho\Re\rho .
\]
For every \(B>1/2\) this is strictly below the full one-sided detector exponent \(2B-1\). For \(B\le17/24\) the complementary positive energy already has a subpower bound. The estimate includes all depths and all genuine signs on its stated domain. [One-sided full-shell detector](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

To see the signs, put \(P_y=\prod_{p\le y}(1-1/p)^{-1}\), \(y=\lceil\log_2X\rceil^2\), and use the genuine signed density
\[
 d(J)=-\sum_{a\le Z}\frac{\mu_y(a)}a\int_J\frac{du}{\log(u/a)} .
\]
The uniform signed reciprocal expansion from the cone calculation gives \(d(J)=(1+o(1))HP_y/\log^2 U>0\) for all nonempty intervals, uniformly here since \(\log U\asymp\log X\). [Exact derivative calculation](../step4-prime-transport-2026-11-19/CONE_DRIFT.md)

For \(H\ge U^{7/12+\delta}\) every scaled interval \(J/a\), \(a\le Z\), is eligible for the all-interval ordinary prime number theorem. Indeed \(\log a/\log U\le .01/.99+o(1)\), and
\[
 \frac{7/12-.01/.99}{1-.01/.99}>17/30.
\]
The ratio \((7/12-\alpha)/(1-\alpha)\) decreases in \(\alpha\). Thus there is fixed room above \(17/30\) in the scale \(U/a\). Subdivide longer intervals into equal pieces whose lengths have a fixed exponent strictly between \(17/30\) and the lower available exponent; choose enough pieces to meet the upper \(0.99\) exponent of the prime theorem as well. Its prime-count error per piece of length \(h\) is \(O(h\exp(-c\log^{1/4}(U/a)))\); replacing \(h/\log x\) by the integral of \(1/\log t\) over that piece costs \(O(h^2/(x\log^2x))\), smaller than any fixed log-power relative error. Add the disjoint pieces and then the cofactor errors in absolute value, costing \(\sum_{a\le Z}1/a\ll\log U\). Half-open endpoints cost \(O(Z)\) overall if necessary. This proves \(A_J=d(J)+O_{K,\delta,\kappa}(H/\log^K U)\) for every fixed \(K\). [Guth–Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552)

The all-interval rough Möbius bound gives \(f_J=O_{K,\delta}(H/\log^K U)\) on these same nodes. Therefore \(R_J=f_J-A_J=-(1+o(1))HP_y/\log^2U\), while \(A_J\) has the opposite sign. This estimates the signed charge in each actual long node and removes every positive-part contribution from the complement there. [Earlier all-interval rough count and repeated-factor convolution](../step4-strip-2026-11-19/ROUGH_INTERVAL_CANCELLATION.md)

For the smaller widths put \(\lambda=7/12+\delta<1\), taking \(\delta\) arbitrarily small. On a common shell and depth the earlier centered disjoint-interval result gives
\[
  \sum_J|R_J+d(J)|^2
  \le 2\sum_J |f_J|^2+2\sum_J|A_J-d(J)|^2
  \ll_{\epsilon,\kappa} X^\epsilon U^{2B}.
\]
Since \(d(J)>0\), \([R_J]_+\le |R_J+d(J)|\). The weight is \(H/(UH_0)\), \(H_0=U2^{-s}\). For \(H<U^\lambda\), multiplication by this weight saves \(U^{2-\lambda-o(1)}\) against the unweighted square bound. The alternative elementary count at that level is \(\sum_Jw_J[R_J]_+^2\le H^2/H_0\le U^{2\lambda-1+o(1)}\). Sum over logarithmically many shells and depths, send \(\delta\) to zero within the target epsilon, and use \(U\le X\) when the exponent is positive. This proves the displayed bound. In particular the result covers the complete native graph on aligned cutoffs \(X=2^{100t}\) since omitted endpoint powers of two have zero rough sign. [Centered cone and complete rough interval norms](../step4-prime-transport-2026-11-19/CENTERED_CONE_INTERVALS.md)

This resolves a genuine one-sided sector of the arithmetic. The negative part of \(R_J\) is large and combines with the positive cone charge in \(f_J\). Neither this estimate nor the sign calculation bounds their positive signed difference to the requested scale. The full Step 4 bound remains **OPEN**.
