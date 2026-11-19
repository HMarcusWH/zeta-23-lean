# A necessary large-prime correction for external partners

**DERIVED on paper, unconditionally.** Removing every polynomial-cofactor target together with opposite signs from larger cofactors creates a positive common-prime correction of size at least \(X^{\kappa-o(1)}\). This shows why that correction cannot be dropped from the comparator in [POLYNOMIAL_COFACTOR_AUDIT.md](POLYNOMIAL_COFACTOR_AUDIT.md). The internal-retention construction in [SPARSE_COMPENSATION.md](SPARSE_COMPENSATION.md) avoids this fixed-power obstruction.

Take the same aligned cutoffs \(X=2^{100t}\), the final shell \([U,2U)\), \(U=X/2\), \(A=X^\kappa\), \(M=X^\alpha\), \(0<\kappa<\alpha<.01\), \(y=\lceil\log_2X\rceil^2\), and \(P_y=\prod_{p\le y}(1-1/p)^{-1}\). Let \(G\) be the full rough graph, \(T=\{n:n/P^+(n)\le A\}\) its target cone, and \(V\) the external matched partners with \(A<n/P^+(n)\le M\). Write \(R=G\setminus(T\cup V)\). Only the complete removal of \(T\), the stated cofactor restriction, and charge balance within the shell are used in the following lower bound; the choice among eligible partners can be arbitrary.

By [the full arithmetic drift](CONE_DRIFT.md), with the actual squarefree signs,
\[
 \sum_{n\in V\cap[U,2U)}\mu_y(n)
 =-\sum_{n\in T\cap[U,2U)}\mu_y(n)
 =-(1+o(1))P_yU/(\log U)^2.                                      \tag{1}
\]
Every one of these partners has its unique largest prime in
\(\mathcal P=[U/M,2U/A]\).
Before their removal the whole \(G\setminus T\) sector with largest prime in \(\mathcal P\) has signed shell charge \(O_K(U/\log^K U)\) for each fixed \(K\). Indeed for each \(p\in\mathcal P\) the cofactor \(m\) ranges over \([U/p,2U/p)\cap(A,\infty)\). It is below \(2M<p\). Its sign after multiplication by \(p\) is \(-\mu_y(m)\). Put \(W=U/p\ge A/2\). Each nonempty interval sum is \(O_{K'}(W P_y/\log^{K'} U)\), applying the unconditional rough Mertens estimate of [CONE_DRIFT.md](CONE_DRIFT.md) at the clipped endpoints between \(W\) and \(2W\), where \(\log W\gg_\kappa\log U\). Its smooth-number tail is smaller than every fixed inverse log power uniformly in this range. Sum over the indicated primes using \(\sum W\le U\sum_{p\le2U}1/p\ll U\log(2U)\) and take \(K'\) sufficiently large. Subtract (1). The remaining \(R\)-charge with prime in \(\mathcal P\) is positive and equals
\[
                  (1+o(1))P_yU/(\log U)^2.                         \tag{2}
\]

Let \(D(R)\) be the total signed ordered off-diagonal correction in the polynomial-cofactor audit. In each shell it includes every pair sharing a prime \(p\ge U/M\). This prime is unique and always rejected by the native GCD test. Each correction is the sum of the actual \(p\)-fibre charge squares less its diagonal. Summed with the original weights, all diagonals cost \(O(\log X)\). Every square is nonnegative, so retain just the base nodes of the final shell and \(p\in\mathcal P\). Cauchy on at most \(2^s(2U/A)\) such base-prime sites, with \(s=\lceil\sqrt{\log_2 X}\rceil\) on aligned cutoffs, and (2) yield
\[
 D(R)\ \gg\ \frac{A P_y^2}{2^s(\log U)^4}-O(\log X)
          \ \ge\ X^{\kappa-o(1)} .                                \tag{3}
\]
This uses a positive square lower on the combined fibre statistic, with the entire signed diagonal correction accounted for. It does not assume a sign for any single off-diagonal pair.

Write \(b=B-\tfrac12\) as before. If \(2b<\kappa\), the corrected comparator \(C(R)+D(R)\) is \(O_\epsilon(X^{2b+\epsilon})\) on every sufficiently late aligned cutoff. Therefore the uncorrected primitive covariance satisfies
\[
                         C(R)\le -X^{\kappa-o(1)}.                 \tag{4}
\]
In particular, a cofinal one-sided subpower upper on this external-partner primitive covariance would hold even in the presence of a hypothetical sufficiently small positive displacement. It cannot distinguish those possibilities by this route. This conclusion concerns the external-partner selector only.

For comparison, the internal selector leaves \(L\) in the target cone and removes only charge-balanced matches. Its shell charge equals that of \(T\); its cardinality is at least \((1-o(1))P_yU/(\log U)^2\). Every label in \(L\) has cofactor \(2^{2s}<m\le X^{\tau(X)}\) with \(\tau(X)\to0\). Its shared-prime fibres are disjoint from the \(m>A\) labels in the same shell once \(2X^{\tau(X)}<A\). Across at most \(2^s(2U/2^{2s})\) final-shell base-prime sites one thus obtains a lower \(\gg 2^s P_y^2/(\log U)^4-O(\log X)\) on the signed correction from the \(L\)-fibres. It exceeds every fixed power of \(\log X\) while remaining within the subpower allowance of the internal construction. No asymptotic upper that closes Step 4 is supplied by this lower bound.
