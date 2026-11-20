# Paying sparse prime-factor collisions inside the original signed matching

**DERIVED on paper.** A single source-preserving matching can enforce both of the following prohibitions on every actual survivor in each complete terminal shell \([U,2U)\). The relations may vary with \(X,U\); their lists are specified per prime, shared by the entire shell. Degrees refer to possible *larger* partners of a fixed smaller prime. Incoming degrees need no bound.

1. On primes \(p\ge U^a\), for any fixed \(0<a<1/2\), forbid a partner graph of outdegree \(U^{o(1)}\). A small admissible fixed polynomial degree is also permitted as specified below. This conclusion uses the earlier three matching scales.
2. On **all** primes \(p>y=\lceil\log_2 X\rceil^2\), forbid any lists of \(O(p^\theta)\) possible larger primes, for some fixed \(\theta>0\) independent of \(X\). This composes with the existing three-large-factor constraint. The permitted exponent can be very small and depends on the fixed donor and factor parameters.

Any number of prescriptions can be combined if their union satisfies the stated degree budgets. The lists cannot change with the undisclosed cofactor of \(n\) for a given smaller prime. They may be nonmonotone and can link widely separated factor sizes. They need not correspond to short ordinary prime gaps. The same positive and negative tree energies each change by \(O(1)\) per complete shell, in the existing stronger sense that nodewise absolute differences weighted by their native weights have bounded sum. This holds with the retained path, moving-small-factor, central divisor-gap and [all-divisor spacing](SURVIVOR_DIVISOR_SPACING.md) restrictions. Original signed vertices and actually spent opposite-sign donors are counted throughout.

## New first-stage exceptional cells

For a shell graph on \(p\ge U^a\) of outdegree at most \(U^{\delta+o(1)}\), let \(T\) count original squarefree rough labels carrying an edge inside \(J\), without requiring that they satisfy any other new target restriction. A label is an actual multiple of \(pq\) with \(p<q\); hence \(p\le\sqrt{2U}\). Multiple edge witnesses only increase the following positive upper. In the complete shell,
\[
 T_{\rm shell}\le\sum_{U^a\le p\le\sqrt{2U}}\sum_{q\sim p,\ q>p}
             \left\lfloor\frac{2U}{pq}\right\rfloor
       \ll U^{1-a+\delta+o(1)}.
\]
On any \(H\)-cell, counting multiples by \(H/(pq)+1\) gives
\[
 T_J\ll H U^{-a+\delta+o(1)}+U^{1/2+\delta+o(1)}.                 \tag{1}
\]
The sum \(\sum_{p\ge U^a}1/p^2\ll U^{-a}\) needs only ordinary integer counting. No uniformity in pairs of primes in short intervals is assumed.

Recall \(V=\prod_{p\le y}(1-1/p)\). The published matching first chooses \(c>0\) sufficiently small with \(\nu(.49)<1-4c\), then \(\eta=c/4\), and then the smaller donor cofactor constants. For \(\delta=0\), take \(c\) still smaller so \(2\eta<a\). More generally choose admissible constants with
\[
       \delta<\eta,\qquad 2\eta<a-\delta .                         \tag{2}
\]
The original fixed-power union over donor cofactors and its prime-window exceptional-volume bounds still hold after choosing its own cofactor exponent sufficiently small relative to this \(\eta\). At middle width \(H_2=2^{\lfloor(.5+\eta)\log_2 U\rfloor}\) and last width \(H_3=2^{\lfloor .58\log_2 U\rfloor}\), (1) is \(o(H_iV)\) on every native cell. [Parameter order and supply of each genuine sign](../step4-prime-transport-2026-11-19/POSITIVE_DENSITY_RETIREMENT.md)

At the first width \(H_1=2^{\lfloor(\log_2 H_0)/2\rfloor}\), \(H_0=U2^{-s_X}\), \(s_X=\lceil\sqrt{\lfloor\log_2 X\rfloor}\rceil\), mark additional bad cells having more than \(c_0 H_1 V\) new targets. Choose \(c_0\) a sufficiently small fixed fraction of the spare supply of either sign, leaving room for the original selections. Total extra bad integer length is at most \(T_{\rm shell}/(c_0V)\ll U^{1-a+\delta+o(1)}\). A new target may both use a donor and disqualify a donor. Each sign pool loses at most the total new target count, so both debits fit on a good cell. Start with the union of targets and remove them from both prospective donor pools. Earlier pairs in any larger good cell debit its opposite target and donor counts equally. At stage one the number of unmatched targets is therefore \(K_1\ll U^{1-3c}+U^{1-a+\delta+o(1)}\). The earlier bound \(K_2\ll U^{.76}\) survives at stage two. All targets are paired within their stage-three cell.

For each polarity \(s\), full charge \(f_J\), and true residual \(r_J\), use \(|[s f_J]_+^2-[s r_J]_+^2|\le2H|f_J-r_J|\). Between widths \(H_i\) and \(H_{i+1}\) at most \(2K_i\) uncompensated endpoints remain on any level. With \(w_J=H/(UH_0)\), the total intermediate cost is \(O(K_i H_{i+1}^2/(U H_0))\). At stage one both exponents are negative by (2) and the earlier choice \(2\eta<3c\). At stage two the exponent is \(.76+1.16-2+o(1)<0\). Fine levels cost \(O(H_1^2/H_0)=O(1)\). At and above \(H_3\) the signed net deletion in every node is zero. This proves the claimed transferable bound for the first graph. [Source definition and weighted one-sided comparison](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md)

## Polynomial outgoing lists down to the actual rough threshold

The earlier factor restriction with \(k=3\) supplies a fixed \(\xi=1/u>0\) such that every candidate passing it has at least three distinct primes above \(U^\xi\). Choose \(0<\theta<\min(1,\xi/(1-\xi))\). For any pair \(p<q\mid n\) in such a candidate, a third prime above \(U^\xi\) divides \(n/(pq)\). This is true even when one or both of \(p,q\) lie below \(U^\xi\). Consequently
\[
 p\le\sqrt{2}\,U^{(1-\xi)/2}.
\]
Count new targets only among candidates outside the already prescribed target set. Counting all multiples after imposing the last necessary inequality gives, uniformly in each donor cell,
\[
 T_J\ll H\sum_{p>y}p^{\theta-2}+
             \sum_{p\le\sqrt{2}U^{(1-\xi)/2}}p^\theta
       \ll H y^{\theta-1}
            +U^{(1-\xi)(1+\theta)/2}=o(HV).                      \tag{3}
\]
The strict gap \((1-\xi)(1+\theta)<1\) and \(H\ge U^{1/2-o(1)}\) make the floor error small. The first term is small because \(V\asymp1/\log y\). Choose the admissible \(u\) with slack in the earlier three-factor exclusion, then fix \(\theta\); the parameters are fixed before the horizon. Equation (3) bounds both the new targets of either sign and any eligible pool members they could disqualify. It requires no additional first-stage exceptional cells. It can therefore be used jointly with the first construction. [Fixed minimum number of large prime factors, its choice of \(u\), and matching](../step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md)

## Lists chosen separately on each first-stage cell

Fix an integer \(k\ge3\) and its admissible threshold \(U^\xi\) and donor parameters before choosing cutoffs. Put \(\beta=(k-2)\xi<1\). On the candidates with at least \(k\) such distinct primes, \(n/(pq)\) contains at least \(k-2\) of them; hence \(p\le\sqrt2\,U^{(1-\beta)/2}\). Fix \(C<\infty\) and \(0\le\theta<\min(1,\beta/(1-\beta))\). For every sufficiently large shell and **every** assignment of lists \(G_I(p)\) to its first-stage cells \(I\), require only that each list contains at most \(C p^\theta\) possible larger primes \(q>p\). The lists may be chosen after inspecting all the genuine factorizations and charges. Freeze them before pairing. Within a given \(I\) there is a single list for each \(p\), shared by every label in that cell.

The number of additional targets on \(I\), after allowing for the earlier target categories, is at most \(\varepsilon_U H_1V\), where uniformly in both the cell and the assignment,
\[
 \varepsilon_U\ll_C \frac{y^{\theta-1}}{V}
                 +\frac{U^{(1-\beta)(1+\theta)/2}}{H_1V}=o(1).
\]
This follows from the same positive count as (3), with \(\beta\) in place of \(\xi\). For an \(H_2\)- or \(H_3\)-cell \(J\) the first-stage cells partition \(J\) exactly. Summing their bounds gives \(\varepsilon_U |J|V\), with the same \(\varepsilon_U\), although different constituents can have entirely different lists. The same total bounds either sign of new targets and either sign of lost donor offers. Apply the earlier matching to this fixed union. The quantifiers are “for every admissible assignment there exists a matching”; both the matching and the survivors can depend on that assignment.

This also allows a family of tests along each near-root dyadic path. For example, restrict the smaller primes in these tests to \(p\ge U^a\), for fixed \(a>0\). Suppose each first-stage cell inherits at most \(R_U=U^{o(1)}\) tests in total from its ancestors and any local choices, uniformly in the cell and all admitted choices. If every test offers at most \(C_0p^{\theta_0}\) candidates with a uniform \(C_0\) and fixed \(\theta_0<\theta\), their union offers at most \(C_0R_U p^{\theta_0}\le p^\theta\) eventually, since \(C_0R_U\le U^{a(\theta-\theta_0)}\). Existing lists can be included within the same total budget. A logarithmic number of ancestors is harmless. Only the union seen along a single cell's path needs to meet that budget; there is no demand to union tests on unrelated paths. For primes down to \(y\), check the actual outgoing bound separately; the macroscopic-prime inequality need not hold there.

Every finished opposite-sign pair lies in a single \(H_3\)-cell. Thus on **every aligned node \(J\) of width \(H\ge H_3\)**, including each base cell, the residual charge satisfies \(r_J=f_J\) exactly for every admissible assignment and its matching. In particular the one-sided square on each such node is invariant under all these choices. The local freedom restricts what factorizations can carry that charge. The remaining independent upper must still bound the original charge at these scales.

**Scope of the improvement.** This theorem constructs a new jointly matched survivor set. Simply discarding the collision vertices from an existing signed survivor file can leave their former partners behind and has no such guaranteed \(O(1)\) cost. The distinct [signed cofactor calculation](SPARSE_PRIME_FACTOR_CHARGES.md) estimates the collision sector on the unselected full source *without* changing the rows or selecting new donors. The original primitive-to-node comparison is made before these reductions. Every new survivor still has a sign fixed by the parity of all its prime factors. No bound on its aggregate large-cofactor parity follows from the allowable absence of sparse relations. Step 4 and RH remain **OPEN**.
