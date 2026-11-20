# The unsigned counting error on an arbitrary disjoint cut

**DERIVED on paper.** The counting estimate in the first part is unconditional. The implication for a zeta zero also uses the published OPICA paper estimates for one polarity and for signed interval sums. The finite compiler modules cover separate identities. Step 4 and RH remain OPEN.

## A stronger arithmetic estimate for the actual unsigned field

Freeze the original roughness \(y=\lceil\log_2X\rceil^2\), a set of marked primes in \((y,z]\) with \(z=(\log X)^{2+o(1)}\), and a complete terminal shell \([U,2U)\). Let \(N_J(F)\) count the squarefree, rough integers in \(J\) with exactly the marked fingerprint \(F\). Use the full Euler density vector \(\rho\) of the earlier unsigned calculation. For **any disjoint collection** \(\mathcal D\) of half-open integer intervals within this shell,
\[
  \sum_{J\in\mathcal D}\left(\sum_F |N_J(F)-|J|\rho(F)|\right)^2
       \ll_\epsilon U X^\epsilon .                                      \tag{1}
\]
There is no charge for the number of intervals. Their widths can differ and they may be chosen after observing both signs. The marked set is fixed in the shell. A different subset of its fingerprints may be tested on each cell. [Arithmetic inputs and the earlier weighted estimate](../step4-parity-deficit-2026-11-20/SURVIVOR_HAAR_FINGERPRINTS.md)

Write the true signed-vector convolution for these **unsigned counts** as \(A=\mathbf1*B_0\) in the finite group algebra of fingerprints. The local polynomial for \(B_0\) is \(1-t\) at a prime through \(y\), \((1+\mathbf e_{\{p\}}t)(1-t)\) at a marked prime, and \(1-t^2\) at any other prime. Hence for fixed \(0<\delta<1/2\) and \(\sigma=1/2+\delta\),
\[
   M_\sigma=\sum_{d\ge1}\|B_0(d)\|_1d^{-\sigma}
       \le \zeta(2\sigma)\exp\!\left(2\sum_{p\le\max(y,z)}p^{-\sigma}\right)
       = X^{o_\delta(1)},\qquad \rho=\sum_d B_0(d)/d .
\]
For one divisor put \(e_J(d)=\#\{n\in J:d\mid n\}-|J|/d\). For \(d\le2U\), every \(|e_J(d)|\le1\). Disjointness gives
\[
  \sum_J |e_J(d)|^2\le \sum_J |e_J(d)|
       \le (U/d+1)+U/d\le4U/d .
\]
For \(d>2U\), there are no multiples and the Euclidean norm of the errors is at most \(U/d\). Minkowski in the interval index, after taking the fingerprint norm, gives
\[
 \left(\sum_J\|N_J-|J|\rho\|_1^2\right)^{1/2}
  \le 2\sqrt U\sum_{d\le2U}\|B_0(d)\|_1/\sqrt d
            + U\sum_{d>2U}\|B_0(d)\|_1/d
  \ll_\delta U^{1/2+\delta} M_\sigma .
\]
Choose \(\delta\) sufficiently small for the requested exponent, before \(X\). This proves (1), including for a random or arithmetically chosen cut after fixing its realized cells. On one dyadic level, (1) pays the squared discrepancy **with weight \(1/U\)**. The older product comparison charged it with weight \(2^{-k}/U\) at level \(k\). Summing the stronger bound over the logarithmically many levels also controls all the nodes with the constant shell weight. The same argument pays an exact removed-count correction to the survivors' center, because their corrected unsigned discrepancy is still the raw discrepancy.

The master marked set can also be the union of all primes in the allowed range. Forgetting a different selection of marks on each interval pushes both its count vector and its density vector through the same projection. The fingerprint norm contracts under each such projection. Thus even these cell-specific choices obey (1).

## A stronger test of what must remain signed

Use the native depths and complete whole shells from [the nested path calculation](NESTED_SIGNED_OBSTRUCTION.md). Fix one polarity \(s\), and \(0<a<c<1/4\). At each shell cover every native base cell by a disjoint stopping cut between depths \(\lfloor a\log_2U\rfloor\) and \(\lfloor c\log_2U\rfloor\). Include geometrically empty cells in this cover. With the original genuine matched arithmetic and both target and partner corrections, put
\[
 S_s(a,c;X)=\sum_U\min_{\mathcal C_U}
            \sum_{J\in\mathcal C_U} Q_J^s/U,
 \qquad Q_J^s=\big[[sr_J]_+^2-D_J^2\big]_+ .
\]
Here \(D_J\) sums all fingerprints before squaring. On every tested cell \(r_J=f_J\) is the full raw signed charge because every actual matched pair lies within one finer, aligned third-stage cell. All signs in the following estimates are the same fixed sign.

Let \(B=\sup_\rho\Re\rho\) for the nontrivial zeta zeros and \(b=B-1/2\). If \(b>0\), the earlier one-sided detector and signed mean-square estimate give a native cell \(I\), depth \(k_0<\lfloor a\log_2U\rfloor\), at every sufficiently late \(X\), with \(s f_I/\sqrt U\ge X^{b-o(1)}\). Every admissible cut partitions this particular cell into at most \(2^{\lfloor c\log_2U\rfloor-k_0}\le X^c\) pieces. For any such partition, additivity, Cauchy–Schwarz, (1) and the exact node identity give
\[
 \sum_{J\subset I,\ J\in\mathcal C_U}Q_J^s/U
 \ \ge\ \frac{[s f_I]_+^2}{U\,\#\{J\in\mathcal C_U:J\subset I\}}
                 -\frac1U\sum_{J\subset I,\ J\in\mathcal C_U}D_J^2
 \ \ge\ X^{2b-c-o(1)}-O_\epsilon(X^\epsilon).
\]
The bound is simultaneous over every such cut, including its minimizer. For the upper, group the selected cells by depth. Apply the prior signed mean-square bound to the full level, a positive majorant. This bounds every allowed cut at once, with at most logarithmically many levels and shells. With the positive part of the exponent on the left, this proves
\[
 (2b-c)_+\le\liminf_X\frac{\log(1+S_s(a,c;X))}{\log X}
 \le\limsup_X\frac{\log(1+S_s(a,c;X))}{\log X}\le2b .
\]
If \(2b\le c\), the asserted lower is simply zero. Thus an independent cofinal upper \(S_s\le C X^\lambda\) implies \(B\le1/2+(c+\lambda)/2\). At a fixed window this has half the depth loss in the earlier bound for the different, maximum-path observable. The two observables have different units of aggregation. For the bottleneck \(Z_s\) of the nested-path paper, \(Z_s\le S_s\le X^{c+o(1)}Z_s\). For the second inequality take a first-hit cover in each base; the deepest allowed level over all shells has at most \(X^{c+o(1)}\) cells. Thus their cofinal criteria coincide when the depth exponent and requested loss tend to zero. They are two ways to test the same open arithmetic issue.

**OPEN.** Bound the complete signed cost of one admissible cover at arbitrarily late cutoffs, with \(c\) and \(\lambda\) tending to zero and constants fixed before the choice of cutoff. Equation (1) pays the full unsigned error even on the best data-dependent cover. It does not pay the opposed parity product. A single deleted cofactor class, one sign chosen separately per cell, or overlap charged as disjoint would change the test.
