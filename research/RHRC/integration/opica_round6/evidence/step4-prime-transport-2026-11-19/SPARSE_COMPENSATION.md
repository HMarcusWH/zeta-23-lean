# Retaining the arithmetic compensation after removing a fixed cofactor range

**DERIVED on paper.** Fix a sufficiently small constant \(\kappa>0\), independently of the positions of zeta zeros and the desired closing exponent. On the genuine rough graph and the sequence \(X=2^{100t}\), write \(A=\{n:n/P^+(n)\le X^\kappa\}\). There is an observable rule retaining a subset \(L\subset A\) with
\[
 2^{2s}<n/P^+(n)\le X^{o(1)}\quad(n\in L),\qquad
 |L|=o(X/\log y).
\]
The reduced graph has precisely the vertices \(R=(\mathrm{all}\setminus A)\cup L\) and the original edges, weights and signs. It stores the signed charge of the *entire* original graph exactly on every node of width at least \(H_3\). For every \(\xi>0\), writing \(b=\sup_\rho\Re\rho-1/2\),
\[
 |C(\mathrm{all})-C(R)|\ll_{\xi,\kappa} X^{2b\kappa+\xi}.
 \tag{1}
\]
This holds for either the complete tree or its coarse levels. Here the small set \(L\) carries actual original vertices and its interactions with the large-cofactor vertices are retained. The estimates hold for the statistics with their original GCD test. In particular **one and the same reduced graph** retains the exponent \(2b\) at every sufficiently late aligned cutoff if \(b>0\), while obeying \(O_\epsilon(X^\epsilon)\) if \(b=0\). The required one-sided cofinal bound on this graph is open.

## The amount of imbalance to be transported

Use the definitions of \(s,y,H_0,H_i,c,\eta\) and the good-cell estimates of [the positive-density calculation](POSITIVE_DENSITY_RETIREMENT.md). Choose \(\kappa\) to satisfy all its upper restrictions on the largest cofactor exponent \(\alpha\). Here the largest allowed cofactor exponent is \(\kappa\) itself. For now fix \(0<\tau<\kappa\), set \(u=\tau/64\), and reserve the three disjoint cofactor intervals
\[
 (X^u,X^{2u}],\quad (X^{2u},X^{10u}],\quad (X^{10u},X^{64u}].
\]
All offers and targets are squarefree \(y\)-rough cofactors multiplied by a genuine prime. The targets \(T\) are all of \(A\) outside the three intervals. Reserve vertices that never participate in a match survive in \(L\).

There is a signed reciprocal estimate uniform in the endpoint \(t\):
\[
 \left|\sum_{m\le t,\;P^-(m)>y}\frac{\mu(m)}m\right|
 \le 2\prod_{p\le y}(1-1/p)^{-1}\ll\log y .
 \tag{2}
\]
Indeed \(\sum_{n\le t}\mu(n)\lfloor t/n\rfloor=1\) for \(t\ge1\), whence \(|\sum_{n\le t}\mu(n)/n|\le1+1/t\). Convolve with the indicator of integers all of whose prime factors are at most \(y\) and sum the reciprocals of that positive sequence. Formula (2) applies by subtraction on each fixed cofactor interval. Partial summation against \(1/\log(U/m)\) on \(m\le X^\kappa\) bounds the modeled signed prime rate of \(T\) in a good cell of length \(H\) by \(O_\kappa(H\log y/\log X)\), uniformly over all shells. This tends to zero compared with \(Hu/\log y\) for fixed \(u>0\).

More explicitly, with \(h=\log U/\log X\in[.99,1]\) the modeled rate for both signs in a polynomial cofactor interval \((X^a,X^d]\) is
\[
 (1+o(1))\, H V(y)\int_a^d\frac{dv}{h-v},
 \qquad V(y)=\prod_{p\le y}(1-1/p).
 \tag{3}
\]
This follows from the uniform squarefree rough count in the preceding paper by partial summation. Each sign receives half of (3), up to \(o(Hu/\log y)\) for the fixed reserve widths, by (2). The total gross prime rate through \(X^\kappa\) is \(O(H\kappa/\log y)\), by the upper Euler product. Require relative error \(\delta>0\) for each cofactor's individual prime count at a good cell. The exceptional-volume theorems permit **any fixed** \(\delta\). Take \(\delta\) small enough in terms of \(u,\kappa\) that the sum of errors in the signed target rate is below \(HuV(y)/20\). The uniform \(\log p=\log(U/m)+O(1)\) variation contributes a smaller error as \(X\to\infty\). For all sufficiently large cutoffs the raw target sign difference is then below \(HuV(y)/10\).

## Three reservoirs on the original nested grid

Process first the cells of length \(H_1\), then \(H_2\), then \(H_3\). In each cell match remaining targets of opposite signs to one another as far as possible. Match the remaining majority targets to opposite signs from that stage's reserve as far as possible. Order all lists by increasing integer label. No reserve vertex enters a second stage.

In a good cell at stage \(i\), the imbalance of the as-yet-unmatched targets is bounded by the raw signed target difference plus the total number of earlier reserve labels in the cell. This follows by restoring earlier pairs: target–target pairs have zero sum and each match against an earlier reserve changes the difference by at most one. By (3) and the fixed tolerances, there are enough reserve vertices of *either* sign to pay this bound. In units \(HuV(y)\), the approximate lower supplies per sign are at least \(1/2,4,27\) at the three stages, since \(1/(h-v)\ge1\). Earlier reserve counts are at most \(0,1/(.99-\kappa),9/(.99-\kappa)\) in the same units before tolerances. These are strict margins. Thus all targets are matched in every good cell. The number still unmatched at the first and second stages is \(O(U^{1-3c})\) and \(O(U^{.76})\) respectively, by the same all-cofactor exceptional-volume bounds. All final cells are good. These assertions are uniform in the shells for each fixed \(\tau\).

Let \(S=A\setminus L\) be the union of all matched vertices. Temporarily disregard the GCD test. Every signed pair of matches is internal to its common node at and above its matching scale. Hence \(S\) has charge zero in every node at \(H\ge H_3\). In the intermediate scales, \(\sum_J|\sum_{n\in J\cap S}\mu(n)|\le2K_i\) when at most \(K_i\) targets still needed to be matched after stage \(i\); every subsequent pair uses at least one such target. The bounds from the previous paper yield an \(O(\log X)\) unmasked off-diagonal signed incidence for the whole selection, including every edge to its complement. This reasoning also covers the coarse-only graph.

## Making a single choice at each cutoff

For integer \(j\ge1\) try \(\tau_j=\kappa 2^{-j}\), restricted to \(X^{\tau_j/64}\ge 2^{2s}\). Run the displayed matching and keep the choice if all targets finish and in every shell the unmatched counts after stages one and two are at most \(U^{1-2c}\) and \(U^{.77}\) respectively. Choose the largest successful \(j\), and use no deletions if no choice succeeds. This is a finite rule using only original arithmetic and fixed constants; it queries no zeta zero or future cutoff. For every fixed \(j\) it succeeds eventually. Thus \(\tau(X)\to0\), without needing a quantitative exceptional-set theorem at an \(X\)-dependent tolerance. The relaxed unmatched thresholds still give exponents \(-2c+2\eta+o(1)<0\) and \(.77+.16-1+o(1)<0\) in the two intermediate incidence bounds. Their constants are now uniform for the chosen rule.

Every unused reserve vertex has cofactor strictly above \(2^{2s}\) and at most \(X^{\tau(X)}\). All primes have therefore been matched. The leftover count is \(o(X/\log y)\): ordinary PNT on the full shell bounds the number for cofactor \(m\) above by \(O(U/(m\log X))\), uniformly up to \(X^\kappa\). The total reciprocal mass for \(y\)-rough \(m\le X^{\tau(X)}\) is \(O(\log(X^{\tau(X)})/\log y)\) by Mertens' prime product; \(\log(X^{\tau(X)})\) grows at least as fast as \(\sqrt{\log X}\) whenever a choice is admitted. Sum geometrically over the shells. Meanwhile \(A\) itself contains \(\gg\kappa X/\log y\) vertices by the last-shell prime count.

## Restoring the exact masked incidence

Let \(D(E)\) be the signed incidence of all *rejected* distinct pairs touching \(E\), counted once with the original orientations and node weights. The [deterministic cofactor calculation](DETERMINISTIC_CONE_GCD.md) proves \(|D(A)|\ll_{\xi,\kappa} X^{2b\kappa+\xi}\). In outline, every such pair shares the unique prime \(p\ge U/X^\kappa\). In a node its signed incidence is a difference of squares of true Möbius interval sums over the other factors, less the target diagonal. A rough Mertens upper bounds each square by \(X^{o(1)}(2U/p)^{2B+\xi}\), \(B=1/2+b\). Summing over \(p\) and the node weights gives the stated bound. This retains cancellations within a fibre and all cross terms with the complement.

The difference \(D(A)-D(S)\) consists only of rejected pairs with an endpoint in \(L\) and both endpoints outside \(S\). For any such endpoint \(n=mp\), \(m\le X^{\tau(X)}\), a rejection requires \(p\mid r\), with at most \(2H/p\) other multiples in a cell. The absolute shell estimate in the previous paper gives \(O(2^{-s}X^{\tau(X)})\). This argument permits *arbitrary* thinning of the leftover reserve. Combining it with the signed deterministic bound and the unmasked calculation proves (1). It does not apply an interval estimate to adaptively selected cofactors.

## Where the closing estimate now enters

For \(b>0\), the rough graph law and (1), with fixed \(\xi<2b(1-\kappa)\), give \(C(R)=X^{2b+o(1)}\) on every sufficiently late aligned cutoff. A one-sided \(C(R)\le X^\epsilon\) for every \(\epsilon>0\) on arbitrarily late aligned cutoffs would give a contradiction. \(R\) still contains both the large-cofactor vertices and their interactions with \(L\). The charge identity on each large node only states where the arithmetic imbalance is stored. It does not independently bound the size of those charges. All the asymptotic deductions here are paper mathematics; this checkpoint adds no claim of a Lean proof of Step 4.
