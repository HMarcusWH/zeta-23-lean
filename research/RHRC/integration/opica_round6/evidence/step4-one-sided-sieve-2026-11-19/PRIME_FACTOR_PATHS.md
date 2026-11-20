# Which prime-factor histories can still carry the signed excess?

**DERIVED on paper.** On every complete terminal shell one can remove all rough squarefree labels with an atypical *running* number of prime factors, and all labels with a small cofactor, together with actual opposite-sign partners. For each polarity, the change in the original weighted one-sided square energy is \(O(1)\) per shell, including all depths. The removal and its constants are fixed independently of a hypothetical zeta zero. The result concerns the node detector for the full source. The original large-GCD comparison is invoked on that full source before the reduction. The finite test below measures the separate cost of changing a masked graph.

## The surviving labels

Freeze \(X\) and its actual roughness \(y=\lceil\log_2 X\rceil^2\). In a whole dyadic shell \([U,2U)\) inside \(X^{.99}<n\le X\), use every squarefree \(y\)-rough label with its sign \(\mu(n)\). For \(y\le v\le 2U\) put
\[
 A(v)=\sum_{y<p\le v}\frac1p,\qquad
 D(n)=\sup_{y\le v\le 2U}\left|
       \sum_{\substack{p\mid n\\y<p\le v}}1-A(v)\right|,\qquad
 L=1+A(2U).
\]
There are fixed \(\kappa>0\) and \(K<\infty\) such that all survivors satisfy
\[
     n/P^+(n)>X^\kappa,\qquad D(n)\le K\sqrt L .                   \tag{1}
\]
The same \(K,\kappa\) work in all sufficiently large whole terminal shells. Some additional labels satisfying (1) are spent as partners. Keeping their identity matters. For signs \(s=\pm1\), write \(f_J\) for the complete node charge and \(r_J\) for the surviving charge. With the original root length \(H_0=U2^{-s_X}\), subdivision \(H=|J|\), and weight \(w_J=H/(UH_0)\), the assertion is
\[
  \sum_{J\ {\rm in\ shell}} w_J\,
      \left|[s f_J]_+^2-[s r_J]_+^2\right|=O(1).                  \tag{2}
\]
The absolute value is inside the sum. The statement applies to every subset of the shell's nodes. Complete shells alone retain the earlier zero-sensitive exponent. For \(X=2^{100t}\) the full terminal graph partitions into such shells up to powers of two of zero weight. At arbitrary horizons the argument uses complete shells and makes no assumption about donors just outside a clipped cell. [Full-source detector and interior-shell criterion](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

## A maximal fourth moment on each actual cell

Let \(V=\prod_{p\le y}(1-1/p)\). Uniformly in any integer interval \(J\subset[U,2U)\) of length \(H\ge U^{.48}\),
\[
 \sum_{\substack{n\in J\\P^-(n)>y}}D(n)^4
                \ll HV L^2 .                                       \tag{3}
\]
This upper includes repeated prime factors in its population and counts distinct divisors in \(D\). It therefore bounds the number of actual squarefree target labels by \(C HV/K^4\).

Here are details to keep the conditioning and the growing number of cutoffs explicit. For each squarefree \(d\) formed from at most four primes in \((y,U^{1/40}]\), let \(N_d\) count \(n\in J\) divisible by \(d\) and by no prime through \(y\). For any fixed \(A>0\),
\[
 N_d=\frac Hd\bigl(V+O_A((\log U)^{-A})\bigr)+O_A(U^{o(1)}).
\]
Indeed, truncate inclusion and exclusion at the two parities nearest \(C_A\log\log U\). The elementary symmetric tail is bounded by \((\sum_{p\le y}1/p)^k/k!\) at the truncation degree \(k\). It is \(O_A((\log U)^{-A})\) by the prime harmonic bound and Stirling's inequality. Floor errors cost \(O(y^{k+1})=U^{o(1)}\) since \((d,\prod_{p\le y}p)=1\). This also proves \(N_1\asymp HV\) on the stated cells.

For any consecutive block \(I\) of primes through \(U^{1/40}\) above \(y\), put \(M=\sum_{p\in I}1/p\) and \(S_I(n)=\sum_{p\in I}(\mathbf1_{p\mid n}-1/p)\). Expanding the fourth power and using the estimate for \(N_d\) compares its normalized rough-cell moment with the fourth moment of independent centered Bernoulli variables of means \(1/p\). Independence is used only to *evaluate the finite main terms*. For the expansion with absolute coefficients, replace each centered factor by \(B_p+1/p\). The fourth moment is \(O((1+M)^4)\) by grouping tuples by repeated indices. Thus the relative sieve error is \(O_A((1+L)^4(\log U)^{-A}/V)\). The total floor error is \(O(U^{1/10+o(1)}/(HV))\). Both are \(o(1)\) uniformly. The independent centered moment is at most \(3M^2+M\), since only even pairs and fourth moments remain. Normalizing by \(HV\) gives a bound \(O(1+M^2)\).

Group consecutive primes into blocks of mass between 1 and 2, with at most one incomplete last block. There are \(O(L)\) blocks. Pad with empty blocks up to a power of two \(N\asymp L\). At scale \(2^j\) the normalized fourth moment of the largest absolute sum over its disjoint groups is at most
\[
             O((N/2^j)(1+2^{2j}))=O(N2^j).
\]
Every prefix at a block endpoint uses at most one of these groups at each scale. Minkowski's inequality bounds its maximal fourth norm by \(\sum_{j\le\log_2 N}O((N2^j)^{1/4})=O(\sqrt N)\). Within a block, the count and the centering mass are monotone; a partial centered sum has absolute value at most the absolute complete centered block sum plus 2. For \(v>U^{1/40}\) the extra prime divisor count is at most 41, and the extra reciprocal mass is \(O(1)\) by the prime harmonic estimate. These pointwise additions have bounded normalized fourth norm. This proves (3), including the supremum over all thresholds on the *same* integer.

## Paying the signed deletion

Use the fixed positive-density partner construction with \(0<\kappa=\alpha/100<\alpha<.001\) sufficiently small for its three interval estimates. Write \(Z=X^\kappa\) and \(M_0=\log Z/\log y\). Its source partners have the form \(mp\), with true prime \(p\) uniquely largest and \(Z<m\le X^\alpha\). Its cofactor lists give both signs separately: for each squarefree \(y^2\)-rough cofactor \(a\) in \((Z,X^\alpha/y^2]\) one offers \(a\) and the distinct cofactors \(\ell a\), \(y<\ell\le y^2\) prime. The cofactor reciprocal mass in **each** sign pool is at least \((99e^{-\gamma}\log(2)/2+o(1))M_0\). Both signs of the prescribed \(m\le Z\) targets together have reciprocal mass at most \((1+o(1))M_0\). On a good cell the existing fixed-tolerance prime count in each scaled interval therefore gives at least \(10HM_0/\log U\) source partners of either sign and at most \(2HM_0/\log U\) original small-cofactor targets in total. The same counts hold on every cell at the third scale. These are distinct integer labels. [Cofactor lists and uniformity](../step4-prime-transport-2026-11-19/POSITIVE_DENSITY_RETIREMENT.md)

Add to the target list every \(n\) with \(D(n)>K\sqrt L\), counting duplicates only once. In each cell of any of the three sizes, (3) bounds these additions by \(CHV/K^4\). Since \(V\asymp1/\log y\), \(M_0/\log U\asymp\kappa/\log y\). Fix \(K\) large enough that the additions are at most \(HM_0/\log U\). Remove all these targets from the potential partner lists before matching. The two lost margins (new targets and lost partners) are both covered by the strict supply bound above. No probabilistic assumption about parity conditional on \(D(n)\) enters this calculation.

Use the actual nested dyadic widths
\[
 H_1=2^{\lfloor(\log_2 H_0)/2\rfloor},\qquad
 H_2=2^{\lfloor(.5+\eta)\log_2U\rfloor},\qquad
 H_3=2^{\lfloor.58\log_2U\rfloor}.
\]
Here \(\nu(.49)<1-4c\), \(0<c<.002\), \(\eta=c/4\), and \(\alpha\) above is small enough for the scaled prime windows. All three lengths exceed \(U^{.48}\) eventually. In each cell in order of increasing stage, for each sign in turn match unused targets in increasing order to unused opposite-sign partners in increasing order. Each previous pair in a parent used one of each of its two relevant lists. Consequently a good parent matches all remaining targets regardless of the pattern in its children. The total integer lengths of bad cells after the first two stages are \(O(U^{1-3c})\) and \(O(U^{.76})\) respectively. They bound the counts \(K_1,K_2\) of unmatched targets. At stage three every cell is good. The estimates used here are for the same donor cofactors as in the earlier construction. The additional target test uses the elementary calculation (3) on *every* cell. [Transfer from prime windows to the actual grid](../step4-prime-transport-2026-11-19/PRIME_SPLIT.md) · [Gafni and Tao](https://arxiv.org/abs/2505.24017) · [Guth and Maynard](https://arxiv.org/abs/2405.20552)

Let \(e_J=f_J-r_J\) count the signed endpoints of the finished pairs. At lengths \(H\ge H_3\) it is identically zero. At any intervening level \(H_i\le H<H_{i+1}\), \(\sum_{|J|=H}|e_J|\le2K_i\), since earlier pairs cancel in each node. Each signed charge has absolute value at most \(H\). The scalar estimate
\[
 \big|[s f_J]_+^2-[s r_J]_+^2\big|\le2H|e_J|
\]
and the geometric weights bound the cost of these levels by \(O(K_iH_{i+1}^2/(UH_0))\). The exponents are at most \(-3c+2\eta+o(1)\) and \(.76+1.16-2+o(1)\). At widths \(H\le H_1\) direct counting costs \(O(H_1^2/H_0)=O(1)\). This proves (2).

## What this leaves to prove

Write \(r_J\) using exactly the survivors above, including the removal of spent partners. For either fixed polarity the sum over complete terminal shells differs from the original by \(O(\log X)\). Thus one can seek an independent bound
\[
       \sum_{J\ {\rm coarse,\ whole\ shells}} w_J [s r_J]_+^2
                                     \ll_\epsilon X^\epsilon
\]
at arbitrarily large cutoffs for every fixed \(\epsilon>0\). Both the cofactor floor and the simultaneous constraints (1) can now be imposed when seeking that bound. All labels with any *fixed* number of prime factors eventually violate (1), since \(A(2U)\to\infty\). This includes balanced semiprimes far outside the retired small-cofactor cone. On the original graph their cost is paid together with the real opposite signs used by the selector. A cutoff on prime-factor counts alone has a large signed bias. [Exact failure of fixed-layer truncation](WHOLE_COARSE_SURPLUS.md)

The fourth-moment upper estimates the number of labels one can afford to pair. On the retained paths, consecutive values of the final count still have opposite Möbius signs. A count of paths in the band gives no bound of square-root order for their signed difference. The preceding reduction leaves that independent arithmetic bound and Step 4 **OPEN**. Deleting these same endpoints directly from the primitive GCD-filtered pair sum would require an additional estimate for its changed rejected pairs. [Exact finite masked and unmasked controls](BALANCED_TRANSPORT_CHECK.json)
