# Where the signed Möbius tree can carry a zero

**DERIVED on paper.** Over one shell, all the disjoint node charges together obey the mean-square upper that a single Mertens prefix obeys. The bound also holds for the largest absolute subinterval charge in each node, with the actual Möbius signs and arbitrary common excluded primes. It rules out a fixed-power range of smaller nodes as the source of the full off-line-zero exponent. It also gives an integer version of the tree statistic. The upper on the remaining coarse signed charges needed for Step 4 is **OPEN**.

## A uniform maximal interval bound

Let \(B=\sup_\rho\Re\rho\) over nontrivial zeta zeros and \(b=B-1/2\). In \([U,2U)\), \(U\ge2\), take the cells of one grid of spacing \(1\le H\le U\), with any origin. Intersect with the shell. In each cell choose any subinterval \(I_j\), including an empty one. Then for every \(\epsilon>0\) and every positive integer \(l\),
\[
 \sum_j\left|\sum_{\substack{n\in I_j\\(n,6l)=1}}\mu(n)\right|^2
 \ll_\epsilon l^\epsilon U^{2B+\epsilon}.                         \tag{1}
\]
In particular (1) applies after separately choosing the two endpoints in each cell to attain its largest absolute charge. The elementary bound \(O(UH)\) also holds. If \(B=1\), counting all labels gives (1). Widths at most four cost \(O(U)\) by disjointness. These estimates also cover the rescaled grids of width less than one used below.

Suppose \(B<1\). Fix \(B<\sigma<1\) and a small \(\nu>0\). On \(\Re s\ge\sigma\),
\[
 F_l(s)=\frac1{\zeta(s)}\prod_{p\mid6l}(1-p^{-s})^{-1},
 \qquad |F_l(s)|\ll_{\sigma,\nu} l^\nu(1+|\Im s|)^\nu.            \tag{2}
\]
Use the classical subpower reciprocal bound strictly to the right of \(B\). The added Euler factors cost \(O_\nu(l^\nu)\), since \((1-p^{-1/2})^{-1}\le p^\nu\) for every sufficiently large prime. The Dirichlet coefficients on the original absolutely convergent line are precisely the signs in (1). The earlier [sharp-prefix contour proof](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md) and [reciprocal estimate](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) give the analytic input and its \(B=1\) convention.

For \(H>4\) replace each nonempty set of integers by its half-integer enclosure \((a_j,b_j]\), from half a unit below the first label to half a unit above the last. These intervals have disjoint interiors, length at most \(H+1\), and endpoints comparable to \(U\). Among cells of the same original index parity, distinct left endpoints are separated by \(\gg H\). The right endpoints separately have the same property, even for adversarial subinterval choices.

For an endpoint \(z\), Perron's formula with height \(V=\lceil(2U)^4\rceil\) and initial line \(1+1/\log(2U)\) has error \(O(U\log^2(2U)/V)\). Near \(z\), sum the reciprocal distances to a half integer with coefficients bounded by one. Outside \([z/2,2z]\), bound the absolute Dirichlet series on the initial line. Move to \(\Re s=\sigma\). The two horizontal integrals cost \(O_{\sigma,\nu}(l^\nu U V^{-1+\nu})\) by (2). There is no residue at 1. With \(\nu\) small enough the combined error is \(O_{\sigma,\nu}(l^\nu U^{-2})\) per endpoint.

Set \(T_0=U/H\ge1\). For \(|t|\le T_0\), express the difference of the two Perron kernels as \(\int_{a_j}^{b_j} y^{\sigma+it-1}dy\). Cauchy on each physical interval, disjointness, and Plancherel in \(v=\log y\) give the following sum of squared contributions, up to fixed factors:
\[
 H U^{2\sigma-1}\int_{-T_0}^{T_0}|F_l(\sigma+it)|^2dt
 \ll_{\sigma,\nu} l^{2\nu}U^{2\sigma}T_0^{2\nu}.                   \tag{3}
\]
In particular the low frequencies use the actual difference, including its short length.

For each high band \(T<|t|\le2T\), \(T\ge T_0\), take the positive and negative frequencies separately, truncating the last band at \(V\). Put \(\widehat f_T(t)=F_l(\sigma+it)/(\sigma+it)\) on that band and zero elsewhere. The individual endpoint terms are fixed constants times \(z^\sigma f_T(\log z)\). Within either parity the log sample sites have spacing \(\Delta\gg H/U\). For separated sites,
\[
 \sum_i |f_T(v_i)|^2
 \ll (\Delta^{-1}+T)\|\widehat f_T\|_2^2.                          \tag{4}
\]
Indeed on disjoint intervals about these sites of length comparable to \(\min(\Delta,1/T)\), the fundamental theorem of calculus bounds a point square by a constant times the interval mean square plus its length times the integral of \(|f_T'|^2\). Sum and use \(\|f_T'\|_2\le2T\|f_T\|_2\). Since \(\Delta^{-1}\ll T\), (2) and (4) bound each high band's squared sample sum by
\[
 \ll_{\sigma,\nu} l^{2\nu}U^{2\sigma} T^{2\nu}.
\]
Sum square roots over \(O(\log(2U))\) bands, use (3), and include \(O(U)\) endpoint errors. Taking \(\sigma-B\) and \(\nu\) sufficiently small in terms of the requested \(\epsilon\) proves (1). No uniform rate as \(\sigma\downarrow B\) is asserted.

## Fixed-power depths on the native graph

Use the integer graph and the proven-on-paper band-to-tree implication of [DYADIC_TREE.md](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md). An integer \(X\) fixes the terminal labels \(X^{.99}<q\le X\), \(\mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}\), shells \(U=2^j\), \(s=\lceil\sqrt{\lfloor\log_2X\rfloor}\rceil\), and base width \(H_0=2^{\max(j-s,0)}\). At depth \(k\) the node width is \(H=H_0 2^{-k}\), with weight \(2^{-k}/U\). The terminal cutoff can clip the grid. Write \(S_J=\sum_{q\in J}\mu_6(q)\). Formula (1) directly gives
\[
 E_{U,k}=\frac{2^{-k}}U\sum_{J\ {\rm at\ this\ level}}S_J^2
       \ll_\epsilon 2^{-k}U^{2b+\epsilon}.                          \tag{5}
\]
The factor \(2^{-k}\) survives summing the nodes. The estimate permits a simultaneous maximal subinterval choice in every node.

For the small-GCD signed covariance use exact GCD inversion. The ordered charge of pairs with exact GCD \(d\), summed over this same depth and shell, is
\[
 \mu_6(d)^2\sum_{\substack{e\le2U/d\\(e,6d)=1}}\mu(e)
 \sum_J\left|\sum_{\substack{dem\in J\\(m,6de)=1}}\mu(m)\right|^2. \tag{6}
\]
Factor out \(d\), expand the coprimality of the two quotients by Möbius inversion, and factor out \(e\) in both coordinates. Squarefreeness supplies precisely the displayed coprimality. The inner intervals comprise one rescaled grid of spacing \(H/(de)\) in \([U/(de),2U/(de))\). Formula (1) bounds the sum of squares by
\[
 \ll_\epsilon (de)^\epsilon (U/(de))^{2B+\epsilon}
       = U^{2B+\epsilon}(de)^{-1-2b}.
\]
If \(U/(de)<2\), it is at least \(1/2\) and direct counting suffices. If the rescaled spacing is below one, each nonempty interval contains at most one label and direct counting again suffices. Summing (6) for \(d\ge D=X^{.01}\), multiplying by the node weight, gives
\[
 O_{\epsilon,b}(2^{-k}U^{2b+\epsilon}D^{-2b}) \qquad (b>0).       \tag{7}
\]
For \(b=0\) the sums over \(d,e\le2U\) incur at most two logarithms. For all \(d\) one may omit \(D^{-2b}\) in the bound. Removing large GCDs in (5) therefore gives the same level bound for the absolute value of the **sum** of small-GCD signed pairs. Every native terminal diagonal has \(q>D\) for sufficiently large \(X\), so it is removed in (7). Taking absolute values inside the original pair sum would lose the arithmetic cancellation.

Fix any \(0<\kappa<1\). The sum of the positive energies of all nodes of physical width \(H\le U^{1-\kappa}\), and the sum of the absolute values of the corresponding signed level totals, are separately
\[
 \ll_{\epsilon,\kappa} X^{2b-.99\kappa+\epsilon}.                  \tag{8}
\]
Indeed \(2^{-k}\ll 2^s U^{-\kappa}\) there. The depth weights sum geometrically, \(2^s=X^{o(1)}\), and every terminal shell has \(X^{.99}/2<U\le X\). The elementary absolute fine-level estimate in the earlier paper remains valid simultaneously. If \(b>0\), (8) has a strict power deficit from the full exponent \(2b\). At every sufficiently large integer horizon the same leading exponent is already present in the primitive covariance of nodes of physical width \(H>U^{1-\kappa}\), for **every fixed** \(\kappa>0\). This conclusion holds whether the finite-height right edge is attained or approached by distinct zeros. It does not supply uniform constants as \(\kappa\to0\).

As an absolute critical-scale payment, (5) controls the signed primitive level totals by \(X^\epsilon\) in aggregate on widths \(H\le H_0 U^{-2b}\). This extends the elementary square-root width cutoff by a fixed power if \(B<3/4\). For larger \(B\), (8) still rules out full-exponent concentration at every fixed-power depth. Neither conclusion gives an independent critical upper on the coarsest nodes.

## An integer statistic with the same normalized exponent

Keep exactly the fixed coarse nodes from the earlier paper, \(2k<\log_2 H_0\), and define
\[
 K(X)=2\sum_{J\ {\rm coarse}}\;
       \sum_{\substack{q<r\in J\\ \gcd(q,r)^{100}<X}}\mu_6(q)\mu_6(r).
                                                                    \tag{9}
\]
Thus each eligible unordered pair has integer multiplicity twice its number of shared coarse ancestors. Uniformly at integer horizons tending to infinity,
\[
                 1+\frac{[K(X)]_+}{X}=X^{2b+o(1)}.                \tag{10}
\]
For the positive energy \(A^\#=\sum_{J\ {\rm coarse}} S_J^2\), (1) summed over \(O(\log^2(2X))\) shell-depth choices gives \(O_\epsilon(X^{1+2b+\epsilon})\). The unweighted version of (7) gives a signed large-GCD error \(O_{\epsilon,b}(X^{1+2b-.02b+\epsilon})\) if \(b>0\); if \(b=0\) use \(O_\epsilon(X^{1+\epsilon})\). The entire unweighted diagonal is \(O(X\log(2X))\), counting at most one node per label and depth.

For the lower bound assume \(b>0\). Fix \(0<\tau<.01\) and \(0<u<2\tau b\). Take the bounded band of the earlier tree argument with lower squared-norm exponent \(2b-u\) at every sufficiently large \(X\). Remove all \(q<U_*=2^{\lceil(1-\tau)\log_2 X\rceil}\); their band norm costs \(O(X^{(1-\tau)(b+\eta)})\) by the restricted Mertens bound and partial summation, where \(\eta>0\) can be chosen small. All labels left lie in native terminal shells \(U\ge U_*\), including the shell clipped at \(X\). The exact dyadic telescoping and Cauchy argument of the earlier tree paper gives weighted energy \(\gg X^{2b-u-o(1)}\) there. Removing the fine nodes costs \(O(\log(2X))\) even in pairwise absolute value. Each remaining weight is at most \(X^{-1+\tau}\), so positivity gives \(A^\#\gg X^{1-\tau+2b-u-o(1)}\). Send \(u\) and \(\tau\) to zero after taking the lower exponent. This yields \(A^\#=X^{1+2b+o(1)}\) along all integers. The strict loss in the large-GCD contribution gives the same asymptotic exponent and eventual positivity for \(K(X)\). For \(b=0\) the upper just proved and the baseline one yield (10).

Equations (8) and (10) constrain the full, coupled Möbius source and establish where a hypothetical off-line zero would have to appear. A cofinal one-sided \(K(X)\ll_\epsilon X^{1+\epsilon}\) for every \(\epsilon>0\) would exclude it. The present argument supplies only the \(B\)-dependent upper. No new computation, Lean verification, or proof of that cofinal bound is asserted.
