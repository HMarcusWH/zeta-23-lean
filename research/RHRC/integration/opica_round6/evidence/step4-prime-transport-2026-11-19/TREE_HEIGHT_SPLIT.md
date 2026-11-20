# How finite-height zeros enter the interval variance

**DERIVED on paper.** The maximal disjoint-interval estimate can distinguish zeros at bounded heights from the far-height edge. The distinction matters if the rightmost zeros are separated in real part from that latter edge. Let
\[
 B=\sup_\rho\Re\rho,\quad B_\infty=\limsup_{|\Im\rho|\to\infty}\Re\rho,
 \qquad b=B-\tfrac12,\quad b_\infty=B_\infty-\tfrac12.
\]
These are features of the actual zeta function. Both \(B\) and \(B_\infty\) are at least \(1/2\) by symmetry and the existence of arbitrarily high zeros.

In the notation of [TREE_INTERVALS.md](TREE_INTERVALS.md), for arbitrary subintervals of the \(H\)-cells in a shell \([U,2U)\),
\[
 \sum_j\left|\sum_{n\in I_j,(n,6l)=1}\mu(n)\right|^2
 \ll_\epsilon l^\epsilon
 \bigl(U^{2B_\infty+\epsilon}+H U^{2B-1+\epsilon}\bigr).           \tag{1}
\]
Indeed if \(B_\infty=B\), the earlier estimate suffices. Otherwise fix \(\sigma>B_\infty\) as close to \(B_\infty\) as desired, strictly below \(B\), and avoid the real parts of the finitely many zeros to the right of an intermediate line in \((B_\infty,\sigma)\). The Borel–Carathéodory and three-circles proof of the subpower bound for the reciprocal of zeta on \(\Re s\ge\sigma\) now applies at all sufficiently large heights. On the line \(\Re s=\sigma\) itself, the remaining bounded-height segment is compact and zero-free. Its contribution is covered by a constant depending on this choice of \(\sigma\). For all sufficiently large \(U\), the two horizontal sides of the Perron rectangles are above all the exceptional poles. The bounded \(U\)-range is covered by counting.

Move each half-integer endpoint contour to this line. The estimates (3) and (4) in [the interval proof](TREE_INTERVALS.md) bound the sum of squared contour-remainder increments by \(O_\epsilon(l^\epsilon U^{2B_\infty+\epsilon})\). In the finitely many residue terms a zero \(\rho\) of multiplicity \(m\) contributes \(x^\rho P_{\rho,l}(\log x)\) with a polynomial of degree at most \(m-1\). Its coefficients are \(O_{\rho,\eta}(l^\eta)\) for every \(\eta>0\). To see this, take a small fixed circle about \(\rho\) in \(\Re s>0\), separate it from all other zeros, and use the finite Euler product bound \(O_{\rho,\eta}(l^\eta)\) there for \(\prod_{p\mid6l}(1-p^{-s})^{-1}\). Cauchy estimates bound all the necessary Laurent coefficients after the fixed pole is removed.

Every residue profile has derivative of modulus \(O_{\rho,\eta}(l^\eta U^{B-1+\eta})\) on the shell with its half-unit endpoint margin. Its increment on interval \(j\) costs this quantity times the half-integer interval length. The squared lengths sum to \(O(UH)\) by disjointness and maximal length \(O(H)\). Summing the finitely many profiles and decreasing the preliminary losses proves (1). At widths below one, direct counting of the actual labels in disjoint cells costs \(O(U)\) and suffices. The same proof applies to arbitrary disjoint intervals of lengths in \([H,2H]\). Their left endpoints have separation \(\gg H\); their right endpoints separately have the same separation. Splitting lengths into dyadic classes extends the \(U^{2B+\epsilon}\) upper to arbitrary individual interval lengths and adaptive partitions.

## Native signed covariance

In a terminal shell of the native tree, at width \(H=H_0 2^{-k}\), both the positive energy and the absolute value of the aggregate signed small-GCD covariance at that depth obey
\[
 \ll_\epsilon 2^{-k} U^\epsilon
       \left(U^{2b_\infty}+\frac{H}{U}U^{2b}\right).                \tag{2}
\]
For the GCD mask use the exact identity (6) of [TREE_INTERVALS.md](TREE_INTERVALS.md) at scale \(U/(de)\), width \(H/(de)\) and excluded modulus \(6de\). The first term of the unweighted estimate has the divisor weight \((de)^{-2B_\infty}\), and the second has weight \((de)^{-2B}\), including the reciprocal \(de\) in the rescaled width. Either double sum costs at most \(O(\log^2(2U))\). If the rescaled width is less than one, the first term alone bounds all nonempty integer cells. The terminal diagonals belong to the removed large-GCD sector. All original coefficients and arithmetic signs are retained throughout this estimate.

Since \(2^{-k}=H/H_0\) and \(H_0=U\,X^{-o(1)}\) on terminal shells, the sum of absolute signed level totals in the region
\[
                     H\le U^{1-\max(2b_\infty,b)}
\]
is \(O_\epsilon(X^\epsilon)\) at every sufficiently large integer horizon. Sum the geometric weights and allow the \(O(\log X)\) shells. In particular if \(B_\infty=1/2<B\), the paid region extends to \(U^{1-b}\), a fixed power above the elementary square-root width whenever \(b<1/2\). This condition permits arbitrarily many off-line zeros approaching the line at large height. If \(B_\infty=B\), the general bound in the earlier interval paper applies unchanged. No strict separation of the two real-part edges has been established. In either case the signed charge on the coarsest nodes remains open.
