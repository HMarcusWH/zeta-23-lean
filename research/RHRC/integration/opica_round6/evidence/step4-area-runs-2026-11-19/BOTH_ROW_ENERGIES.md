# Paying the energy of both complete product-row vectors

**DERIVED on paper.** Keep the same two disjoint outer-prime intervals, genuine source and fixed exponents as in the [cross-product calculation](SHARED_PRODUCT_COVARIANCE.md). The arithmetic normalization equations admit a choice of coefficients for which *each* complete row vector has squared Euclidean norm \(x^{3+o(1)}\) as an upper bound. Thus every association of the rows of bounded or subpower operator norm can be paid at the target scale. The native all-pairs signed product remains open.

## Distributing the coefficient corrections

For each of the two filters separately, fix its original \(L\) and all its lower coefficients. For each integer \(R=2L+1,\ldots,3L\) solve precisely that filter's four original scalar equations at \(R,4R,16R,64R\). Average these \(L\) solutions with weights \(1/L\). The four equations are linear in the final list of coefficients and remain exact. Every \(R\asymp L\) exceeds \(2L\), so the prescribed prefix and first unresolved dyadic band remain exact. The fixed normalized four-by-four matrices in the two proofs bound every individual correction by \(O(\log^2(2L))\) uniformly in this interval. Each integer \(m\) is of the form \(4^iR\) at most four ways, giving
\[
 |m a_m^{\mathrm{correction}}|\ll\log^2(2L).
\]
All original absolute moment estimates for the lists follow by the triangle inequality and averaging. Both sampled prime ranges are fixed by \(x,L\), independently of \(R\). All contour or real-variable error estimates previously used are uniform for \(R\asymp L\); the two averaged observations still equal \(F(x)+o(x^{3/2})\) at the same \(x\). This averages only the auxiliary representations; every observation inside the average uses the unchanged primes at the same horizon. [Factorial normalization](OLD_PRIME_LOCALIZATION.md) · [Eta normalization](ETA_FILTERED_PRIME_LOCALIZATION.md)

## Row energies and all low-norm associations

Let \(f_i(n)=(x-n)b_i(n;x)\) for \(1\le n\le x\), with the newly distributed coefficient lists. The low coefficients and the divisor convolutions are the same as in the [full row bound](SHARED_PRODUCT_COVARIANCE.md). The uniform correction bound removes every exceptional divisibility factor from its majorants. Thus \(|b_1(n;x)|\le x^{o(1)}\) and \(|b_2(n;x)|\le x^{o(1)}2^{v_2(n)/2}\). Every prime label, every power of two in the inverse eta factors, and all logarithms are included. Since \(\sum_{n\le x}2^{v_2(n)}\le\sum_{j\le\log_2 x}2^j\lfloor x/2^j\rfloor=O(x\log(2x))\), this proves
\[
 \sum_{n\le x}|f_1(n)|^2\le x^{3+o(1)},\qquad
 \sum_{n\le x}|f_2(n)|^2\le x^{3+o(1)}. \tag{1}
\]
For either row vector all additive phases therefore satisfy the exact mean-square bound
\[
 \int_0^1 \left|\sum_{n\le x} f_i(n)e^{2\pi i n\alpha}\right|^2 d\alpha\le x^{3+o(1)}
\]
by finite Parseval. The positive common semiprime diagonal from the cross-product calculation is unchanged: its cofactors miss every possible correction and still have exact coefficient \(-1\).

For any matrix \(M_x\) on these rows, \(|f_1^\mathsf{T}M_x f_2|\le \|M_x\|_{2\to2}x^{3+o(1)}\). In particular any bipartite graph of row pairs having maximum degree \(x^{o(1)}\) at each end is fully paid in absolute value, using the same norm bound on its nonnegative adjacency matrix and absolute row vectors. The earlier small-lcm absolute family also survives this averaged construction: assign pairs to their lcm \(w\), use the divisor bound on multiplicities and \(\sum_{w\le U}2^{v_2(w)/2}\ll U\). The native matrix has every entry equal to 1. Its operator norm is the number of rows, and its arithmetic pairing selects the single additive phase \(\alpha=0\). Inequality (1) therefore explains exactly which additional signed estimate is needed to pass from the complete row energies to that specific observation. On a set of additive phases of measure at most \(x^{-2d+o(1)}\) one of the two sums can exceed \(x^{3/2+d}\), by Chebyshev's inequality. Small measure alone cannot exclude the actual phase 0.

The cutoff cross-sections in the earlier drawings give a concrete example. For each cut \(j\), include all ordered pairs \(n\le j<m\) with weight \(1/(m-n)\). Even the **whole** distance-weighted matrix on \(n\ne m\) has row and column sums at most \(2(1+\log x)\); the two energy bounds therefore pay its full absolute contribution at \(x^{3+o(1)}\). Summing the cuts to reconstruct the unweighted product counts the pair \(m-n\) times and removes that discount exactly. This explains where the signed long-range estimate enters even after establishing the complete individual row energies.
