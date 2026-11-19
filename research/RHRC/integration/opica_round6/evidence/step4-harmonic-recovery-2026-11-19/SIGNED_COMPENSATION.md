# What the actual arithmetic already cancels on the pair graph

**DERIVED on paper.** Let \(P(X)\) be the sum of the positive edge weights on the retained graph and let \(N(X)\) be the absolute weight of its negative edges. This applies both to the rational graph and the binary tree. Write \(s\) for that graph's specified grid resolution, differing by at most one between the two constructions. At all sufficiently large integer cutoffs,
\[
 P(X)+N(X)\asymp X/2^s,\qquad
 \frac{|P(X)-N(X)|}{P(X)+N(X)}
 \ll \exp[-c\,(\log X)^{3/5}(\log\log X)^{-1/5}]
\]
for some \(c>0\). This includes the actual shared-divisor mask. The same estimates hold if the fine tree levels and the subpower short gaps of PAID_PAIR_DISTANCES.md are removed. This gives a genuine signed bound on the remaining graph without a fixed right-edge hypothesis. It leaves a large gap to the one-sided cofinal target. [Mertens estimate of Lee and Leong](https://arxiv.org/abs/2208.06141)

## Absolute mass and genuine coherent blocks

In any dyadic shell \(U\le q<2U\) let \(H_0=U/2^s\) (for large terminal shells). A retained unordered pair has combined weight at most \(4/U\); its indices differ by at most \(H_0\). Hence the shell costs \(O(H_0)\) in absolute value, and the upper follows by dyadic summation. For the lower, choose a complete shell \(U\asymp X\) inside the terminal range. For example \(U=2^{\lfloor\log_2 X\rfloor-1}\) works for all sufficiently large \(X\) since \(X^{0.99}<X/4\) eventually. There are \(\gg U\) nonzero squarefree labels coprime to six by elementary squarefree counting. Cauchy's inequality across the \(2^s\) cells gives \(\gg U^2/2^s\) unordered distinct pairs after subtracting diagonals. Each such pair has weight \(\gg1/U\): use just the root term for the tree and the positive denominator bound for the rational kernel. The number with common divisor \(\ge D=X^{0.01}\) is at most
\[
 \sum_{d\ge D} \lfloor 2U/d\rfloor\lfloor H_0/d\rfloor\ll U H_0/D.
\]
Indeed \(d\) divides both the smaller label and their positive difference. Thus the discarded fraction tends to zero and the lower follows. The same argument applied just to prime labels, using the prime number theorem, gives a **positive** coherent contribution \(\gg X/(2^s\log^2 X)\), from pairs of distinct actual primes. Those pairs already meet the GCD restriction. They must be compensated elsewhere.

## Signed count

Put \(f(L)=L^{3/5}(\log L)^{-1/5}\). The unconditional Mertens upper is \( |M(y)|\ll y e^{-c_0 f(\log y)}\) for large \(y\). Removing 2 and 3 preserves this bound with a smaller constant. Specifically, sum \(M(y/d)\) over \(d=2^i3^j\); for \(d\le\sqrt y\) sum the geometric reciprocals and use \(f(\log(y/d))\gg f(\log y)\). For \(d>\sqrt y\), counting alone contributes \(O(y^{3/4}\sum_d d^{-1/2})\). Hence every restricted-prefix difference in a terminal shell is \(O(U e^{-c_1 f(\log X)})\). The shell's endpoints are comparable and \(\log U\ge0.99\log X-O(1)\).

For the tree, before imposing a GCD cutoff, the full signed form including the diagonal is \(\sum_J S_J^2/(U2^k)\). Each shell's weighted node count \(\sum_J2^{-k}\) is \(O(2^s(1+\log X))\). The full energy is therefore \(O(X\,2^s(1+\log X)e^{-2c_1 f(\log X)})\). The rational graph gives the same bound by its positive moment expansion: the \(n\)-th monotone weight on a cell costs \(O(2^{-n}U e^{-c_1f(\log X)})\); the square and geometric coefficients sum. Subtract the diagonals, of size \(O(\log X)\). The large-GCD off-diagonal terms removed have absolute weight \(O(X/(2^s D))\) by the preceding count summed over shells. Finally \(s=O(\sqrt{\log X})=o(f(\log X))\), so dividing by the proven absolute mass gives the assertion. The omitted fine/short sectors cost \(X^{o(1)}\) absolutely. This proof controls an entire signed graph for all large cutoffs and also explains why a coherent prime-only subgraph is a poor estimate for the complete source.

In particular both \(P\) and \(N\) are asymptotic to half their sum, despite exact opposite-sign examples for \(P-N\). With the separately cited project ceiling \(B\le0.873346\), the exponent transfer gives the one-sided relative upper \([P-N]_+/(P+N)\ll_\epsilon X^{-0.253308+\epsilon}\). Bounding both full energies and the signed large-GCD subtraction as in the tree proof also gives this power upper for the absolute difference. The Step 4 criterion still requires cofinal **absolute-scale** \(P-N\le X^\epsilon\) for every \(\epsilon>0\), equivalently cofinal one-sided relative size \(X^{-1+\epsilon}\) with arbitrarily small positive loss. The estimates above do not reach it.
