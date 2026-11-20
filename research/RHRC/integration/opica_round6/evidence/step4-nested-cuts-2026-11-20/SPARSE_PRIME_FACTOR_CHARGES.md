# Signed charge on labels carrying a sparse relation between large prime factors

**DERIVED on paper.** Fix \(0<\alpha<1/2\) and the original squarefree rough source \(\mu_y(n)\) on each complete terminal shell \([U,2U)\). Let \(G_U\) be any simple graph on primes \(U^\alpha\le p\le 2U\) with maximum degree \(U^{o(1)}\), uniformly as the shell grows. Include a label in \(A_U\) if two of its actual prime factors form an edge. The graph may depend on the shell. There is no assumption about the signs or distribution of its primes. For example it can connect all \(p<q\) with \(q-p\le\exp(\sqrt{\log p})\), with their actual overlaps.

Let \(B=\sup_\rho\Re\rho\), \(b=B-1/2\). At every node \(J\) in the shell, the original signed charge from this entire sector satisfies
\[
 \left|\sum_{n\in J\cap A_U}\mu_y(n)\right|
       \ll_\epsilon U^{B-\alpha(2B-1)+\epsilon}.                  \tag{1}
\]
The exponent uses the true right edge; this does not assume a numerical ceiling or locate a zero. Uniformity over a family of graphs means their asserted degree bound is uniform. For either polarity on all complete terminal shells, the complements \(A_U^c\) retain the published exact exponent \(2b\). Thus a cofinal subpower upper for the **collision-free** charge of one polarity suffices for Step 4. No such upper is proved. [Original detector for each polarity](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

## Multiplicity and the unchanged signed cofactor

For each integer \(n\) there are at most \(1/\alpha+O(1)\) primes \(\ge U^\alpha\) dividing it. Apply the exact inclusion–exclusion formula for the event that their induced graph contains an edge. A term selects a nonempty edge set and requires every prime in its vertex union to divide \(n\). Write \(d\) for their squarefree product. Terms with \(d>2U\) vanish. For \(d\le2U\) its signed contribution is exactly
\[
  \mu(d)\sum_{\substack{m\in J/d\\(m,d)=1}}\mu_y(m).
\]
The complete true cofactor remains. The original roughness \(y=\lceil\log_2 X\rceil^2\) is held fixed at both endpoints. The existing restricted Mertens estimate with \(l=d\) bounds this by \(U^{B+o_\epsilon(1)+O(\epsilon)}d^{-B}\), after differencing at the actual endpoints; if \(B=1\), use ordinary integer counting instead. This estimate follows by removing Euler factors in \(M(t)\ll_\epsilon t^{B+\epsilon}\) and costs at most \(X^{o(1)}\) for the roughness mask. For the additional \(d\) here the product has only a bounded number of factors \(\ge U^\alpha\). Equivalently those factors lie in an absolutely summable geometric Euler product for any fixed positive abscissa. [Uniform signed prefix estimate, equation (3)](../step4-prime-transport-2026-11-19/ROUGH_PRIME_TRANSPORT.md)

There are finitely many abstract graph patterns, with a bound depending only on \(\alpha\), even when \(n\) has several overlapping collisions. To sum \(\prod_{p\mid d}p^{-B}\) for a connected component on \(l\ge2\) vertices, root a spanning tree at its smallest prime \(p\). With an ordering of the remaining vertices compatible with this tree there are \(U^{o(1)}\) choices at each edge, and every selected prime is \(\ge p\). The sum is bounded by
\[
 U^{o(1)}\sum_{U^\alpha\le p\le2U}p^{-lB}
 \ll U^{-\alpha(lB-1)+o(1)} .
\]
At \(lB=1\) the logarithm is absorbed in \(U^{o(1)}\). Additional edges only restrict the embeddings. Different components may be bounded by a product of these positive majorants after dropping distinctness across components. A nonempty pattern therefore costs at most \(U^{-\alpha(2B-1)+o(1)}\). This proves (1). It counts actual existing edges with correctly signed inclusion–exclusion before taking absolute bounds. A test that counts each label repeatedly with its number of edges would define a different source.

For the dyadic weights \(w_J=2^{-k}/U\) at depth \(k\), their sum on a shell and a level is \(2^{s_X}/U=U^{-1+o(1)}\). Summing the square of (1), including all overlapping depths and shells, gives
\[
 \sum_{J}w_J\left|\sum_{n\in J\cap A_U}\mu_y(n)\right|^2
                \le X^{(1-2\alpha)(2B-1)+o(1)} .                \tag{2}
\]
Since \([s\,\cdot]_+\) is 1-Lipschitz for either \(s=\pm1\), the difference of the square roots of the original and complementary polarity energies is bounded by the square root of (2). At \(b>0\) this is a strict power below the original \(X^{b+o(1)}\). At \(b=0\) both energies are subpower by the same upper and the added one in the detector's logarithm. This applies to whole shells and to their original coarse nodes. The inequality need not hold on an arbitrary post-matching subset: those missing cofactor signs would alter the use of (1). The original primitive-to-node transfer is made before this decomposition.

## A sector payable even after arbitrary selections

The following different bound survives any deletion of labels, including actual spent partners. Allow a relation defined on **all** the rough prime factors, with the smaller prime \(p\) used as its distinguished endpoint. Suppose every selected pair has \(q\ge U^{1/2-o(1)}\), and each \(p\) has at most \(U^{o(1)}\) allowed partners. Full-integer counting gives at most
\[
 \sum_p \sum_{\substack{q\sim p\\q\ge U^{1/2-o(1)}}}
             \left\lfloor\frac{2U}{pq}\right\rfloor
 \le U^{1/2+o(1)}\sum_{p\le2U}\frac1p
 = U^{1/2+o(1)}
\]
labels in the shell, irrespective of sign or partners. The sum of their squared counts on **all levels** is \(U^{o(1)}\) with the native weights; use the bound by the squared full shell population on each partition and \(\sum_k2^{-k}\le2\). Thus this second collision sector can be removed from any genuine post-matching node source at subpower cost in the weighted **norm**. Its mixed term with an unrestricted complement is still present. The triangle inequality transfers a proposed cofinal subpower upper for either polarity across this deletion. In particular no hypothesis about the sign of the mixed term was used.

The first result controls a wider range of true factor relations by using signed arithmetic; the second result has a stronger absolute bound on a more restricted population and permits further selection. Neither furnishes a bound for arbitrary pairs of large primes in the genuine remaining source. RH and Step 4 are **OPEN**.
