# Polynomial cofactor matching and the large common prime

**DERIVED on paper.** On the aligned horizons \(X=2^{100t}\), a fixed positive proportion of the genuine rough squarefree labels can be removed from the signed tree, including every label with cofactor \(n/P^+(n)\le X^\kappa\). One explicit comparator restores the signed common-large-prime pairs of the surviving labels. This comparator retains the full zero exponent for any sufficiently small fixed \(\alpha>0\), even if the displacement of a hypothetical rightward zero is much smaller than \(\alpha\). A comparison for the original primitive mask alone has the separate error in (5). The bound on the remaining signed source is **OPEN**.

Use the tree, three nested matching scales and actual prime counts of [PRIME_SPLIT.md](PRIME_SPLIT.md), and the rough zero detector of [ROUGH_PRIME_TRANSPORT.md](ROUGH_PRIME_TRANSPORT.md). Let \(U=2^j\) run over the whole terminal shells, \(X^{.99}\le U<X\). Write \(h=\log U/\log X\), \(y=\lceil\log_2 X\rceil^2\), \(A=X^\kappa\), \(M=X^\alpha\). All labels here are squarefree, have least prime factor greater than \(y\), and carry their actual Möbius sign. Fix \(\kappa,\alpha\) before \(X\), with
\[
             0<\kappa<\alpha,\qquad 2\kappa-\kappa^2<\alpha,\qquad
             \alpha/.99<\eta/10,
\]
where \(0<c<.002,\ \nu(.49)<1-4c,\ \eta=c/4\) are fixed as in the earlier proof. A convenient choice is \(\kappa=.49\alpha\). All targets have unique form \(n=mp,\ m\le A\); the partner pool consists of all such labels with \(A<m\le M\). In this range \(p\) is prime and exceeds \(2M\) for large \(X\). Every distinct eligible cofactor slot produces disjoint source labels.

## Opposite signs are genuinely available at polynomial scale

Put \(\mu_y(m)=\mu(m)\mathbf1_{P^-(m)>y}\), with \(\mu_y(1)=1\), and \(V(y)=\prod_{p\le y}(1-1/p)\). A signed bound independent of the upper cutoff is
\[
 \left|\sum_{m\le Z}\frac{\mu_y(m)}m\right|\le 2V(y)^{-1}
           \ll\log y.                                                \tag{1}
\]
Indeed \(\sum_{n\le u}\mu(n)\lfloor u/n\rfloor=1\) for \(u\ge1\). Replacing the floor by \(u/n+O(1)\) gives \(|\sum_{n\le u}\mu(n)/n|\le1+1/u\). Convolve \(\mu\) with the indicator of the positive integers supported on primes at most \(y\); the result is exactly \(\mu_y\), and the sum of reciprocals of all these smooth numbers is \(V(y)^{-1}\).

For \(\exp(\sqrt{\log X})\le Z\le 2X\), elementary truncated inclusion and exclusion as in [the rough-pool count](PRIME_SPLIT.md) gives
\[
 \sum_{m\le Z}|\mu_y(m)|
 = Z\bigl(V(y)+O((\log y)^{-3}+1/y)\bigr)+O(y^{k+1}),
 \quad k=\lceil20(1+\sum_{p\le y}p^{-1})\rceil .
\]
Both bounding parities may be used, changing \(k\) by one if necessary and taking the larger floor-error power. Indeed \(y^{k+2}=\exp(O(\log\log X\log\log\log X))\). Removing repeated large prime factors costs \(Z\sum_{d>y}d^{-2}=O(Z/y)\). These errors are \(o(ZV(y))\) uniformly on the indicated range. Earlier cofactors have harmonic mass \(O(\sqrt{\log X})=o(V(y)\log X)\). Partial summation, Mertens' prime-product theorem, and (1) show that on a fixed exponent band \(X^u<m\le X^v\), \(0\le u<v\le\alpha\), **each** of the two signs has reciprocal mass \((\tfrac12+o(1))V(y)(v-u)\log X\). The single cofactor 1 can be included in the first band.

In a node of length \(H\) satisfying the individual prime count estimates, the predicted count divided by \(H\), for either sign on this cofactor band, is
\[
  \sum_{\substack{X^u<m\le X^v\\{\rm that\ sign}}}
      \frac1{m\log(U/m)}
 =\left(\frac12+o(1)\right)V(y)\log\frac{h-u}{h-v}.                 \tag{2}
\]
This follows by partial summation of the harmonic counts, or by partition into fixed exponent intervals and passage to the Riemann integral. The estimate is uniform for \(h\in[.99,1]\) because \(h-\alpha\) has a fixed positive lower bound. Each pool sign exceeds the opposite target sign when \((h-\kappa)^2>h(h-\alpha)\). The assumed \(\alpha>2\kappa-\kappa^2\) gives a uniform strict margin. Pick the fixed relative tolerance in the prime counts small enough for that margin before applying the short-interval theorems.

In the entire last shell, the ordinary prime number theorem gives the same counts with relative error \(o(1)\), uniformly for \(m\le M\). Thus the target fraction among rough squarefree labels tends to \(-\log(1-\kappa)>0\) there. This is also the limiting fraction over the whole terminal interval: restrict to any fixed number of final shells, where \(h\to1\); the discarded earlier geometric tail has relative size \(O(2^{-j_0})\) after keeping \(j_0\) shells by the same uniform rough count. Each matched target spends one distinct additional label, so the selected fraction tends to \(-2\log(1-\kappa)\). The density among all integers tends to zero with \(V(y)\).

## The three actual scales and their exceptional cells

Write \(\lambda=\alpha/.99\), so \(m\le U^\lambda\). The count-to-measure conversion of [PRIME_SPLIT.md](PRIME_SPLIT.md) gives, for a fixed cofactor \(m\), total defective cell length
\[
 \ll_\xi m(U/m)^{\nu(v)+\xi}\log U
\]
whenever \(H/m\ge (U/m)^{v+\xi'}\) for some fixed \(\xi'>0\). The spatial cells for each cofactor are disjoint; an exceptional cell contains a fixed proportion divided by \(O(\log U)\) of bad Lebesgue starting points after scaling by \(m\). Use real-variable exceptional sets and the endpoint-strip and prime-power errors established in that paper. If \(\nu(v)\) is negative or infinite in the favorable direction, use any stated larger positive exceptional exponent instead. Summing over all \(m\le M\), a positive exceptional exponent \(\nu_0\ge\nu(v)\), \(\nu_0<1\), gives
\[
 \ll_\xi U^{\nu_0+\lambda(2-\nu_0)+O(\xi)}.                        \tag{3}
\]
The constants use a single fixed \(v,\xi,\xi'\), and count tolerance per stage; every scaled \(U/m\) tends to infinity uniformly. This estimate takes the actual union over polynomially many cofactors.

At \(H_1=2^{\lfloor(\log_2 H_0)/2\rfloor}=U^{1/2-o(1)}\), \(v=.49\) works since \((.5-\lambda)/(1-\lambda)>.49\). Use \(\nu_0=1-4c\), then a sufficiently small \(\xi\); at most \(O(U^{1-3c})\) target labels remain unmatched. At \(H_2=2^{\lfloor(.5+\eta)j\rfloor}\), use \(v=.5+\eta/2\); the length margin follows from \(\lambda<\eta/(1-\eta)\). The Gafni–Tao bound \(\nu(v)\le3(1-v)/2<.75\) gives \(O(U^{.76})\) remaining targets by (3). Finally \(H_3=2^{\lfloor.58j\rfloor}\) gives \((.58-\lambda)/(1-\lambda)>17/30+.005\). Uniform prime counts in every rescaled interval guarantee that all remaining targets are matched. The strict all-interval margin also absorbs dyadic floors and the fixed-ratio change in starting point within \([U/m,2U/m]\). The two cited results concern ordinary prime intervals, with conversion from von Mangoldt weight and endpoints as in the earlier paper. [Gafni and Tao, Definition 1.1, Lemma 1.1 and Theorem 1.2](https://arxiv.org/html/2505.24017v1) · [Guth and Maynard, Corollary 1.3](https://arxiv.org/html/2405.20552v2)

Match in increasing order as in the earlier paper, preserving earlier pairs. A match debits one target and one opposite pool within the same parent cell. The signed sum of all edges incident to the selected set in the *unmasked* interaction has cost \(O(\log X)\). The fine scales cost \(O(1)\) per shell. For \(H_i\le H<H_{i+1}\) the error costs \(O(K_i H_{i+1}^2/(U H_0))\), with \(K_1\ll U^{1-3c}\), \(K_2\ll U^{.76}\). The exponents are at most \(-3c+2\eta+o(1)\) and \(.76+1.16-2+o(1)\). At \(H\ge H_3\) the selected charge cancels exactly inside every node. The diagonal of the selected labels costs \(O(\log X)\). This calculation also applies whenever every off-diagonal edge incident to a selected label is admitted and all other edges are treated the same before and after deletion.

## Which common-prime pairs matter?

Let \(C(G)\) denote the native small-GCD covariance on \(G\), let \(G\) be the entire rough graph, and let \(R\) be the unselected labels. The mask is \(\gcd(n,r)<X^{.01}\). If \(n=mp\) is selected then \(m\le M<X^{.01}\). An incident off-diagonal edge fails the original mask exactly when \(p\mid r\). Indeed otherwise its GCD divides \(m\), while \(p\ge U/M>X^{.01}\). Such edges can occur at polynomial cofactor scale. In a node of length \(H\), each selected \(n\) has at most \(2H/p\) distinct neighboring multiples. There are at most \(U\) selected endpoints in its shell. With weight \(H/(UH_0)\) and a geometric sum over the lengths, their unsigned cost per shell is \(O(M H_0/U)=O(M2^{-s})\). Hence
\[
 |C(G)-C(R)|\ll (1+M2^{-s})\log(2X),\qquad M=X^\alpha.            \tag{5}
\]
This suffices to preserve the off-line exponent \(2b\) for fixed \(\alpha<2b\). With \(\alpha\) chosen below a prescribed error exponent, (5) gives the corresponding tolerance-dependent bound and selector. A single fixed positive \(\alpha\) cannot be made smaller than every requested loss.

There is a sharper signed comparison. In each shell restore exactly those distinct originally excluded pairs that share a prime \(p\ge U/M\). Denote their signed weighted sum on any vertex set \(T\) by \(D(T)\). Here every such \(p\) automatically exceeds the GCD cutoff; two endpoints cannot share two such primes since \((U/M)^2>2U\). All the incident edges of selected vertices are now admitted. The complete comparison becomes
\[
        |(C(G)+D(G))-(C(R)+D(R))|\ll\log(2X).                      \tag{6}
\]
The full-source correction obeys an independent signed upper for \(b=B-1/2\),
\[
                    |D(G)|\ll_\epsilon X^\epsilon M^{2b}.         \tag{7}
\]
For fixed \(p\) in one shell write \(n=pm\) with \(m\le2M<p\). The source sign is \(-\mu_y(m)\). In a node \(J\) the ordered distinct contribution equals \((\sum_{m\in J/p}\mu_y(m))^2-\sum_{m\in J/p}|\mu_y(m)|^2\). At a fixed shell-depth, \(J/p\) runs through disjoint cells of width \(H/p\) in a shell of size \(W=U/p\ge1/2\). The proof of [the maximal disjoint-interval bound](TREE_INTERVALS.md) gives
\[
            \sum_J\left|\sum_{m\in J/p}\mu_y(m)\right|^2
               \ll_\epsilon X^{o_\epsilon(1)} W^{2B+\epsilon}.
\]
The same holds for clipping each \(J/p\) by a fixed upper or lower cofactor cutoff. In the contour proof, on any fixed \(\sigma>B\) use the factor \(\prod_{\ell\le y}(1-\ell^{-\sigma})^{-1}=\exp(o_\sigma(\log X))\), by \(\sigma>1/2,\ y=(\log X)^{2+o(1)}\). If \(B=1\), or \(W<2\), or \(H/p<1\), the corresponding counting estimate suffices. Sum over \(p\ge U/M\) using integer majorization. For \(\epsilon>0\),
\[
  \sum_{U/M\le p\le 2U}(U/p)^{2B+\epsilon}
       \ll_\epsilon U M^{2B-1+\epsilon}.
\]
The weighted diagonal costs \(O(\log X)\) since each shell label has at most one such prime. The weight \(2^{-k}/U\) sums geometrically over depths. Decreasing preliminary losses proves (7). The same estimate bounds the complete signed large-prime incidence of *any fixed cofactor interval of targets*: the mixed full-versus-clipped product is bounded by Cauchy and the two corresponding interval-square estimates. A fixed finite union incurs only a fixed factor.

By the genuine rough detector, for \(b>0\) one has \(C(G)=X^{2b+o(1)}\) at every aligned horizon. Since \(\alpha<1\), (6)–(7) give
\[
             1+[C(R)+D(R)]_+=X^{2b+o(1)}                           \tag{8}
\]
for every \(b\ge0\); for \(b=0\) use the subpower upper and the baseline one. Thus an independent cofinal subpower upper on this explicit corrected survivor graph suffices. The original small-GCD covariance is visible as \(C(R)\) in (8). The correction \(D(R)\) consists solely of the actual signed common-large-prime pairs among survivors. It is bounded below by minus the \(O(\log X)\) diagonal cost, since its fibre expressions are charge squares less their diagonals. An upper for the thinned fibre squares does not follow from (7): matching can leave scattered cofactor subsets inside individual \(J/p\). The remaining arithmetic obligation is an upper for the sum in (8), or an independent control of those surviving fibre charges together with the primitive composite covariance. No such bound, new Lean theorem, or Step 4 closure was obtained here.
