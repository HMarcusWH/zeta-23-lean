# Removing every terminal label with a small cofactor on aligned cutoffs

**DERIVED on paper.** On the actual dyadic Möbius graph there is a deterministic selector containing every nonzero label \(n\) with \(n/P^+(n)\le B\), where \(B=\lfloor 2^{s/200}\rfloor\) and \(s=\lceil\sqrt{\log_2 X}\rceil\). For all sufficiently large \(X=2^{100t}\), removing the selector and all its incident edges changes the signed covariance by \(O(\log X)\). It removes every ordinary prime and includes \(\gg X/\sqrt{\log X}\) prescribed target labels. Their compensation comes from opposite-sign labels of the original graph. The surviving signed composite covariance is **OPEN**.

## Native inputs and comparator

Write \(X=2^{100t}\), \(t\) a positive integer tending to infinity. Retain \(X^{.99}<n\le X\), with sign \(\mu_6(n)=\mu(n)\mathbf 1_{(n,6)=1}\). Both endpoints are powers of two with zero sign. The nonzero labels can therefore be partitioned into whole shells \([U,2U)\), \(U=2^j\), \(99t\le j<100t\), without any boundary correction. A base cell has length \(H_0=U2^{-s}\). A descendant of length \(H\) has weight \(w=H/(U H_0)\). The covariance counts ordered distinct pairs in each node with \(\gcd(n,r)^{100}<X\). Write \(C(E)\) for that same statistic restricted to endpoints in \(E\). Here \(C(\mathrm{all})\) includes all the native signs. [Full source and graph](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md)

In each shell the targets are \(n=ap\), where \(a\le B\) is squarefree and coprime to 6 and \(p\) is prime. The sign is \(-\mu(a)\). At these scales \(p>B^{100}\) and it is uniquely the largest prime factor. The same holds for the following two disjoint pools of possible partners.

For each squarefree \(m\) coprime to 30 with \(B<m\le B^{100}/5\), use cofactors \(m\) and \(5m\), assigning each to its native sign. These cofactors are uniquely distinguished by divisibility by 5. Each sign receives reciprocal mass at least
\[
 \frac15\sum_{\substack{B<m\le B^{100}/5\\(m,30)=1}}\frac{\mu^2(m)}m
 =\bigl(99c_{30}/5+o(1)\bigr)\log B,\qquad
 c_{30}=\frac8{30}\prod_{p\ge7}(1-p^{-2}).
\]
The usual square-divisor expansion of \(\mu^2\) and partial summation give this density and the reciprocal sum. In particular \(\prod_{p\ge7}(1-p^{-2})\ge\prod_{n\ge7}(1-n^{-2})=6/7\), so the coefficient exceeds 4. The reciprocal mass of either target sign is at most \(1+\log B\). This fixed slack allows a fixed small relative error, say \(1/10\), in each prime progression count (ordinary primes in a rescaled interval). Since \(m\le B^{100}=U^{o(1)}\), replacing \(\log(U/m)\) by \(\log U\) costs \(1+o(1)\) uniformly. Distinct cofactor slots produce disjoint source labels because the largest factor is unique. On a node with the stated relative precision in every cofactor count, each sign pool therefore outnumbers its opposite-sign targets.

For any selected \(n=ap\), \(a\le B^{100}\le 2^{s/2}\), one has \(p\ge U/2^{s/2}>H_0\). A distinct row \(r\) sharing any base cell with \(n\) satisfies \(0<|r-n|<H_0\), so \(p\nmid r\) and \(\gcd(n,r)\mid a<X^{.01}\). Every actual off-diagonal edge touching a selected row passes the original mask, including those with an arbitrary unselected cofactor.

## Short intervals and their exceptional cells

Use \(\nu(v)\) for the exceptional-measure exponent of the prime number theorem on variable windows \((z,z+z^v]\), as defined by Gafni and Tao. Their Theorem 1.2 and the discussion following (1.8) imply \(\nu(.49)<1\) unconditionally. Choose \(0<c<.002\) with \(\nu(.49)<1-4c\), and set \(\eta=c/4\). For \(v=.5+\eta/2\), Lemma 1.1(iii) gives \(\nu(v)\le3(1-v)/2<.75\). This second estimate is used strictly above \(1/2\). The proof also uses Guth and Maynard's all-interval prime number theorem for lengths at least \(z^{17/30+\epsilon}\). [Gafni and Tao, Definition 1.1, Lemma 1.1 and Theorem 1.2](https://arxiv.org/pdf/2505.24017) · [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552)

Here is the conversion from exceptional real starting points to aligned cells of the graph. For a cofactor \(a\) and a partition into integer cells of length \(H\), work at \(V=U/a\) on the disjoint scaled intervals \(I\) of length \(H/a\). Define
\[
 F(z)=z^{-v}\sum_{z<n\le z+z^v}\Lambda(n).
\]
For \(I\subset[V,2V]\),
\[
 \int_I F(z)\,dz=\sum_{n\in I}\Lambda(n)
  +O\bigl(V^v\log V+|I|V^{v-1}\log V+\log V\bigr).
\]
Indeed, away from endpoint strips of length \(O(V^v)\), the integral of \(z^{-v}\) from the unique solution of \(z+z^v=n\) up to \(n\) is \(1+O(V^{v-1})\). The trivial bound \(\Lambda(n)\le\log(3V)\) pays both strips and all endpoint conventions. If \(H/a\ge V^{v+\epsilon}\), this error is \(o(|I|)\). The proper prime powers in \(I\) have total weight \(O((1+|I|/\sqrt V)\log^2 V)\): for each integer exponent \(k\ge2\), consecutive integer \(k\)-th powers have spacing \(\gg\sqrt V\) there, and only \(O(\log V)\) exponents occur. Since \(\log p=\log V+O(1)\) in that shell, failure of a \(1/10\) relative prime-count estimate entails a fixed positive relative failure in the integral.

We have \(0\le F\ll\log V\). Therefore a defective cell contains \(\gg |I|/\log V\) points by measure at which \(|F-1|\) exceeds a fixed small constant. Definition 1.1 bounds the total measure of these points by \(O_\xi(V^{\nu(v)+\xi})\) for each fixed \(\xi>0\). Undo the scaling and take a union over the at most \(B^{100}=U^{o(1)}\) cofactors. The total *integer cell length* of defective cells is \(\ll_\xi U^{\nu(v)+\xi}\), increasing the preliminary loss slightly. This transfer justifies counting the actual dyadic intervals, even though their endpoints have zero Lebesgue measure.

## Three nested matchings

Choose three dyadic lengths
\[
 H_1=2^{\lfloor(\log_2 H_0)/2\rfloor},\qquad
 H_2=2^{\lfloor(.5+\eta)j\rfloor},\qquad
 H_3=2^{\lfloor .58j\rfloor}.
\]
Eventually \(H_1<H_2<H_3\le H_0\). Process the \(H_1\)-cells, then the \(H_2\)-cells, then the \(H_3\)-cells. In each cell match remaining target labels of either sign to remaining pool labels of opposite sign, in increasing numerical order in each list. Previously matched pairs are retained. Because every earlier pair within a larger cell debits the opposite pool and target by exactly one each, the raw surplus test also suffices at every later stage.

At the first scale \(H_1/a=(U/a)^{.5-o(1)}\). The transfer at \(v=.49\) leaves at most \(K_1\ll U^{1-3c}\) unmatched targets in the shell; count even every integer in every defective cell. At the middle scale \(H_2/a=(U/a)^{.5+\eta-o(1)}\). The transfer at \(v=.5+\eta/2\) leaves at most \(K_2\ll U^{.76}\) unmatched targets. At \(H_3\), every rescaled cell has length exceeding \((U/a)^{17/30+.005}\) for large \(U\). The cited all-interval theorem gives the required uniform relative estimates at all starts and all cofactors. Thus **every target acquires a partner**. Let \(S\) be the union of both endpoints of every match, and \(R\) its complement.

For any node \(J\), put \(s_J=\sum_{n\in J\cap S}\mu_6(n)\) and \(r_J=\sum_{n\in J\cap R}\mu_6(n)\). The mask observation gives the exact node difference before multiplication by \(w\),
\[
   s_J^2+2s_Jr_J-\#(S\cap J).
\]
The diagonal deductions cost at most \(2\) per shell summed over all depths. For \(H\le H_1\) the absolute edge mass, even before matching, costs \(O(H_1^2/H_0)=O(1)\) per shell by the geometric sum over dyadic lengths. For \(H_i\le H< H_{i+1}\), all pairs finished at stages through \(i\) cancel in their node. Hence \(\sum_J |s_J|\le2K_i\) over nodes of that length, including partners first selected later. Since \(|r_J|,|s_J|\le H\), the total contribution of the two quadratic terms at those scales costs
\[
 O\left(\frac{K_i H_{i+1}^2}{U H_0}\right).
\]
At \(i=1\) the exponent in \(U\) is at most \(-3c+2\eta+o(1)<0\). At \(i=2\) it is at most \(.76+1.16-2+o(1)<0\). For \(H\ge H_3\), \(s_J=0\) exactly. Summing the bounds proves
\[
       \boxed{|C(\mathrm{all})-C(R)|\ll \log X,\qquad X=2^{100t}.}
\]
There is no postulated independence of labels or of prime fluctuations in neighboring cells. The large prime in \(ap\) supplies the full mask calculation, and only the complete signed sum of incident terms was retired.

## Size and the open remainder

In the last whole shell \(U=X/2\), the number of targets is \(\gg U\log B/\log U\). Indeed the ordinary prime number theorem on \([U/a,2U/a)\) holds uniformly for \(a\le B\) since \(U/B\to\infty\). The reciprocal mass of squarefree cofactors coprime to 6 through \(B\) is asymptotic to \(c_6\log B\), \(c_6>0\). Thus there are \(\gg X/\sqrt{\log X}\) distinct targets. As a signed falsification check, the selected *prime–prime* piece alone is \(\gg U/(2^s\log^2 U)=X^{1-o(1)}\): distribute the \(\asymp U/\log U\) primes over the \(2^s\) base cells and apply Cauchy to their counts, subtracting the diagonal. All such distinct pairs have gcd one. Their much larger positive contribution requires the opposite-sign incidence in the theorem.

Every nonzero survivor has \(n/P^+(n)>B\). Some labels with still larger cofactors were spent as partners. The comparator is precisely the complement of this deterministic selector. Replacing it by every label with \(n/P^+(n)>B\) would add those partners back and does not follow from the argument. No bound on the signed covariance between the survivors was established. The graph comparison holds on the displayed aligned cofinal sequence. No new Lean compilation, production workflow result, or Step 4 closure is claimed.

## Compatibility with the all-rough source

The same signed retirement applies inside the all-rough graph with \(y=\lceil\log_2 X\rceil^2\) and \(P^-(n)>y\). This needs different partner pools because 5 is excluded. Put \(z=y^2\). The rough target cofactors \(a\le B\) have total reciprocal mass at most
\[
 \prod_{y<p\le B}(1+1/p)\le (1+o(1))\,\log B/\log y
\]
by Mertens' prime-product theorem. For the pools use squarefree \(z\)-rough \(m\in(B,B^{100}/z]\). Offer \(m\) and every \(\ell m\) with \(y<\ell\le z\) prime. The second family has a unique prime in \((y,z]\) and its sign is opposite to the first. For each \(m\), both signs therefore receive reciprocal mass at least \(\min(1,\sum_{y<\ell\le z}1/\ell)/m=(\log 2+o(1))/m\).

To count this supply, put \(V(z)=\prod_{p\le z}(1-1/p)\). Uniformly for \(T\ge B\), the proportion of integers through \(T\) having no prime factor through \(z\) is
\[
 V(z)+O((\log z)^{-3}+z^{k+1}/T),
 \qquad k=\lceil20(1+\sum_{p\le z}1/p)\rceil.
\]
Indeed, truncate inclusion and exclusion at two consecutive parities. The difference of their Euler sums is at most \((\sum_{p\le z}1/p)^k/k!\), up to changing the index by one. This is \(O((\log z)^{-3})\) by the prime harmonic estimate. The accumulated floor errors cost \(O(z^{k+1})\) since each squarefree divisor indexed here is at most \(z^{k+1}\). We have \(z^{k+1}=B^{o(1)}\). Removing squares of primes above \(z\) costs at most \(T\sum_{d>z}d^{-2}=O(T/z)\). Partial summation and \(V(z)\sim e^{-\gamma}/\log z\) give a squarefree reciprocal supply of \((99+o(1))V(z)\log B\) from these \(m\). Hence **each** sign pool has at least \((99e^{-\gamma}\log(2)/2+o(1))\log B/\log y\), more than ten times the upper on either target sign.

Every partner and target is now genuinely \(y\)-rough, and every cofactor still lies below \(2^{s/2}\). All three interval, mask and incidence arguments apply unchanged to the restricted graph, including all its residual cross terms. Consequently the all-rough comparison costs \(O(\log X)\) on the same cutoffs and every nonzero survivor satisfies both \(P^-(n)>y\) and \(n/P^+(n)>B\). This combines with the separate paper result that the all-rough primitive graph retains the exponent of the Step 4 obstruction. The remaining composite covariance still needs an independent upper. [All-rough detector](ROUGH_PRIME_TRANSPORT.md)

## Finite implementation check

At \(X=16384,32768\) exact pair enumeration independently agreed with the node identity after subtracting the signed gcd defects. The original cap is 1 in both fixtures. In the second, 197 prime–semiprime pairs were matched and 5,524 distinct incident pairs failed that cap. Their signed defect was \(-115763/524288\), changing the incidence from \(-93431/2097152\) before masking to \(369621/2097152\) after masking. An explicitly auxiliary cap of 13 retained every incident pair at each cutoff. Both runs use genuine integer labels on the published native tree and deliberately small test pools and matching scales. Their leftover primes and sign changes illustrate why small-cutoff results cannot certify the asymptotic cofactor or supply estimates. [Independent enumeration](check_prime_split.py) · [Exact receipts](PRIME_SPLIT_CHECK.json)
