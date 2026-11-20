# Combining the marked divisors with the residue classes

**Paper calculation.** Write \(U,P,V_y,c_r\) as in the [same-group covariance note](ROUGH_CORE_PHASE_TRANSITION.md). This extends the marked common-divisor argument to a permuted vector of residue classes. It reduces the missing signed arithmetic upper to coprime, comparable squarefree pairs whose difference lies in a single growing progression.

For a large integer \(n\), let \(y=\lfloor\log\log n\rfloor\), \(q=2^{\lfloor\sqrt n\rfloor}\), \(\sigma=1/\sqrt{\log y}\). Use the whole damped history space \(L^2([0,n],e^{-2\sigma t}dt;\ell^2((\mathbb Z/q)^\times))\), extending histories by zero at negative times. Every active rough core is coprime to \(q\). Define the vector \(G_h(t)=\sum_{r\equiv h(q)}c_r(t)\), and let \(\Pi_v\) send coordinate \(h\) to \(vh\) modulo \(q\) for \((v,q)=1\). The commuting operators \(B_p=p^{-1/2}\tau_{\log p}\Pi_p\) for \(p>y\) obey \(\|B_p\|\le p^{-1/2-\sigma}\).

For squarefree \(u\) whose prime factors exceed \(y\), mark the sum over \(u\mid r\) in each residue class to obtain \(G^{[u]}\). The exact squarefree factorization gives
\[
 G^{[u]}=\mu(u)\left(\prod_{p\mid u} B_p(I-B_p)^{-1}\right)G .
\]
Indeed \(G=\prod_{p>y}(I-B_p)\boldsymbol e_1 V_y\) on the finite horizon; only primes \(p\le e^{n+s}\) can act there, and the coefficient is zero before the causal gap. Marking \(p\) retains only the term \(-B_p\) of that factor. Each inverse is given by a locally finite geometric series, or converges by its operator norm. The norm of \(\Pi_p\) is one, so no ambient \(\phi(q)\) enters this marking bound.

In the energy summed over classes, the signed contribution \(H\) of pairs sharing a prime (including \(r=r'>1\)) is exactly
\[
 H=-\sum_{u>1\text{ squarefree rough}}\mu(u)\|G^{[u]}\|^2 .
\]
Consequently
\[
 |H|\le\delta_n\|G\|^2,\quad
 1+\delta_n=\prod_{p>y}
 \left(1+\frac{p^{-1-2\sigma}}{(1-p^{-1/2-\sigma})^2}\right).
\]
Since \(\sum_{k>y}k^{-1-2\sigma}\ll y^{-2\sigma}/\sigma\), \(\delta_n=o(1)\). Thus if \(K\) denotes the same-residue *coprime* contribution, \(K=\|G\|^2-H\ge(1-\delta_n)\|G\|^2\). Positivity here is a consequence of bounding the complete signed marked contribution by the vector norm. It need not hold pairwise.

Cauchy across the \(\phi(q)\) classes gives the following actual-source estimate, with finite horizon and all terms priced,
\[
 \int_0^n P(t)^2dt
 \le \frac{e^{2\sigma n}\phi(q)}{1-\delta_n}
   \int_0^n e^{-2\sigma t}
   \sum_{\substack{(r,r')=1\\r\equiv r'(q)}}c_r(t)c_{r'}(t)\,dt .
 \tag{1}
\]
The prefactor is \(\exp(o(n))\). Within (1) the sole diagonal is \(r=r'=1\). Its integral is \(\le n\exp(O_j(\sqrt y))\) by the bounded drive and the elementary absolute filter estimate.

For any prescribed \(B>0\), the terms with either core less than \(e^t/(K n^2 P_y)\) cost \(O_B(e^{-Bn})\) uniformly after increasing the fixed \(K\). In fact for such an \(r\), every \(a=rd\) with \(d\mid P_y\) has \(a<e^t/(Kn^2)\). Since the rough/smooth split is unique,
\[
 \sum_{\mathrm{small}\ r}|c_r(t)| \le
 \sum_{a<e^t/(Kn^2)}a^{-1/2}|U(t-\log a)|
 \ll (1+n)^2 e^{n/2-c\sqrt K n}.
\]
The sum of absolute weights over all other \(r\) is \(O_j(e^{n/2})\) on \(0\le t\le n\) by boundedness of \(U\) and the same unique factorization. This proves the removal both pointwise and after the damped integration, even multiplied by the prefactor in (1). Every surviving core is \(\le e^{t+s}\) by causality, giving \(r/r'\) and \(r'/r\le e^s Kn^2P_y=n^{2+o(1)}\).

Now fold by \(m=rr'\). Each contributing \(m\) is odd, squarefree and rough. Using \((r,r')=1\), the product \(\mu(r)\mu(r')=\mu(m)\) is independent of the divisor allocation, with its genuine sign retained. The equal residue condition gives \(r^2\equiv m\pmod q\). At \(q=2^a\), \(a\ge3\), any soluble such congruence has at most four odd classes. Indeed the ratio of two roots satisfies \(x^2\equiv1\). The consecutive even numbers \(x-1,x+1\) have gcd 2, forcing one to be divisible by \(2^{a-1}\). The two possibilities \(x\equiv\pm1\) modulo \(2^{a-1}\) give four classes modulo \(2^a\). Thus a cofinal one-sided subexponential upper for only the remaining \(\mu(m)\)-weighted sum over these allocations would close the complete-source bound. The proof uses all signs in the residues and the marked estimate. No independent such upper has been found.
