# The positive and negative arithmetic inside the first numerator

19 November 2026. **DERIVED on paper.** In the [single-harmonic calculation](ONE_HARMONIC_ZERO_DETECTOR.md) the two signs of the individual arithmetic summands each contribute a fixed positive multiple of \(L^2\), for every sufficiently large cutoff. Their signed difference has the smaller, zero-sensitive growth law derived there. This calculation quantifies the cancellation the desired upper would require at the actual site.

Keep \(a=24/25,\ c=21/20,\ n_L=\lfloor cL\rfloor\), and \(aL<q\le L,\ (q,6)=1\). Let \(A_+(L)\) and \(A_-(L)\) sum respectively the positive part and the negative part of each conjugate-paired row. The cosine is uniformly positive on this interval for large \(L\), so the sign is determined by \(\mu(q)\). Then
\[
 A_+(L)\sim A_-(L)\sim
 \left(\frac{3}{4\pi^4}\int_a^1 u\cos(2\pi c/u)\,du\right)L^2 .
\]
Indeed, among integers prime to 6 the squarefree ones have density
\[
 (1-\tfrac12)(1-\tfrac13)\prod_{p\ge5}(1-p^{-2})
   = \frac1{2\zeta(2)}=\frac3{\pi^2}.
\]
For a direct proof, expand the squarefree indicator as \(\sum_{d^2\mid q}\mu(d)\); for \(d\) coprime to 6 the secondary count is \(x/(3d^2)+O(1)\). Summing \(d\le\sqrt x\) gives the density with \(O(\sqrt x)\) counting error. The signed Möbius count on the same coprime set is \(o(x)\) by ordinary PNT: expand it as \(\sum_{i,j\ge0}M(x/(2^i3^j))\), truncate the absolutely summable geometric weights and use \(M(y)=o(y)\) on the finite prefix. The identities \(\mathbf1_{\mu=\pm1}=(\mu^2\pm\mu)/2\) now give each sign density \(3/(2\pi^2)\). Partial summation with the smooth weight \(u\cos(2\pi c/u)\) gives the asserted limits. The rounding and sine-normalization errors are \(O(L)\) even if every eligible denominator is counted in absolute value.

A bound \(|A_+(L)-A_-(L)|\ll_\epsilon L^{3/2+\epsilon}\) would require relative precision \(O_\epsilon(L^{-1/2+\epsilon})\) compared with either mass. The preceding counting proof gives convergence of their ratio to one; it supplies no such rate. The merged repository's Mertens first theorem controls a different sum, weighted by the von Mangoldt function divided by \(n\). Its receipt cannot be substituted for this signed cancellation. [Pinned Lean theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/Chebyshev.lean#L509)
