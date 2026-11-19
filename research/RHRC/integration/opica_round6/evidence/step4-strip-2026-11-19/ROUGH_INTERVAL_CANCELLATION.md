# Unconditional cancellation in the actual rough Möbius intervals

**DERIVED on paper, 19 November 2026.** The signed quantity isolated by the OPICA graph admits a uniform bound with an arbitrary saving in powers of the logarithm on each sufficiently long interval. This uses an unconditional arithmetic theorem, separately from the detection of hypothetical zeros. It applies after imposing every one of the growing small-prime exclusions in the graph.

Fix \(0<c<1\), \(7/12<\lambda<1\), \(A>0\), and a single schedule \(Q_n=n^{2+o(1)}\). In particular one may take the graph choice \(n^2\exp(\sqrt{\log(n+2)})\). Uniformly for \(e^{cn}\le x\le e^n\) and **every** \(x^\lambda\le H\le x\), one has
\[
 \left|\sum_{\substack{x<r\le x+H\\p\mid r\Rightarrow p>Q_n}}\mu(r)\right|
 \ll_{c,\lambda,A} {H\over(\log x)^A}. \tag{1}
\]
All thresholds can depend on the fixed schedule and on \(A,c,\lambda\). Squareful endpoints retain their Möbius value zero. Every allowable squarefree endpoint retains its original sign. One may replace \(\lambda\) by any larger fixed exponent without changing the definition of the graph. The source paper also proves discorrelation with polynomial phases on longer intervals, though no such twist is needed here. [Matomäki, Shao, Tao and Teräväinen, Theorem 3.1(i)](https://arxiv.org/pdf/2204.03754#page=35)

## Proof with the complete arithmetic cutoff

Let \(g_Q(d)=1\) when all prime factors of \(d\) are \(\le Q\), and zero otherwise. Include \(d=1\) and **every positive power** of each such prime. The coefficient identity
\[
  \mu(r)\mathbf1_{\{p\mid r\Rightarrow p>Q\}} = (\mu*g_Q)(r)
\]
follows by multiplying finite prime factors at the given integer \(r\). At a small prime the formal factors \((1-z)(1-z)^{-1}=1\) cancel every positive degree. At a large prime the retained factor is \(1-z\). This identity never replaces the signed subsequence by an independent random model.

Choose \(7/12<\lambda_0<\lambda\) and \(a>0\) small enough that \(\lambda-a>(1-a)\lambda_0\). For \(d\le x^a\), set \(u=x/d,\ L=H/d\). Then \(u^{\lambda_0}\le L\le u\) with \(u\ge x^{1-a}\). For fixed \(\lambda_0>7/12\), the cited theorem yields
\[
 \left|\sum_{u<k\le u+L}\mu(k)\right|\ll_{D,\lambda_0} L(\log u)^{-D}
\]
for any \(D>0\). To stay strictly inside the paper's upper and lower length exponents even when \(L\) is close to \(u\), choose a fixed \(7/12<\lambda_1<\lambda_0\). Subdivide into equal contiguous lengths comparable to \(u^{\lambda_1}\), using \(\lceil L/u^{\lambda_1}\rceil\) pieces. All starting points lie between \(u\) and \(2u\); a small fixed margin in both exponent bounds makes every piece admissible. Add the estimates for those disjoint pieces. Summing the \(d\le x^a\) portion now costs at most
\[
 O_{D,\lambda}\!\left(H(\log x)^{-D}\prod_{p\le Q_n}(1-1/p)^{-1}\right)
       \ll H(\log x)^{-D}\log(2Q_n).
\]
The last inequality is the ordinary Mertens product bound, and \(\log Q_n\ll\log n\).

For \(d>x^a\) keep the complete divisor range \(d\le x+H\le2x\). A row contains at most \(H/d+1\) terms in absolute value. Choose once and for all \(1/2<\sigma<\lambda\). Its smooth-number product \(Z_Q(\sigma)=\prod_{p\le Q_n}(1-p^{-\sigma})^{-1}\) satisfies
\[
 \log Z_Q(\sigma)\ll_\sigma 1+\sum_{j\le Q_n} j^{-\sigma}
 \ll_\sigma Q_n^{1-\sigma}=n^{2(1-\sigma)+o(1)}=o(n).
\]
Consequently \(Z_Q(\sigma)=x^{o(1)}\) uniformly for \(x\ge e^{cn}\). Bounding the reciprocal mass above \(x^a\) by \(x^{-a(1-\sigma)}Z_Q(\sigma)\) and the number of smooth integers through \(2x\) by \((2x)^\sigma Z_Q(\sigma)\) gives
\[
  \sum_{\substack{x^a<d\le2x\\g_Q(d)=1}}(H/d+1)
   \ll Hx^{-a(1-\sigma)+o(1)}+x^{\sigma+o(1)} .
\]
Both terms save a fixed arithmetic power relative to \(H\), since \(\sigma<\lambda\) and \(H\ge x^\lambda\). They absorb any requested log power for sufficiently large \(n\). Taking \(D=A+1\) proves (1). This argument pays the added \(1\) for every large smooth divisor and does not assume cancellation in that tail.

## What (1) buys for the full graph

For a graph cell starting at \(x\) put \(B_n=\exp(n/\log(n+2))\) and \(H_x=x(\exp(1/B_n)-1)\). On the stated late range \(H_x\asymp x/B_n=x^{1-o(1)}\). Bound every prefix of length at least \(x^\lambda\) by (1), and every shorter prefix by \(x^\lambda+1\). The latter is smaller than \(H_x/(\log x)^A\) for large \(n\), uniformly on that range. Hence
\[
 \sup_{0\le h\le H_x}
     \frac{|M_{Q_n}(x+h)-M_{Q_n}(x)|}{\sqrt{x}}
 \ll_{A,c} \frac{\sqrt{x}}{B_n(\log x)^A}.                 \tag{2}
\]
This is also a signed estimate for each corresponding smooth source-weighted cell: Abel summation multiplies the supremum of the **unnormalized** partial sums by the supremum plus total variation of its actual weight. For \(w(k)=k^{-1/2}V(t-\log(sk))\), both are \(O_V(x^{-1/2})\) on the cell, uniformly in \(s,t\) when \(V,V'\) are bounded. The smooth-color factor \(\mu(s)/\sqrt s\) remains outside. All prefixes are included; no cancellation between two independent choices of endpoints is presumed.

For \(x\approx e^n\), the right side of (2) is still \(\exp(n/2-o(n))\). For every fixed \(A\), taking logarithms and dividing by \(n\) leaves the limiting upper exponent \(1/2\). The graph needs exponent **zero** at arbitrarily large common orders. Choosing \(A\) depending on \(n\) would lose the fixed threshold and implicit constant. This identifies exactly what the published short-interval theorem contributes and where it stops. The unconditional saving works on the actual signed sequence. An upper strong enough for Step 4 remains **OPEN**. [Graph definition, source projection and exact exponent](LOG_RATIO_STRIP.md)
