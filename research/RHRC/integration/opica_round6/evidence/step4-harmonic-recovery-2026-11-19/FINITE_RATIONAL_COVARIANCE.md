# An all-cutoff finite bound for the rational covariance

**DERIVED.** The rational graph itself admits the following finite coverage, independently of sampled signs:
\[
 |\mathcal C(X)|\le220000\,J_X(1+\log X)
 \quad\text{for every integer }2\le X\le10^{16}.
\]
Here \(J_X\) is the number of occupied bins in RATIONAL_SIGNED_COVARIANCE.md, at most \(2^s(1+\log_2X)\). Counting every nonempty geometric bin instead is also valid. The right side has subpower growth as a function of \(X\). The proved range of this inequality is finite. The factor is a conservative analytic constant.

On the indicated range \(1<X^{1/100}<2\), so the retained pairs are exactly the relatively prime pairs in each bin. No label equals 1. The off-diagonal ordered sum in \(\mathcal C\) is therefore the entire ordered coprime sum: there are no coprime diagonal pairs.

Write \(G(l)=\prod_{p\mid l}(1-p^{-1/2})^{-1}\). The published \(|M(u)|\le0.571\sqrt u\) for \(33\le u\le10^{16}\), combined with the checked table \(|M(u)|\le\sqrt u\) below 33, implies
\[
 \left|\sum_{n\le y,\,(n,l)=1}\mu(n)\right|\le G(l)\sqrt y
 \qquad(1\le y\le10^{16}).
\]
Expand by the nonnegative Euler-factor removal convolution. Every ordinary Mertens input in that expansion is \(\le y\). [Hurst's exhaustive computation](https://arxiv.org/abs/1610.08551) · [Explicit bound (A6)](https://www.tandfonline.com/doi/full/10.1080/10586458.2025.2483942?src=exp-la)

Expand the coprimality indicator as in the preceding paper. For \(e\) squarefree and coprime to six, a term of order \(n\) in a bin is
\[
 \sum_{ek\in\mathcal I,\,(k,6e)=1}\mu(k) z_{ek}^n .
\]
The weight decreases across the bin, from at most \(2^{-n}\) to a nonnegative endpoint; use weight 1 at order zero. A restricted prefix difference from the beginning of the bin has absolute size at most \(2G(6e)\sqrt{Q/e}\). The actual prefix endpoints are \(\le X/e\) even when the exclusive edge \(Q>X\). Positive summation by parts gives the same upper times \(2^{-n}\) for the displayed weighted sum. Squaring, multiplying by \(2^n/Q\), summing \(n\ge0\), then taking absolute values of the exterior \(e\) coefficients gives for each bin at most
\[
 8\sum_{\substack{e\le X\\(e,6)=1}}\frac{G(6e)^2}{e}.
\]
For \((e,6)=1\), \(G(6e)=G(6)G(e)\), with \(G(6)<8.1\). Expand
\(G(e)^2=\sum_{d\mid e}h(d)\), where \(h\) is nonnegative, supported on squarefree \(d\), and \(h(p)=(1-p^{-1/2})^{-2}-1\). Summing reciprocals yields
\[
 \sum_{e\le X,\,(e,6)=1}G(e)^2/e
 \le(1+\log X)\prod_{p\ge5}(1+h(p)/p)\le(1+\log X)e^6 .
\]
Indeed \(h(p)\le6/\sqrt p\) for \(p\ge5\), and \(\sum_{n\ge5}n^{-3/2}\le\int_4^\infty t^{-3/2}dt=1\). Now \(8(8.1)^2 e^6<220000\). All rows retain their actual labels and all coprime pairs. This interval proof and the exact finite sign controls address different questions. Neither supplies unbounded cutoffs.
