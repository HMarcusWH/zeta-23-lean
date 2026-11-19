# How much the actual primes pay for removing an average

**DERIVED on paper.** For the logarithmically weighted ordinary-prime area \(A_\vartheta(x)=\int_2^x(\vartheta(t)-t)\,dt\), one can improve the elementary convexity allowance on every sufficiently large scale, using the actual prime contributions on the same interval. This comparison is unconditional. Combining it with a verified zero height yields a further asymptotic extension of the finite-height sign calculation.

Let \(Y\) be any positive averaging variable with \(\mathbb EY=x\) and \(|Y-x|\le x/100\). There is a uniform estimate
\[
 \left|A_\vartheta(x)-\mathbb E A_\vartheta(Y)\right|
 \ll e^{-(\log x)^{1/4}/4}\operatorname{Var}(Y)+x^{4/3}\log x.       \tag{1}
\]
Its constant is independent of the chosen probability law. In particular the variance term has an arithmetic saving on the full, unsmoothed signed area, for each such law and every sufficiently large \(x\). At a fixed relative averaging width the right side can still exceed \(x^{3/2}\).

## The exact edges paid by the prime counts

Write \(F(x)=\sum_{p\le x}(x-p)\log p\), so \(A_\vartheta(x)=F(x)-(x^2-4)/2\). For \(h=Y-x\) the exact convexity remainder \(D_x(h)=F(x+h)-F(x)-h\vartheta(x)\) is a sum of positive prime contributions. For \(h>0\) it equals \(\int_0^h[\vartheta(x+v)-\vartheta(x)]\,dv\). For \(h<0\) it equals \(\int_0^{|h|}[\vartheta(x)-\vartheta(x-v)]\,dv\). This convention includes the correct contribution when \(x\) itself is a prime. Therefore
\[
 A_\vartheta(x)-\mathbb E A_\vartheta(Y)
 =\tfrac12\operatorname{Var}(Y)-\mathbb E D_x(Y-x).                  \tag{2}
\]
For example, if \(Y=x\pm h\) equiprobably, the exact twice-averaging defect is \(h^2-\sum_{|p-x|\le h}(h-|p-x|)\log p\). This is a triangularly weighted sum over actual ordinary primes from both sides of the cut. Discarding those positive prime contributions is exactly the loss in the elementary Jensen upper.

For \(x^{2/3}\le v\le x/100\), the prime number theorem in short intervals gives, on each side,
\[
 \vartheta(x+v)-\vartheta(x)=v+O(v e^{-(\log x)^{1/4}/4}),
 \qquad
 \vartheta(x)-\vartheta(x-v)=v+O(v e^{-(\log x)^{1/4}/4}).
\]
Here is the uniformity check. Guth and Maynard's Corollary 1.3 yields the ordinary-prime count for an interval beginning at \(z\asymp x\) of length \(w\) between \(z^{17/30+\epsilon}\) and \(z^{0.99}\), with error \(O_\epsilon(w e^{-(\log z)^{1/4}})\) against \(w/\log z\). For each of the two requested intervals, split into equal consecutive pieces of length comparable to \(x^{3/5}\). Since \(3/5>17/30\) and \(v\ge x^{2/3}\), a fixed positive margin makes each piece admissible. Multiplying its prime count by \(\log z\) and replacing the latter by the actual \(\log p\) adds at most \(O(w(w+1)/x)\), using the trivial count on the piece. These errors, the log from the count estimate, and replacement of \(z\) by \(x\) are all absorbed by the factor with exponent \(1/4\) in front of \((\log x)^{1/4}\). This argument uses actual ordinary primes and does not transfer a high-prime-power count without its correction. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=2)

Integrating from \(v=x^{2/3}\) upwards costs \(O(h^2 e^{-(\log x)^{1/4}/4})\). On the remaining prefix, the elementary bound for the prime sum is \(O((v+1)\log x)\), and the entire integrated cost is \(O(x^{4/3}\log x)\), also when \(|h|<x^{2/3}\). Substitution into (2) proves (1).

## A finite-height consequence

There is an absolute \(H_0\) such that, if \(H\ge H_0\) and all nontrivial zeros through height \(H\) are on the line, then
\[
 A_\vartheta(x)<0,\qquad A_\pi(x)<0,\qquad
 2<x\le H^4\exp\big((\log H)^{1/4}/4\big).
\]
This asymptotic assertion has no evaluated \(H_0\) here. The separate numerical result through \(1.21\cdot10^{48}\) uses explicit constants.

Use the positive averaging law and the estimates in [the band-limited proof](BANDLIMITED_THETA.md). That law has relative displacement under \(1/100\), \(\mathbb EY=x\), and \(\operatorname{Var}(Y)\ll x^2/H^2\). Independently of the variance loss, the explicit formula for the averaged area, divided by \(x^{3/2}\), gives an upper
\[
 0.04621(1.0016)-49/75
 +O\big(\sqrt{x}\,(1+\log H)/H^3+x^{-3/2}\big).
\]
The first term bounds all verified low zeros. The second term comes from the genuine proper prime powers. The high-zero error follows from the same truncated Fourier multiplier, retaining its full tail. All constants here are absolute.

For \(10^{-2}H^4\le x\le H^4\exp((\log H)^{1/4}/4)\), the error just displayed tends uniformly to zero. By (1) the cost of returning to the actual area after division by \(x^{3/2}\) is at most
\[
 O\left(\frac{\sqrt{x}}{H^2} e^{-(\log x)^{1/4}/4}+x^{-1/6}\log x\right)=o(1).
\]
Indeed \(\sqrt x/H^2\le\exp((\log H)^{1/4}/8)\) while \(\log x\ge4\log H-\log 100\). The negative margin persists. For \(x<10^{-2}H^4\), the explicit band-limited sign result applies directly with the same verified height; early \(2<x\le10^{19}\) is handled by the published pointwise comparisons. The positive-kernel [transfer to \(A_\pi\)](ORDINARY_PRIME_AREA.md) works on the entire prefix, since both ingredients have a fixed negative terminal margin for large \(x\).

**Remaining arithmetic.** Estimate (1) controls the cost of removing a smoothing, using the actual local prime counts. The finite-height sign theorem also needs the smoothed prime area itself to be negative. At unbounded \(x\), fixed verified height and the saving above do not furnish that sign at the required horizons. No off-line zeros above the verified range have been ruled out in this argument.

A falsification test makes the distinction quantitative. For fixed \(1/2<b<1\) and fixed \(\gamma\ne0\), the function \(G(x)=x^{1+b}\cos(\gamma\log x)\) has \(|G''(x)|\ll_{b,\gamma}x^{b-1}\). For every averaging law allowed in (1), Taylor's formula and \(\mathbb EY=x\) give \(|G(x)-\mathbb EG(Y)|\ll_{b,\gamma}x^{b-1}\operatorname{Var}(Y)\). This is already smaller than the variance term in (1) at late \(x\), although \(G\) has positive excursions of order \(x^{1+b}\). This is a test of the proposed inference from the averaging estimate alone. The function is not the actual prime area and is not a counterexample to RH.
