# The critical prime-factor inequality through a larger finite range

**DERIVED on paper.** The [weighted criterion](WEIGHTED_PRIME_FACTOR_CRITERION.md) at \(a=1/2\) satisfies
\[
 \int_2^x\frac{\vartheta(t)-t}{t^{3/2}}\,dt<0
 \qquad (2<x\le 8\cdot10^{50}).
\]
Consequently, for every squarefree \(8\le n\le\exp(8\cdot10^{50})\),
\[
 \sum_{p\mid n}\frac{\log p}{\sqrt p}<2\sqrt{\log n}-\sqrt2.
\]
The improvement over the old real cutoff \(1.21\cdot10^{48}\) is for the critically weighted criterion. The earlier bound for the unweighted area continues to have its original range.

Write \(A(t)=\int_2^t(\vartheta(v)-v)dv\), \(t_0=10^{19}\), and \(H=3\cdot10^{12}\). Formula (3) of the [positive-average estimate](../step4-strip-2026-11-19/BANDLIMITED_THETA.md), before restricting to where its right side is negative, implies for **every** \(t\ge t_0\)
\[
 A(t)/t^{3/2}<-0.60+5.1\sqrt t/H^2 .
\]
Indeed the negative constant is at least \((2/3)0.98-0.04621(1.0016)-900/10^{28}>0.60\), and the positive slope is below \(1.0021(22/7)^2/2+0.04621(1.7\cdot10^{10}+2800)/10^{12}<5.1\). The true zero-height verification and complete prime-power correction in that estimate are essential. [Platt and Trudgian](https://doi.org/10.1112/blms.12460) · [Johnston, Lemmas 2.1–2.3 and integrated explicit formula](https://arxiv.org/html/2201.06184v2#S2)

Integration by parts now gives
\[
 I_{1/2}(x)=A(x)x^{-3/2}+\tfrac32\int_2^x A(t)t^{-5/2}dt .
\]
On \((2,t_0]\) the area is strictly negative. For \(t_0\le x\le X=8\cdot10^{50}\), discard the negative contribution of this initial integral and the negative lower-end square-root term after integration. This yields
\[
 I_{1/2}(x)< -0.60\big(1+\tfrac32\log(x/t_0)\big)
                  +20.4\sqrt{x}/H^2 .
\]
The last function is convex in \(\log(x/t_0)\), so its maximum on the interval is at an endpoint. At \(t_0\), \(20.4\sqrt{t_0}/H^2<0.01\). At \(X\), \(\sqrt X/H^2<3.15\), and \(\log(X/t_0)>\log(10^{31})>71.3\), since \(\log10>2.3\). Hence the last endpoint is below \(-0.60(1+1.5\times71.3)+20.4\times3.15<0\). This establishes continuous coverage. Substituting \(x=\log n\) in the true prime-factor maximum proves the integer statement with the stated strict sign. The argument does not supply an unbounded sequence of new admissible exponents or an upper for the unweighted area after its earlier cutoff.
